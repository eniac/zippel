//! The hybrid backend: curve25519-dalek's Ristretto group over arkworks' Curve25519
//! scalar field, so polynomial arithmetic stays in arkworks and only group operations
//! use dalek; and its key, dalek's MSM tables.

use super::{Backend, G1Points, Key, Keyed, NoKey};
use crate::algebra::Group;
use crate::backends::nothing::NoPairing;
use ark_ff::{PrimeField, UniformRand};
use curve25519_dalek::RistrettoPoint;
use curve25519_dalek::ristretto::VartimeRistrettoPrecomputation;
use curve25519_dalek::traits::{Identity, VartimeMultiscalarMul, VartimePrecomputedMultiscalarMul};
use rand::Rng;
use rayon::prelude::*;
use std::fmt;

/// A Ristretto255 point from curve25519-dalek, with arkworks' `ark_curve25519::Fr` (the
/// same prime field as dalek's scalars) as its scalars: polynomial arithmetic stays in
/// arkworks, and only group operations convert a scalar to dalek's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArkFrRistrettoPoint(RistrettoPoint);

impl ArkFrRistrettoPoint {
    /// `p` as an element.
    pub const fn new(p: RistrettoPoint) -> Self {
        Self(p)
    }
}

/// `value` as dalek's scalar, by its canonical little-endian bytes.
fn dalek_scalar(value: ark_curve25519::Fr) -> curve25519_dalek::Scalar {
    let mut bytes = [0u8; 32];
    for (chunk, limb) in bytes
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(value.into_bigint().0)
    {
        *chunk = limb.to_le_bytes();
    }
    Option::from(curve25519_dalek::Scalar::from_canonical_bytes(bytes))
        .expect("the two scalar fields have the same modulus")
}

impl std::ops::Add for ArkFrRistrettoPoint {
    type Output = Self;
    fn add(self, o: Self) -> Self {
        Self(self.0 + o.0)
    }
}

impl std::ops::Sub for ArkFrRistrettoPoint {
    type Output = Self;
    fn sub(self, o: Self) -> Self {
        Self(self.0 - o.0)
    }
}

impl std::ops::Neg for ArkFrRistrettoPoint {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl std::ops::AddAssign for ArkFrRistrettoPoint {
    fn add_assign(&mut self, o: Self) {
        self.0 += o.0;
    }
}

impl std::ops::SubAssign for ArkFrRistrettoPoint {
    fn sub_assign(&mut self, o: Self) {
        self.0 -= o.0;
    }
}

impl std::ops::Mul<ark_curve25519::Fr> for ArkFrRistrettoPoint {
    type Output = Self;
    fn mul(self, s: ark_curve25519::Fr) -> Self {
        Self(self.0 * dalek_scalar(s))
    }
}

impl std::ops::MulAssign<ark_curve25519::Fr> for ArkFrRistrettoPoint {
    fn mul_assign(&mut self, s: ark_curve25519::Fr) {
        self.0 *= dalek_scalar(s);
    }
}

impl std::hash::Hash for ArkFrRistrettoPoint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.compress().as_bytes().hash(state);
    }
}

/// The compressed encoding, in hexadecimal.
impl std::fmt::Display for ArkFrRistrettoPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0
            .compress()
            .as_bytes()
            .iter()
            .try_for_each(|b| write!(f, "{b:02x}"))
    }
}

impl Group for ArkFrRistrettoPoint {
    type Scalar = ark_curve25519::Fr;
    type Affine = Self;

    fn zero() -> Self {
        Self(RistrettoPoint::identity())
    }

    fn generator() -> Self {
        Self(curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT)
    }

    fn is_zero(&self) -> bool {
        self.0 == RistrettoPoint::identity()
    }

    /// The generator times a random scalar: uniform, the group having prime order.
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self::generator() * <ark_curve25519::Fr as UniformRand>::rand(rng)
    }

    fn add_affine(&mut self, a: &Self) {
        *self += *a;
    }

    fn normalize(&self) -> Self {
        *self
    }

    fn normalize_batch(v: &[Self]) -> Vec<Self> {
        v.to_vec()
    }

    fn batch_mul(&self, scalars: &[Self::Scalar]) -> Vec<Self> {
        scalars.par_iter().map(|&s| *self * s).collect()
    }

    fn msm(bases: &[Self], scalars: &[Self::Scalar]) -> Self {
        assert_eq!(
            bases.len(),
            scalars.len(),
            "an MSM of {} bases and {} scalars",
            bases.len(),
            scalars.len()
        );
        Self(RistrettoPoint::vartime_multiscalar_mul(
            scalars.iter().map(|&s| dalek_scalar(s)),
            bases.iter().map(|b| b.0),
        ))
    }

    fn write_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.0.compress().as_bytes());
    }

    fn write_affine_bytes(a: &Self, out: &mut Vec<u8>) {
        a.write_bytes(out);
    }
}

/// The hybrid backend's key for first-source-group points: dalek's per-point lookup
/// tables (64 points each) for MSMs over the whole vector. Measured faster than dalek's
/// Pippenger only up to [`MSM_KEY_MAX_POINTS`] points on the reference host: about 16%
/// at 512, none at 1024, slower above as the tables leave the cache.
pub struct RistrettoMsmKey {
    tables: VartimeRistrettoPrecomputation,
    len: usize,
}

/// The most points a [`RistrettoMsmKey`] is kept for.
const MSM_KEY_MAX_POINTS: usize = 512;

impl Key<ArkFrRistrettoPoint> for RistrettoMsmKey {
    fn prepare(points: &[ArkFrRistrettoPoint]) -> Option<Self> {
        (points.len() <= MSM_KEY_MAX_POINTS).then(|| RistrettoMsmKey {
            tables: VartimeRistrettoPrecomputation::new(points.iter().map(|p| p.0)),
            len: points.len(),
        })
    }
}

impl RistrettoMsmKey {
    /// `Σ scalars[i]·points[i]` over every point the tables were built for.
    ///
    /// # Panics
    /// Panics if `scalars` has a different length than the points.
    fn msm(&self, scalars: &[ark_curve25519::Fr]) -> ArkFrRistrettoPoint {
        assert_eq!(
            self.len,
            scalars.len(),
            "an MSM of {} bases and {} scalars",
            self.len,
            scalars.len()
        );
        ArkFrRistrettoPoint(
            self.tables
                .vartime_multiscalar_mul(scalars.iter().map(|&s| dalek_scalar(s))),
        )
    }
}

/// Ristretto255 from curve25519-dalek with arkworks' Curve25519 scalar field: the group
/// libspartan uses, with [`ArkCurve25519`]'s field arithmetic. No pairing.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkFrRistretto {}

impl fmt::Display for ArkFrRistretto {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ristretto255 (curve25519-dalek, arkworks scalars)")
    }
}

impl Backend for ArkFrRistretto {
    type Analysis = Self;
    type G1Key = RistrettoMsmKey;
    type G2Key = NoKey;
    type F = ark_curve25519::Fr;
    type G1 = ArkFrRistrettoPoint;
    type G2 = ArkFrRistrettoPoint;
    type P = NoPairing<ArkFrRistrettoPoint>;
    const HAS_PAIRING: bool = false;

    /// By the key's tables when the operand is the whole vector they describe.
    fn msm_g1(points: &G1Points<Self>, scalars: &[ark_curve25519::Fr]) -> ArkFrRistrettoPoint {
        match points.key() {
            Some(Keyed { key, view: None }) => key.msm(scalars),
            _ => ArkFrRistrettoPoint::msm(points, scalars),
        }
    }
}
