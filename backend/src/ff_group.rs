//! [`Field`] and [`Group`] for the zkcrypto `ff`/`group` (0.14) ecosystem: [`FfScalar`]
//! and [`FfPoint`] wrap any `ff::PrimeField` and prime-order `group::Group` (the orphan
//! rule rules out implementing Zippel's traits on the foreign types directly), and
//! [`DalekRistretto`] and [`PastaPallas`] are the backends built from them.
//!
//! A group has a single form here (`Affine = Self`): `group::Group` has no affine type in
//! general (Ristretto has none). Its MSM is the [`Msm`] marker `M` of `FfPoint<G, M>`:
//! the generic [`Pippenger`] by default, or a curve's own (dalek's, [`DalekMsm`]). A
//! crate plugging in another curve can implement `Msm<TheirCurve>` on a marker of its
//! own.

use crate::algebra::{Field, Group};
use crate::config::Backend;
use crate::nothing::NoPairing;
use num_bigint::BigUint;
use rand::Rng;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// An element of the `ff` prime field `S`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FfScalar<S>(pub S);

/// An element of the `group` prime-order group `G`, whose MSM is `M`'s.
pub struct FfPoint<G, M = Pippenger>(pub G, PhantomData<fn() -> M>);

impl<G, M> FfPoint<G, M> {
    /// `g` as an element.
    pub const fn new(g: G) -> Self {
        FfPoint(g, PhantomData)
    }
}

// By hand: derives would require the marker `M` to implement each trait too.
impl<G: Clone, M> Clone for FfPoint<G, M> {
    fn clone(&self) -> Self {
        Self::new(self.0.clone())
    }
}

impl<G: Copy, M> Copy for FfPoint<G, M> {}

impl<G: PartialEq, M> PartialEq for FfPoint<G, M> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<G: Eq, M> Eq for FfPoint<G, M> {}

impl<G: fmt::Debug, M> fmt::Debug for FfPoint<G, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A multi-scalar multiplication for the group `G`: `Σ scalars[i] * bases[i]`.
pub trait Msm<G: group::Group>: 'static {
    /// `Σ scalars[i] * bases[i]`; the two have equal lengths.
    fn msm(bases: &[G], scalars: &[G::Scalar]) -> G;
}

/// The generic MSM, [`pippenger`], for any group.
pub struct Pippenger;

impl<G: group::Group> Msm<G> for Pippenger {
    fn msm(bases: &[G], scalars: &[G::Scalar]) -> G {
        pippenger(bases, scalars)
    }
}

/// curve25519-dalek's variable-time Ristretto MSM.
pub struct DalekMsm;

impl Msm<curve25519_dalek::RistrettoPoint> for DalekMsm {
    fn msm(
        bases: &[curve25519_dalek::RistrettoPoint],
        scalars: &[curve25519_dalek::Scalar],
    ) -> curve25519_dalek::RistrettoPoint {
        use curve25519_dalek::traits::VartimeMultiscalarMul;
        curve25519_dalek::RistrettoPoint::vartime_multiscalar_mul(scalars, bases)
    }
}

/// Pippenger's bucket method over any group: windows of `c` bits of each scalar's
/// little-endian representation, the windows in parallel.
pub fn pippenger<G: group::Group>(bases: &[G], scalars: &[G::Scalar]) -> G {
    use ff::PrimeField;
    let reprs: Vec<_> = scalars.par_iter().map(PrimeField::to_repr).collect();
    let bits = G::Scalar::NUM_BITS as usize;
    let c = match bases.len() {
        0..32 => 3,
        n => (n.ilog2() as usize * 69 / 100 + 2).min(16),
    };
    let bit = |repr: &[u8], i: usize| (repr[i / 8] >> (i % 8)) & 1;
    let windows: Vec<G> = (0..bits.div_ceil(c))
        .into_par_iter()
        .map(|w| {
            let mut buckets = vec![G::identity(); (1 << c) - 1];
            for (base, repr) in bases.iter().zip(&reprs) {
                let repr = repr.as_ref();
                let digit = (0..c)
                    .filter(|j| w * c + j < bits)
                    .fold(0usize, |d, j| d | usize::from(bit(repr, w * c + j)) << j);
                if digit != 0 {
                    buckets[digit - 1] += base;
                }
            }
            // Σ (i + 1) * buckets[i], by running sums from the top.
            let (mut running, mut sum) = (G::identity(), G::identity());
            for b in buckets.iter().rev() {
                running += b;
                sum += running;
            }
            sum
        })
        .collect();
    windows.iter().rev().fold(G::identity(), |acc, w| {
        (0..c).fold(acc, |a, _| a.double()) + w
    })
}

/// Field operators on [`FfScalar`] and group operators on [`FfPoint`], by the wrapped
/// type's.
macro_rules! delegate_ops {
    ($ty:ident<$($p:ident: $bound:path),+>, $rhs:ty, $rhs_get:expr, $wrap:expr) => {
        impl<$($p: $bound),+> Add for $ty<$($p),+> {
            type Output = Self;
            fn add(self, o: Self) -> Self {
                $wrap(self.0 + o.0)
            }
        }
        impl<'a, $($p: $bound),+> Add<&'a Self> for $ty<$($p),+> {
            type Output = Self;
            fn add(self, o: &'a Self) -> Self {
                $wrap(self.0 + o.0)
            }
        }
        impl<$($p: $bound),+> Sub for $ty<$($p),+> {
            type Output = Self;
            fn sub(self, o: Self) -> Self {
                $wrap(self.0 - o.0)
            }
        }
        impl<'a, $($p: $bound),+> Sub<&'a Self> for $ty<$($p),+> {
            type Output = Self;
            fn sub(self, o: &'a Self) -> Self {
                $wrap(self.0 - o.0)
            }
        }
        impl<$($p: $bound),+> Neg for $ty<$($p),+> {
            type Output = Self;
            fn neg(self) -> Self {
                $wrap(-self.0)
            }
        }
        impl<$($p: $bound),+> AddAssign for $ty<$($p),+> {
            fn add_assign(&mut self, o: Self) {
                self.0 += o.0;
            }
        }
        impl<'a, $($p: $bound),+> AddAssign<&'a Self> for $ty<$($p),+> {
            fn add_assign(&mut self, o: &'a Self) {
                self.0 += o.0;
            }
        }
        impl<$($p: $bound),+> SubAssign for $ty<$($p),+> {
            fn sub_assign(&mut self, o: Self) {
                self.0 -= o.0;
            }
        }
        impl<'a, $($p: $bound),+> SubAssign<&'a Self> for $ty<$($p),+> {
            fn sub_assign(&mut self, o: &'a Self) {
                self.0 -= o.0;
            }
        }
        impl<$($p: $bound),+> Mul<$rhs> for $ty<$($p),+> {
            type Output = Self;
            fn mul(self, o: $rhs) -> Self {
                $wrap(self.0 * $rhs_get(o))
            }
        }
        impl<$($p: $bound),+> MulAssign<$rhs> for $ty<$($p),+> {
            fn mul_assign(&mut self, o: $rhs) {
                self.0 *= $rhs_get(o);
            }
        }
        impl<$($p: $bound),+> Sum for $ty<$($p),+> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                $wrap(iter.map(|x| x.0).sum())
            }
        }
        impl<'a, $($p: $bound),+> Sum<&'a Self> for $ty<$($p),+> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                $wrap(iter.map(|x| x.0).sum())
            }
        }
    };
}

delegate_ops!(FfScalar<S: ff::PrimeField>, Self, |o: Self| o.0, FfScalar);
delegate_ops!(
    FfPoint<G: group::Group, M: Msm<G>>,
    FfScalar<G::Scalar>,
    |o: FfScalar<G::Scalar>| o.0,
    FfPoint::new
);

impl<'a, S: ff::PrimeField> Mul<&'a Self> for FfScalar<S> {
    type Output = Self;
    fn mul(self, o: &'a Self) -> Self {
        FfScalar(self.0 * o.0)
    }
}

impl<'a, S: ff::PrimeField> MulAssign<&'a Self> for FfScalar<S> {
    fn mul_assign(&mut self, o: &'a Self) {
        self.0 *= o.0;
    }
}

impl<S: ff::PrimeField> Product for FfScalar<S> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        FfScalar(iter.map(|x| x.0).product())
    }
}

impl<'a, S: ff::PrimeField> Product<&'a Self> for FfScalar<S> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        FfScalar(iter.map(|x| x.0).product())
    }
}

impl<S: ff::PrimeField> From<u64> for FfScalar<S> {
    fn from(x: u64) -> Self {
        FfScalar(S::from(x))
    }
}

impl<S: ff::PrimeField> Hash for FfScalar<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_repr().as_ref().hash(state);
    }
}

/// The canonical integer, in decimal, as arkworks prints field elements. Assumes a
/// little-endian representation, as `curve25519-dalek` and `pasta_curves` use.
impl<S: ff::PrimeField> fmt::Display for FfScalar<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", BigUint::from_bytes_le(self.0.to_repr().as_ref()))
    }
}

impl<S: ff::PrimeField> Field for FfScalar<S> {
    const MODULUS_BITS: u32 = S::NUM_BITS;
    const TWO_ADICITY: u32 = S::S;

    fn zero() -> Self {
        FfScalar(S::ZERO)
    }

    fn one() -> Self {
        FfScalar(S::ONE)
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero_vartime()
    }

    fn inverse(&self) -> Option<Self> {
        Option::from(self.0.invert()).map(FfScalar)
    }

    fn pow(&self, e: u64) -> Self {
        FfScalar(self.0.pow_vartime([e]))
    }

    /// 64 random bytes reduced modulo the prime: within `2^-256` of uniform for a field
    /// of at most 256 bits. (`ff`'s own sampler takes a rand_core 0.10 generator, and
    /// Zippel's is rand 0.8's.)
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        let mut bytes = [0u8; 64];
        rng.fill_bytes(&mut bytes);
        Self::from_le_bytes_mod_order(&bytes)
    }

    /// Horner's rule over the bytes, most significant first.
    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        let radix = S::from(256);
        FfScalar(
            bytes
                .iter()
                .rev()
                .fold(S::ZERO, |acc, &b| acc * radix + S::from(u64::from(b))),
        )
    }

    fn write_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.0.to_repr().as_ref());
    }

    /// By the representation's bytes: a total order consistent with equality, as
    /// [`Field::cmp_canonical`] needs, whatever the representation's byte order.
    fn cmp_canonical(&self, other: &Self) -> Ordering {
        self.0.to_repr().as_ref().cmp(other.0.to_repr().as_ref())
    }

    /// `ROOT_OF_UNITY`, a primitive `2^S`-th root, squared `S - log_n` times.
    fn two_adic_root(log_n: u32) -> Option<Self> {
        let squarings = S::S.checked_sub(log_n)?;
        Some(FfScalar(
            (0..squarings).fold(S::ROOT_OF_UNITY, |r, _| r.square()),
        ))
    }
}

impl<G: group::Group + group::GroupEncoding, M> Hash for FfPoint<G, M> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bytes().as_ref().hash(state);
    }
}

/// The compressed encoding, in hexadecimal.
impl<G: group::Group + group::GroupEncoding, M> fmt::Display for FfPoint<G, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0
            .to_bytes()
            .as_ref()
            .iter()
            .try_for_each(|b| write!(f, "{b:02x}"))
    }
}

impl<G: group::Group + group::GroupEncoding, M: Msm<G>> Group for FfPoint<G, M> {
    type Scalar = FfScalar<G::Scalar>;
    type Affine = Self;

    fn zero() -> Self {
        FfPoint::new(G::identity())
    }

    fn generator() -> Self {
        FfPoint::new(G::generator())
    }

    fn is_zero(&self) -> bool {
        bool::from(self.0.is_identity())
    }

    /// The generator times a random scalar: uniform, the group having prime order.
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        FfPoint::new(G::generator() * FfScalar::<G::Scalar>::rand(rng).0)
    }

    fn add_affine(&mut self, a: &Self) {
        self.0 += a.0;
    }

    fn normalize(&self) -> Self {
        *self
    }

    fn normalize_batch(v: &[Self]) -> Vec<Self> {
        v.to_vec()
    }

    fn batch_mul(&self, scalars: &[Self::Scalar]) -> Vec<Self> {
        scalars
            .par_iter()
            .map(|s| FfPoint::new(self.0 * s.0))
            .collect()
    }

    fn msm(bases: &[Self], scalars: &[Self::Scalar]) -> Self {
        assert_eq!(
            bases.len(),
            scalars.len(),
            "an MSM of {} bases and {} scalars",
            bases.len(),
            scalars.len()
        );
        let bases: Vec<G> = bases.iter().map(|b| b.0).collect();
        let scalars: Vec<G::Scalar> = scalars.iter().map(|s| s.0).collect();
        FfPoint::new(M::msm(&bases, &scalars))
    }

    fn write_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.0.to_bytes().as_ref());
    }

    fn write_affine_bytes(a: &Self, out: &mut Vec<u8>) {
        a.write_bytes(out);
    }
}

/// Ristretto255 from `curve25519-dalek`: the group libspartan uses, without a pairing,
/// and with a scalar field of 2-adicity 2 (FFTs up to 4 points). Analyze its protocols on
/// [`ArkCurve25519`](crate::ArkCurve25519), which has the same scalar field.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct DalekRistretto {}

/// Pallas from `pasta_curves`, without a pairing. Analyze its protocols on
/// [`ArkPallas`](crate::ArkPallas), which has the same scalar field.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct PastaPallas {}

impl fmt::Display for DalekRistretto {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ristretto255 (curve25519-dalek)")
    }
}

impl fmt::Display for PastaPallas {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Pallas (pasta_curves)")
    }
}

impl Backend for DalekRistretto {
    type F = FfScalar<curve25519_dalek::Scalar>;
    type G1 = FfPoint<curve25519_dalek::RistrettoPoint, DalekMsm>;
    type G2 = Self::G1;
    type P = NoPairing<Self::G1>;
    const HAS_PAIRING: bool = false;
}

impl Backend for PastaPallas {
    type F = FfScalar<pasta_curves::pallas::Scalar>;
    type G1 = FfPoint<pasta_curves::pallas::Point>;
    type G2 = Self::G1;
    type P = NoPairing<Self::G1>;
    const HAS_PAIRING: bool = false;
}
