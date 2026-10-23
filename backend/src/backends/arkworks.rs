//! The arkworks backends: every arkworks prime field, short Weierstrass and twisted
//! Edwards curve, and pairing engine as [`Field`], [`Group`] and [`Pairing`], the
//! pairing backends' G2 key, and the arkworks backends Zippel ships.

use super::{Backend, G2Points, GT, Key, Keyed, NoKey, plain_multi_pairing};
use crate::algebra::{Field, Group, Pairing};
use crate::backends::nothing::NoPairing;
use ark_ec::bls12::Bls12;
use ark_ec::mnt4::MNT4;
use ark_ec::models::bn::Bn;
use ark_ec::pairing::{MillerLoopOutput, PairingOutput};
use ark_ec::scalar_mul::ScalarMul;
use ark_ec::{CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ec::{short_weierstrass as sw, twisted_edwards as te};
use ark_ff::{FftField, One, PrimeField, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_serialize::CanonicalSerialize;
use rand::Rng;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Range;

/// Appends `x`'s compressed arkworks encoding.
fn write_compressed<T: CanonicalSerialize>(x: &T, out: &mut Vec<u8>) {
    x.serialize_compressed(out)
        .expect("serializing into a vector cannot fail");
}

/// The FFT domain of size `n`.
///
/// # Panics
/// Panics if the field has none.
fn domain<F: FftField>(n: usize) -> GeneralEvaluationDomain<F> {
    GeneralEvaluationDomain::new(n)
        .unwrap_or_else(|| panic!("the field has no FFT domain of size {n}"))
}

impl<F: PrimeField> Field for F {
    const MODULUS_BITS: u32 = F::MODULUS_BIT_SIZE;
    const TWO_ADICITY: u32 = <F as FftField>::TWO_ADICITY;

    fn zero() -> Self {
        <F as Zero>::zero()
    }

    fn one() -> Self {
        <F as One>::one()
    }

    fn is_zero(&self) -> bool {
        Zero::is_zero(self)
    }

    fn is_one(&self) -> bool {
        One::is_one(self)
    }

    fn inverse(&self) -> Option<Self> {
        ark_ff::Field::inverse(self)
    }

    fn pow(&self, e: u64) -> Self {
        ark_ff::Field::pow(self, [e])
    }

    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        UniformRand::rand(rng)
    }

    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self {
        PrimeField::from_le_bytes_mod_order(bytes)
    }

    fn write_bytes(&self, out: &mut Vec<u8>) {
        write_compressed(self, out);
    }

    fn cmp_canonical(&self, other: &Self) -> Ordering {
        self.into_bigint().cmp(&other.into_bigint())
    }

    fn two_adic_root(log_n: u32) -> Option<Self> {
        F::get_root_of_unity(1u64.checked_shl(log_n)?)
    }

    fn fft(a: &mut Vec<Self>) {
        domain::<Self>(a.len()).fft_in_place(a);
    }

    fn ifft(a: &mut Vec<Self>) {
        domain::<Self>(a.len()).ifft_in_place(a);
    }
}

/// [`Group`] for an arkworks curve group, by the arkworks operations.
macro_rules! curve_group {
    ($curve:ty, $config:ident: $bound:path) => {
        impl<$config: $bound> Group for $curve {
            type Scalar = <$curve as PrimeGroup>::ScalarField;
            type Affine = <$curve as CurveGroup>::Affine;

            fn zero() -> Self {
                <$curve as Zero>::zero()
            }

            fn generator() -> Self {
                <$curve as PrimeGroup>::generator()
            }

            fn is_zero(&self) -> bool {
                Zero::is_zero(self)
            }

            fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
                UniformRand::rand(rng)
            }

            fn add_affine(&mut self, a: &Self::Affine) {
                *self += a;
            }

            fn normalize(&self) -> Self::Affine {
                self.into_affine()
            }

            fn normalize_batch(v: &[Self]) -> Vec<Self::Affine> {
                <$curve as CurveGroup>::normalize_batch(v)
            }

            fn batch_mul(&self, scalars: &[Self::Scalar]) -> Vec<Self::Affine> {
                // `ScalarMul::batch_mul` builds a window table whose construction costs
                // ~85 inversions on BLS12-381 G1: amortized over many scalars, wasted on one.
                if let [s] = scalars {
                    vec![(*self * s).into_affine()]
                } else {
                    ScalarMul::batch_mul(*self, scalars)
                }
            }

            fn msm(bases: &[Self::Affine], scalars: &[Self::Scalar]) -> Self {
                <$curve as VariableBaseMSM>::msm(bases, scalars).unwrap_or_else(|_| {
                    panic!(
                        "an MSM of {} bases and {} scalars",
                        bases.len(),
                        scalars.len()
                    )
                })
            }

            fn write_bytes(&self, out: &mut Vec<u8>) {
                write_compressed(self, out);
            }

            fn write_affine_bytes(a: &Self::Affine, out: &mut Vec<u8>) {
                write_compressed(a, out);
            }
        }
    };
}

curve_group!(sw::Projective<P>, P: sw::SWCurveConfig);
curve_group!(te::Projective<P>, P: te::TECurveConfig);

impl<P: ark_ec::pairing::Pairing> Group for PairingOutput<P> {
    type Scalar = P::ScalarField;
    type Affine = Self;

    fn zero() -> Self {
        <Self as Zero>::zero()
    }

    fn generator() -> Self {
        <Self as PrimeGroup>::generator()
    }

    fn is_zero(&self) -> bool {
        Zero::is_zero(self)
    }

    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        UniformRand::rand(rng)
    }

    fn add_affine(&mut self, a: &Self) {
        *self += a;
    }

    fn normalize(&self) -> Self {
        *self
    }

    fn normalize_batch(v: &[Self]) -> Vec<Self> {
        v.to_vec()
    }

    fn batch_mul(&self, scalars: &[Self::Scalar]) -> Vec<Self> {
        if let [s] = scalars {
            vec![*self * s]
        } else {
            ScalarMul::batch_mul(*self, scalars)
        }
    }

    fn msm(bases: &[Self], scalars: &[Self::Scalar]) -> Self {
        <Self as VariableBaseMSM>::msm(bases, scalars).unwrap_or_else(|_| {
            panic!(
                "an MSM of {} bases and {} scalars",
                bases.len(),
                scalars.len()
            )
        })
    }

    fn write_bytes(&self, out: &mut Vec<u8>) {
        write_compressed(self, out);
    }

    fn write_affine_bytes(a: &Self, out: &mut Vec<u8>) {
        write_compressed(a, out);
    }
}

/// An arkworks pairing engine as a [`Pairing`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ArkPairing<P>(PhantomData<P>);

impl<P: ark_ec::pairing::Pairing> Pairing for ArkPairing<P>
where
    P::G1: Group<Scalar = P::ScalarField, Affine = P::G1Affine>,
    P::G2: Group<Scalar = P::ScalarField, Affine = P::G2Affine>,
{
    type G1 = P::G1;
    type G2 = P::G2;
    type GT = PairingOutput<P>;

    fn pairing(a: &P::G1, b: &P::G2) -> PairingOutput<P> {
        P::pairing(*a, *b)
    }

    /// One Miller loop and one final exponentiation for all pairs. The inputs are
    /// normalized and prepared in parallel first: arkworks prepares each pair serially
    /// before its parallel loop, and G2 preparation dominates for long vectors.
    fn multi_pairing(a: &[P::G1], b: &[P::G2]) -> PairingOutput<P> {
        let a: Vec<P::G1Prepared> = <P::G1 as CurveGroup>::normalize_batch(a)
            .into_par_iter()
            .map(P::G1Prepared::from)
            .collect();
        let b: Vec<P::G2Prepared> = <P::G2 as CurveGroup>::normalize_batch(b)
            .into_par_iter()
            .map(P::G2Prepared::from)
            .collect();
        P::multi_pairing(a, b)
    }
}

/// The key a pairing backend keeps for second-source-group points (a verifier key):
/// each point prepared for arkworks' Miller loop. A concatenation keeps its points'
/// preparations.
pub struct ArkPairingKey<P: ark_ec::pairing::Pairing>(Vec<P::G2Prepared>);

impl<P: ark_ec::pairing::Pairing> ArkPairingKey<P> {
    /// The preparations of the points at `view` (`None` for all of them).
    fn at(&self, view: Option<Range<usize>>) -> &[P::G2Prepared] {
        &self.0[view.unwrap_or(0..self.0.len())]
    }
}

impl<P: ark_ec::pairing::Pairing> Key<P::G2Affine> for ArkPairingKey<P> {
    fn prepare(points: &[P::G2Affine]) -> Option<Self> {
        Some(ArkPairingKey(
            points.par_iter().map(|&p| P::G2Prepared::from(p)).collect(),
        ))
    }

    fn concat(
        &self,
        view: Option<Range<usize>>,
        other: &Self,
        other_view: Option<Range<usize>>,
    ) -> Option<Self> {
        Some(ArkPairingKey(
            self.at(view)
                .iter()
                .chain(other.at(other_view))
                .cloned()
                .collect(),
        ))
    }
}

/// `Σ e(g1[i], g2[i])` over a key's prepared G2 points: the pairing backends'
/// [`Backend::multi_pairing`] when the G2 operand has a key.
///
/// arkworks' Miller loop consumes its preparations, and stored ones can only be cloned,
/// so the pairs go through it a chunk at a time: the clones never exceed one chunk, and
/// one final exponentiation of the product of the chunks' Miller loops is exactly
/// `multi_pairing`.
///
/// # Panics
/// Panics if `g1` and the viewed points have different lengths.
pub fn keyed_multi_pairing<P: ark_ec::pairing::Pairing>(
    g1: &[P::G1],
    key: Keyed<'_, ArkPairingKey<P>>,
) -> PairingOutput<P> {
    const CHUNK: usize = 32;
    let b = key.key.at(key.view);
    assert_eq!(
        g1.len(),
        b.len(),
        "pairing {} G1 elements with {} G2 elements",
        g1.len(),
        b.len()
    );
    let a = <P::G1 as CurveGroup>::normalize_batch(g1);
    let f = a
        .par_chunks(CHUNK)
        .zip(b.par_chunks(CHUNK))
        .map(|(a, b)| P::multi_miller_loop(a.iter().copied(), b.iter().cloned()).0)
        .reduce(P::TargetField::one, |x, y| x * y);
    P::final_exponentiation(MillerLoopOutput(f)).expect("final exponentiation of a Miller loop")
}

/// [`Backend::multi_pairing`] for an arkworks pairing backend whose `G2Key` is an [`ArkPairingKey`]:
/// by the G2 operand's prepared points when it has a key.
macro_rules! keyed_pairing_backend {
    () => {
        fn multi_pairing(g1: &[Self::G1], g2: &G2Points<Self>) -> GT<Self> {
            match g2.key() {
                Some(key) => keyed_multi_pairing(g1, key),
                None => plain_multi_pairing::<Self>(g1, g2),
            }
        }
    };
}

/// The BLS12-381 pairing-friendly backend.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkBls12_381 {}

/// `BN254` pairing-friendly backend, the curve used by most Ethereum tooling.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkBn254 {}

/// `MNT4-298` pairing-friendly backend, a cycle-friendly curve for recursion.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkMNT4_298 {}

/// Curve25519 backend; a prime-order Edwards group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkCurve25519 {}

/// `secp256k1` backend; a prime-order Weierstrass group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkSecp256k1 {}

/// Pallas backend, the first half of the Pasta cycle; no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkPallas {}

/// Vesta backend, the second half of the Pasta cycle; no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkVesta {}

/// Ed25519 backend; a prime-order Edwards group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkEd25519 {}

impl Backend for ArkBls12_381 {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = ArkPairingKey<Bls12<ark_bls12_381::Config>>;
    type F = ark_bls12_381::Fr;
    type G1 = ark_bls12_381::G1Projective;
    type G2 = ark_bls12_381::G2Projective;
    type P = ArkPairing<Bls12<ark_bls12_381::Config>>;
    const HAS_PAIRING: bool = true;
    keyed_pairing_backend!();
}

impl Backend for ArkBn254 {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = ArkPairingKey<Bn<ark_bn254::Config>>;
    type F = ark_bn254::Fr;
    type G1 = ark_bn254::G1Projective;
    type G2 = ark_bn254::G2Projective;
    type P = ArkPairing<Bn<ark_bn254::Config>>;
    const HAS_PAIRING: bool = true;
    keyed_pairing_backend!();
}

impl Backend for ArkMNT4_298 {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = ArkPairingKey<MNT4<ark_mnt4_298::Config>>;
    type F = ark_mnt4_298::Fr;
    type G1 = ark_mnt4_298::G1Projective;
    type G2 = ark_mnt4_298::G2Projective;
    type P = ArkPairing<MNT4<ark_mnt4_298::Config>>;
    const HAS_PAIRING: bool = true;
    keyed_pairing_backend!();
}

impl Backend for ArkCurve25519 {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = NoKey;
    type F = ark_curve25519::Fr;
    type G1 = ark_curve25519::EdwardsProjective;
    type G2 = ark_curve25519::EdwardsProjective;
    type P = NoPairing<ark_curve25519::EdwardsProjective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkSecp256k1 {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = NoKey;
    type F = ark_secp256k1::Fr;
    type G1 = ark_secp256k1::Projective;
    type G2 = ark_secp256k1::Projective;
    type P = NoPairing<ark_secp256k1::Projective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkPallas {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = NoKey;
    type F = ark_pallas::Fr;
    type G1 = ark_pallas::Projective;
    type G2 = ark_pallas::Projective;
    type P = NoPairing<ark_pallas::Projective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkVesta {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = NoKey;
    type F = ark_vesta::Fr;
    type G1 = ark_vesta::Projective;
    type G2 = ark_vesta::Projective;
    type P = NoPairing<ark_vesta::Projective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkEd25519 {
    type Analysis = Self;
    type G1Key = NoKey;
    type G2Key = NoKey;
    type F = ark_ed25519::Fr;
    type G1 = ark_ed25519::EdwardsProjective;
    type G2 = ark_ed25519::EdwardsProjective;
    type P = NoPairing<ark_ed25519::EdwardsProjective>;
    const HAS_PAIRING: bool = false;
}

impl fmt::Display for ArkBls12_381 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BLS12-381")
    }
}

impl fmt::Display for ArkBn254 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BN254")
    }
}

impl fmt::Display for ArkMNT4_298 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "MNT4-298")
    }
}

impl fmt::Display for ArkCurve25519 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Curve25519")
    }
}

impl fmt::Display for ArkSecp256k1 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SECP256K1")
    }
}

impl fmt::Display for ArkPallas {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Pallas")
    }
}

impl fmt::Display for ArkVesta {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Vesta")
    }
}

impl fmt::Display for ArkEd25519 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ed25519")
    }
}
