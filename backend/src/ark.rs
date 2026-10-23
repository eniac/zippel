//! The arkworks implementation of [`Field`], [`Group`] and [`Pairing`]: every arkworks
//! prime field, short Weierstrass and twisted Edwards curve, and pairing engine.

use crate::algebra::{Field, Group, Pairing};
use ark_ec::pairing::{MillerLoopOutput, PairingOutput};
use ark_ec::scalar_mul::ScalarMul;
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ec::{short_weierstrass as sw, twisted_edwards as te};
use ark_ff::{FftField, One, PrimeField, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_serialize::CanonicalSerialize;
use rand::Rng;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::marker::PhantomData;

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
    type G2Prepared = P::G2Prepared;

    fn prepare_g2(g: &P::G2Affine) -> P::G2Prepared {
        P::G2Prepared::from(g.into_group())
    }

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

    /// arkworks' Miller loop consumes its preparations, and stored ones can only be
    /// cloned, so the pairs go through it a chunk at a time: the clones never exceed one
    /// chunk, and one final exponentiation of the product of the chunks' Miller loops is
    /// exactly `multi_pairing`.
    fn multi_pairing_prepared(a: &[P::G1], b: &[P::G2Prepared]) -> PairingOutput<P> {
        const CHUNK: usize = 32;
        assert_eq!(
            a.len(),
            b.len(),
            "pairing {} G1 elements with {} G2 elements",
            a.len(),
            b.len()
        );
        let a = <P::G1 as CurveGroup>::normalize_batch(a);
        let f = a
            .par_chunks(CHUNK)
            .zip(b.par_chunks(CHUNK))
            .map(|(a, b)| P::multi_miller_loop(a.iter().copied(), b.iter().cloned()).0)
            .reduce(P::TargetField::one, |x, y| x * y);
        P::final_exponentiation(MillerLoopOutput(f)).expect("final exponentiation of a Miller loop")
    }
}
