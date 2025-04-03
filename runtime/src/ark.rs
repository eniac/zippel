use rand::Rng;
use std::hash::Hash;
use std::fmt;
use std::marker::PhantomData;
use core::hash::Hasher;
use rayon::prelude::*;

use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
use ark_ff::{Zero, FftField, PrimeField};
use ark_ec::scalar_mul::ScalarMul;
use ark_ec::VariableBaseMSM;
use ark_ec::pairing::{MillerLoopOutput, Pairing, PairingOutput};
use ark_ec::bls12::Bls12;
use ark_ec::models::bn::Bn;
use ark_ec::mnt4::MNT4;
use ark_ec::{CurveGroup, PrimeGroup};

use crate::Nothing;

/// API to Arkworks finite fields, elliptic curves, and pairings
pub trait ArkConfig {
    type F: FftField;
    type G1: CurveGroup<ScalarField = Self::F>;
    type G2: ArkGroup<ScalarField = Self::F>;
    type GT: PrimeGroup<ScalarField = Self::F> + ScalarMul + VariableBaseMSM;
    type P: Pairing<ScalarField = Self::F, G1 = Self::G1, G2 = Self::G2>;

    type FOps : ArkScalarOps<Self::F>;
    type G1Ops : ArkGroupOps<Self::G1>;
    type G2Ops : ArkGroupOps<Self::G2>;
    type GTOps : ArkGroupOps<Self::GT>;
    type POps : ArkPairingOps<Self::P>;
}

/// Operations on Arkworks scalar fields
pub trait ArkScalarOps<F: FftField> {
    /// Field constants
    #[inline]
    fn scalar_zero() -> F {
        F::zero()
    }

    #[inline]
    fn scalar_one() -> F {
        F::one()
    }

    /// Scalar addition, saves result in f2
    #[inline]
    fn scalar_add(f1: &F, f2: &mut F) {
        *f2 += f1
    }

    /// Scalar negation in place
    #[inline]
    fn scalar_neg(f: &mut F) {
        f.neg_in_place();
    }

    /// Scalar subtraction, saves result in f2
    #[inline]
    fn scalar_sub(f1: &F, f2: &mut F) {
        Self::scalar_neg(f2);
        Self::scalar_add(f1, f2);
    }

    /// Scalar multiplication, saves result in f2
    #[inline]
    fn scalar_mul(f1: &F, f2: &mut F) {
        *f2 *= f1
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn scalar_inv(f: &mut F) {
        f.inverse_in_place();
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn scalar_div(f1: &F, f2: &mut F) {
        Self::scalar_inv(f2);
        Self::scalar_mul(f1, f2);
    }

    /// Scalar exponentiation, saves result in f1
    #[inline]
    fn scalar_pow(f1: &mut F, i: u64) {
        let mut i = i;
        while (i % 2) == 0 {
            f1.square_in_place();
            i /= 2;
        }
        *f1 = f1.pow(&[i as u64])
    }

    #[inline]
    fn scalar_vec_add(f1: &Vec<F>, f2: &mut Vec<F>) {
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a += b);
    }

    #[inline]
    fn scalar_vec_neg(f: &mut Vec<F>) {
        f.par_iter_mut().for_each(|x| { x.neg_in_place(); });
    }

    #[inline]
    fn scalar_vec_sub(f1: &Vec<F>, f2: &mut Vec<F>) {
        Self::scalar_vec_neg(f2);
        Self::scalar_vec_add(f1, f2);
    }

    #[inline]
    fn scalar_vec_mul(f1: &Vec<F>, f2: &mut Vec<F>) {
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a *= b);
    }

    #[inline]
    fn scalar_vec_dot(f1: &Vec<F>, f2: &Vec<F>) -> F {
        f1.par_iter()
            .zip(f2.par_iter())
            .map(|(a, b)| *a * *b)
            .reduce(|| Self::scalar_zero(), |acc, x| acc + x)
    }

    /// Vector batch inversion, saves result in f2
    #[inline]
    fn scalar_vec_inv(f: &mut Vec<F>) {
        ark_ff::fields::batch_inversion::<F>(f);
    }

    /// Vector division by batch inversion, saves result in f2
    #[inline]
    fn scalar_vec_div(f1: &Vec<F>, f2: &mut Vec<F>) {
        Self::scalar_vec_inv(f2);
        ark_ff::fields::batch_inversion::<F>(f2);
        f2.par_iter_mut()
        .zip(f1.par_iter())
        .for_each(|(a, b)| *a *= b);
    }

    #[inline]
    fn scalar_vec_pow(f1: &mut Vec<F>, i: u64) {
        f1.par_iter_mut()
            .for_each(|x| {
                let mut i = i;
                while (i % 2) == 0 {
                    x.square_in_place();
                    i /= 2;
                }
                *x = x.pow(&[i as u64]);
            });
    }

    /// FFT and IFFT
    #[inline]
    fn scalar_vec_ifft(a: &mut Vec<F>) {
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        domain.ifft_in_place(a);
    }

    #[inline]
    fn scalar_vec_fft(a: &mut Vec<F>) {
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        domain.fft_in_place(a);
    }

    /// Random and hashing
    #[inline]
    fn scalar_rand<R: Rng + ?Sized>(rng: &mut R) -> F {
        F::rand(rng)
    }

    #[inline]
    fn scalar_hash<H: Hasher>(f: F, h: &mut H) {
        f.hash(h)
    }

    #[inline]
    fn scalar_vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<F> {
        let mut v = vec![Self::scalar_zero(); n];
        v.iter_mut()
            .for_each(|x| *x = Self::scalar_rand(rng));
        v
    }

    #[inline]
    fn scalar_vec_hash<H: Hasher>(f: Vec<F>, h: &mut H) {
        f.hash(h)
    }
}

/// Minimum API to implement both G1, G2, GT
pub trait ArkGroup = PrimeGroup + ScalarMul + VariableBaseMSM;

pub trait ArkGroupOps<G: ArkGroup> {
    /// Group constants
    #[inline]
    fn zero() -> G {
        G::ZERO
    }
    #[inline]
    fn generator() -> G {
        G::generator()
    }
    /// Group operations
    #[inline]
    fn add(g1: &G, g2: &mut G) {
        *g2 += g1;
    }
    #[inline]
    fn neg(g: &mut G) {
        g.neg_in_place();
    }
    #[inline]
    fn sub(g1: &G, g2: &mut G) {
        Self::neg(g2);
        Self::add(g1, g2);
    }
    #[inline]
    fn mul(f: &G::Scalar, g: &mut G) {
        *g *= f;
    }
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> G {
        G::rand(rng)
    }
    #[inline]
    fn hash<H: Hasher>(g: &G, h: &mut H) {
        g.hash(h)
    }
    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<G> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut()
            .for_each(|x| *x = Self::rand(rng));
        v
    }
    #[inline]
    fn vec_hash<H: Hasher>(g: Vec<G>, h: &mut H) {
        g.hash(h)
    }
    /// Group vec operations
    #[inline]
    fn vec_mul(g: &G, f: &Vec<G::Scalar>) -> Vec<G::MulBase> {
        g.batch_mul(&f[..])
    }
    #[inline]
    fn vec_dot(g: &Vec<G::MulBase>, f: &Vec<G::Scalar>) -> G {
        // TODO: What does Err<usize> mean here?
        G::msm(&g[..], &f[..]).unwrap()
    }
    #[inline]
    fn fmt(g: &G, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
}

pub trait ArkPairingOps<P: Pairing> {
    /// Pairing operations
    #[inline]
    fn billinear_map(g1: &P::G1, g2: &P::G2) -> PairingOutput<P> {
        P::pairing(*g1, *g2)
    }

    #[inline]
    fn billinear_vec_mul(g1: &Vec<P::G1>, g2: &Vec<P::G2>) -> Vec<PairingOutput<P>> {
        g1.par_iter()
            .zip(g2.par_iter())
            .map(|(g1, g2)|
                Self::billinear_map(g1, g2))
            .collect()
    }

    #[inline]
    fn billinear_vec_dot(g1: &Vec<P::G1>, g2: &Vec<P::G2>) -> PairingOutput<P> {
        g1.par_iter()
            .zip(g2.par_iter())
            .fold_with(PairingOutput::zero(), |acc, (g1, g2)|
                P::pairing(*g1, *g2) + acc
            ).reduce(
                || PairingOutput::zero(),
                |acc, gt| gt + acc)
    }
}

/// Zippel arkworks configuration helper objects
pub struct ArkScalarConfig<F: FftField>(PhantomData<F>);
impl<F: FftField> ArkScalarOps<F> for ArkScalarConfig<F> {}

pub struct ArkGroupConfig<G: ArkGroup>(PhantomData<G>);
impl<G: ArkGroup> ArkGroupOps<G> for ArkGroupConfig<G> {}

pub struct ArkPairingConfig<P: Pairing>(PhantomData<P>);
impl<P: Pairing> ArkPairingOps<P> for ArkPairingConfig<P> {}

/// Sometimes we need a dummy pairing for non-pairing curves (1 curve)
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct DummyPairing<G: CurveGroup>(PhantomData<G>);
impl<G: CurveGroup> Pairing for DummyPairing<G> where G::BaseField : PrimeField {
    type BaseField = G::BaseField;
    type ScalarField = G::ScalarField;
    type G1 = G;
    type G1Affine = G::Affine;
    type G1Prepared = G;

    type G2 = G;
    type G2Affine = G::Affine;
    type G2Prepared = G;
    type TargetField = Nothing;

    // Required methods
    fn multi_miller_loop(
        _: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        _: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        MillerLoopOutput(Nothing::new())
    }

    fn final_exponentiation(
        _: MillerLoopOutput<Self>,
    ) -> Option<PairingOutput<Self>> {
        None
    }
}

/// Concrete Zippel arkworks configurations
pub struct ArkBls12_381 {}
impl ArkConfig for ArkBls12_381 {
    type F = ark_bls12_381::Fr;
    type G1 = ark_bls12_381::G1Projective;
    type G2 = ark_bls12_381::G2Projective;
    type GT = PairingOutput<Bls12<ark_bls12_381::Config>>;
    type P = Bls12<ark_bls12_381::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkBn254 {}
impl ArkConfig for ArkBn254 {
    type F = ark_bn254::Fr;
    type G1 = ark_bn254::G1Projective;
    type G2 = ark_bn254::G2Projective;
    type GT = PairingOutput<Bn<ark_bn254::Config>>;
    type P = Bn<ark_bn254::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkMNT4_298 {}
impl ArkConfig for ArkMNT4_298 {
    type F = ark_mnt4_298::Fr;
    type G1 = ark_mnt4_298::G1Projective;
    type G2 = ark_mnt4_298::G2Projective;
    type GT = PairingOutput<MNT4<ark_mnt4_298::Config>>;
    type P = MNT4<ark_mnt4_298::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkCurve25519 {}
impl ArkConfig for ArkCurve25519 {
    type F = ark_curve25519::Fr;
    type G1 = ark_curve25519::EdwardsProjective;
    type G2 = ark_curve25519::EdwardsProjective;
    type GT = ark_curve25519::EdwardsProjective;
    type P = DummyPairing<ark_curve25519::EdwardsProjective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkSecp256k1 {}
impl ArkConfig for ArkSecp256k1 {
    type F = ark_secp256k1::Fr;
    type G1 = ark_secp256k1::Projective;
    type G2 = ark_secp256k1::Projective;
    type GT = ark_secp256k1::Projective;
    type P = DummyPairing<ark_secp256k1::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkPallas {}
impl ArkConfig for ArkPallas {
    type F = ark_pallas::Fr;
    type G1 = ark_pallas::Projective;
    type G2 = ark_pallas::Projective;
    type GT = ark_pallas::Projective;
    type P = DummyPairing<ark_pallas::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkVesta {}
impl ArkConfig for ArkVesta {
    type F = ark_vesta::Fr;
    type G1 = ark_vesta::Projective;
    type G2 = ark_vesta::Projective;
    type GT = ark_vesta::Projective;
    type P = DummyPairing<ark_vesta::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

pub struct ArkEd25519 {}
impl ArkConfig for ArkEd25519 {
    type F = ark_ed25519::Fr;
    type G1 = ark_ed25519::EdwardsProjective;
    type G2 = ark_ed25519::EdwardsProjective;
    type GT = ark_ed25519::EdwardsProjective;
    type P = DummyPairing<ark_ed25519::EdwardsProjective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type GTOps = ArkGroupConfig<Self::GT>;
    type POps = ArkPairingConfig<Self::P>;
}

/*
   pub type ArkSecp256k1 = ArkSWCurve<ark_secp256k1::Config>;
pub type ArkPallas = ArkSWCurve<ark_pallas::PallasConfig>;
pub type ArkVesta = ArkSWCurve<ark_vesta::VestaConfig>;
pub type ArkEd25519 = ArkTECurve<ark_ed25519::EdwardsConfig>;
pub type ArkF17 = ArkField<F17>;
pub type ArkF65537 = ArkField<F65537>;
*/
