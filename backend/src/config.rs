use core::hash::Hasher;
use rand::Rng;
use rayon::prelude::*;
use spongefish::ProverState;
use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

use ark_ec::VariableBaseMSM;
use ark_ec::bls12::Bls12;
use ark_ec::mnt4::MNT4;
use ark_ec::models::bn::Bn;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::scalar_mul::ScalarMul;
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{AdditiveGroup, Fp64, MontConfig, PrimeField, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::UniformRand;

use crate::nothing::{NoCurve, NoPairing};
// use crate::to_bytes;

/// API to Arkworks finite fields, elliptic curves, and pairings
pub trait ArkConfig: Clone + Copy + Send + Sync + 'static + Eq + PartialEq + fmt::Display + Hash {
    type F: PrimeField;
    type G1: CurveGroup<ScalarField = Self::F, Affine = Self::G1Affine>;
    type G2: CurveGroup<ScalarField = Self::F, Affine = Self::G2Affine>;
    type G1Affine: AffineRepr<ScalarField = Self::F, Group = Self::G1>;
    type G2Affine: AffineRepr<ScalarField = Self::F, Group = Self::G2>;
    type P: Pairing<ScalarField = Self::F, G1 = Self::G1, G2 = Self::G2>;

    /// Operations on arkwork types
    type FOps: ArkScalarOps<Self::F>;
    type G1Ops: ArkGroupOps<Self::G1>;
    type G2Ops: ArkGroupOps<Self::G2>;
    type POps: ArkPairingOps<Self::P>;
}

/// Operations on Arkworks scalar fields
pub trait ArkScalarOps<F: PrimeField> {
    /// Field constants
    #[inline]
    fn zero() -> F {
        F::zero()
    }

    #[inline]
    fn one() -> F {
        F::one()
    }

    /// Scalar addition, saves result in f2
    #[inline]
    fn add(f1: &F, f2: &mut F) {
        *f2 += f1
    }

    /// Scalar negation in place
    #[inline]
    fn neg(f: &mut F) {
        f.neg_in_place();
    }

    /// Scalar subtraction, saves result in f2
    #[inline]
    fn sub(f1: &F, f2: &mut F) {
        Self::neg(f2);
        Self::add(f1, f2);
    }

    /// Scalar multiplication, saves result in f2
    #[inline]
    fn mul(f1: &F, f2: &mut F) {
        *f2 *= f1
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn inv(f: &mut F) {
        f.inverse_in_place();
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn div(f1: &F, f2: &mut F) {
        Self::inv(f2);
        Self::mul(f1, f2);
    }

    /// Scalar exponentiation, saves result in f1
    #[inline]
    fn pow(f1: &mut F, i: u64) {
        let mut i = i;
        while (i % 2) == 0 {
            f1.square_in_place();
            i /= 2;
        }
        *f1 = f1.pow(&[i as u64])
    }

    #[inline]
    fn vec_add(f1: &Vec<F>, f2: &mut Vec<F>) {
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a += b);
    }

    #[inline]
    fn vec_neg(f: &mut Vec<F>) {
        f.par_iter_mut().for_each(|x| {
            x.neg_in_place();
        });
    }

    #[inline]
    fn vec_sub(f1: &Vec<F>, f2: &mut Vec<F>) {
        Self::vec_neg(f2);
        Self::vec_add(f1, f2);
    }

    #[inline]
    fn vec_mul(f1: &Vec<F>, f2: &mut Vec<F>) {
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a *= b);
    }

    #[inline]
    fn vec_dot(f1: &Vec<F>, f2: &Vec<F>) -> F {
        f1.par_iter()
            .zip(f2.par_iter())
            .map(|(a, b)| *a * *b)
            .reduce(|| Self::zero(), |acc, x| acc + x)
    }

    /// Vector batch inversion, saves result in f2
    #[inline]
    fn vec_inv(f: &mut Vec<F>) {
        ark_ff::fields::batch_inversion::<F>(f);
    }

    /// Vector division by batch inversion, saves result in f2
    #[inline]
    fn vec_div(f1: &Vec<F>, f2: &mut Vec<F>) {
        Self::vec_inv(f2);
        ark_ff::fields::batch_inversion::<F>(f2);
        f2.par_iter_mut()
            .zip(f1.par_iter())
            .for_each(|(a, b)| *a *= b);
    }

    #[inline]
    fn vec_pow(f1: &mut Vec<F>, i: u64) {
        f1.par_iter_mut().for_each(|x| {
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
    fn vec_ifft(a: &mut Vec<F>) {
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        domain.ifft_in_place(a);
    }

    #[inline]
    fn vec_fft(a: &mut Vec<F>) {
        let domain: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        domain.fft_in_place(a);
    }

    /// Random and challenge sponge infrastructure
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> F {
        F::rand(rng)
    }

    #[inline]
    fn hash(f: &F, state: &mut ProverState) {
        // state.add_bytes(to_bytes!(f).unwrap());
        unimplemented!("hash not implemented");
    }

    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<F> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut().for_each(|x| *x = Self::rand(rng));
        v
    }

    #[inline]
    fn vec_hash(f: &Vec<F>, state: &mut ProverState) {
        // state.add_bytes(to_bytes!(f).unwrap());
        unimplemented!("vec_hash not implemented");
    }

    #[inline]
    fn write(f: &F, h: &mut fmt::Formatter) -> fmt::Result {
        write!(h, "{}", f)
    }
}

pub trait ArkGroupOps<G: CurveGroup> {
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
    fn add(g1: &G::Affine, g2: &mut G) {
        *g2 += g1;
    }
    #[inline]
    fn neg(g: &mut G) {
        g.neg_in_place();
    }
    #[inline]
    fn sub(g1: &G::Affine, g2: &mut G) {
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
    fn hash(g: &G, state: &mut ProverState) {
        // state.add_bytes(to_bytes!(g).unwrap());
        unimplemented!("hash not implemented");
    }
    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<G> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut().for_each(|x| *x = Self::rand(rng));
        v
    }
    #[inline]
    fn vec_hash(g: &Vec<G>, state: &mut ProverState) {
        // state.add_bytes(to_bytes!(g).unwrap());
        unimplemented!("vec_hash not implemented");
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
    fn write(g: &G, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
}

pub trait ArkPairingOps<P: Pairing> {
    /// Group constants
    #[inline]
    fn zero() -> PairingOutput<P> {
        PairingOutput::ZERO
    }
    #[inline]
    fn generator() -> PairingOutput<P> {
        PairingOutput::generator()
    }
    /// Group operations
    #[inline]
    fn add(g1: &PairingOutput<P>, g2: &mut PairingOutput<P>) {
        *g2 += g1;
    }
    #[inline]
    fn neg(g: &mut PairingOutput<P>) {
        g.neg_in_place();
    }
    #[inline]
    fn sub(g1: &PairingOutput<P>, g2: &mut PairingOutput<P>) {
        Self::neg(g2);
        Self::add(g1, g2);
    }
    #[inline]
    fn mul(f: &<PairingOutput<P> as AdditiveGroup>::Scalar, g: &mut PairingOutput<P>) {
        *g *= f;
    }
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> PairingOutput<P> {
        PairingOutput::rand(rng)
    }
    #[inline]
    fn hash(g: &PairingOutput<P>, state: &mut ProverState) {
        // state.add_bytes(to_bytes!(g).unwrap());
        unimplemented!("hash not implemented");
    }
    #[inline]
    fn vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<PairingOutput<P>> {
        let mut v = vec![Self::zero(); n];
        v.iter_mut().for_each(|x| *x = Self::rand(rng));
        v
    }
    #[inline]
    fn vec_hash(g: &Vec<PairingOutput<P>>, state: &mut ProverState) {
        // state.add_bytes(to_bytes!(g).unwrap());
        unimplemented!("vec_hash not implemented");
    }
    /// Group vec operations
    #[inline]
    fn vec_mul(g: &PairingOutput<P>, f: &Vec<P::ScalarField>) -> Vec<PairingOutput<P>> {
        g.batch_mul(&f[..])
    }
    #[inline]
    fn vec_dot(g: &Vec<PairingOutput<P>>, f: &Vec<P::ScalarField>) -> PairingOutput<P> {
        // TODO: What does Err<usize> mean here?
        <PairingOutput<P> as VariableBaseMSM>::msm(&g[..], &f[..]).unwrap()
    }
    #[inline]
    fn write(g: &PairingOutput<P>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }

    /// Pairing operations
    #[inline]
    fn billinear_map(g1: &P::G1, g2: &P::G2) -> PairingOutput<P> {
        P::pairing(*g1, *g2)
    }

    #[inline]
    fn billinear_vec_mul(g1: &Vec<P::G1>, g2: &Vec<P::G2>) -> Vec<PairingOutput<P>> {
        g1.par_iter()
            .zip(g2.par_iter())
            .map(|(g1, g2)| Self::billinear_map(g1, g2))
            .collect()
    }

    #[inline]
    fn billinear_vec_dot(g1: &Vec<P::G1>, g2: &Vec<P::G2>) -> PairingOutput<P> {
        g1.par_iter()
            .zip(g2.par_iter())
            .fold_with(PairingOutput::zero(), |acc, (g1, g2)| {
                P::pairing(*g1, *g2) + acc
            })
            .reduce(|| PairingOutput::zero(), |acc, gt| gt + acc)
    }
}

/// Zippel arkworks configuration helper objects
pub struct ArkScalarConfig<F: PrimeField>(PhantomData<F>);
impl<F: PrimeField> ArkScalarOps<F> for ArkScalarConfig<F> {}

pub struct ArkGroupConfig<G: CurveGroup>(PhantomData<G>);
impl<G: CurveGroup> ArkGroupOps<G> for ArkGroupConfig<G> {}

pub struct ArkPairingConfig<P: Pairing>(PhantomData<P>);
impl<P: Pairing> ArkPairingOps<P> for ArkPairingConfig<P> {}

/// Concrete Zippel arkworks configurations
#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkBls12_381 {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkBn254 {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkMNT4_298 {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkCurve25519 {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkSecp256k1 {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkPallas {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkVesta {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkEd25519 {}

#[derive(Clone, Debug, Copy, Eq, PartialEq, Hash)]
pub struct ArkFieldN<F: PrimeField>(PhantomData<F>);

pub type ArkField17 = ArkFieldN<F17>;
pub type ArkField65537 = ArkFieldN<F65537>;

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
impl<F: PrimeField> fmt::Display for ArkFieldN<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Field<{}>", F::MODULUS)
    }
}

impl ArkConfig for ArkBls12_381 {
    type F = ark_bls12_381::Fr;
    type G1 = ark_bls12_381::G1Projective;
    type G2 = ark_bls12_381::G2Projective;
    type G1Affine = ark_bls12_381::G1Affine;
    type G2Affine = ark_bls12_381::G2Affine;
    type P = Bls12<ark_bls12_381::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkBn254 {
    type F = ark_bn254::Fr;
    type G1 = ark_bn254::G1Projective;
    type G2 = ark_bn254::G2Projective;
    type G1Affine = ark_bn254::G1Affine;
    type G2Affine = ark_bn254::G2Affine;
    type P = Bn<ark_bn254::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkMNT4_298 {
    type F = ark_mnt4_298::Fr;
    type G1 = ark_mnt4_298::G1Projective;
    type G2 = ark_mnt4_298::G2Projective;
    type G1Affine = ark_mnt4_298::G1Affine;
    type G2Affine = ark_mnt4_298::G2Affine;
    type P = MNT4<ark_mnt4_298::Config>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkCurve25519 {
    type F = ark_curve25519::Fr;
    type G1 = ark_curve25519::EdwardsProjective;
    type G2 = ark_curve25519::EdwardsProjective;
    type G1Affine = ark_curve25519::EdwardsAffine;
    type G2Affine = ark_curve25519::EdwardsAffine;
    type P = NoPairing<ark_curve25519::EdwardsProjective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkSecp256k1 {
    type F = ark_secp256k1::Fr;
    type G1 = ark_secp256k1::Projective;
    type G2 = ark_secp256k1::Projective;
    type G1Affine = ark_secp256k1::Affine;
    type G2Affine = ark_secp256k1::Affine;
    type P = NoPairing<ark_secp256k1::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkPallas {
    type F = ark_pallas::Fr;
    type G1 = ark_pallas::Projective;
    type G2 = ark_pallas::Projective;
    type G1Affine = ark_pallas::Affine;
    type G2Affine = ark_pallas::Affine;
    type P = NoPairing<ark_pallas::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkVesta {
    type F = ark_vesta::Fr;
    type G1 = ark_vesta::Projective;
    type G2 = ark_vesta::Projective;
    type G1Affine = ark_vesta::Affine;
    type G2Affine = ark_vesta::Affine;
    type P = NoPairing<ark_vesta::Projective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl ArkConfig for ArkEd25519 {
    type F = ark_ed25519::Fr;
    type G1 = ark_ed25519::EdwardsProjective;
    type G2 = ark_ed25519::EdwardsProjective;
    type G1Affine = ark_ed25519::EdwardsAffine;
    type G2Affine = ark_ed25519::EdwardsAffine;
    type P = NoPairing<ark_ed25519::EdwardsProjective>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

impl<F: PrimeField> ArkConfig for ArkFieldN<F> {
    type F = F;
    type G1 = NoCurve<F>;
    type G2 = NoCurve<F>;
    type G1Affine = NoCurve<F>;
    type G2Affine = NoCurve<F>;
    type P = NoPairing<NoCurve<F>>;

    type FOps = ArkScalarConfig<Self::F>;
    type G1Ops = ArkGroupConfig<Self::G1>;
    type G2Ops = ArkGroupConfig<Self::G2>;
    type POps = ArkPairingConfig<Self::P>;
}

#[derive(MontConfig, Clone, Copy, Eq, PartialEq, Hash)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
pub type F17 = Fp64<F17Config>;

#[derive(MontConfig, Clone, Copy, Eq, PartialEq, Hash)]
#[modulus = "65537"]
#[generator = "3"]
pub struct F65537Config;
pub type F65537 = Fp64<F65537Config>;
