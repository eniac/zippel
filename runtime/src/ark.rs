use rand::Rng;
use std::hash::Hash;
use std::marker::PhantomData;
use core::hash::Hasher;
use rayon::prelude::*;

use ark_poly::{DenseMVPolynomial, DenseUVPolynomial, MultilinearExtension, Polynomial};
use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;
use ark_ff::{Zero, One, Field, UniformRand};
use ark_ff::{Fp64, MontBackend, MontConfig, FftField};
use ark_ec::scalar_mul::ScalarMul;
use ark_ec::{VariableBaseMSM, AffineRepr};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::models::short_weierstrass::{Affine as SWAffine, SWCurveConfig};
use ark_ec::models::twisted_edwards::{Affine as TEAffine, TECurveConfig};

/// Represents a type instantiation of a zippel program in Arkworks
pub trait ArkConfig {
    type F: FftField;
    type G1;
    type G2;
    type GT;

    // Field constants
    fn scalar_zero() -> Self::F {
        Self::F::zero()
    }
    fn scalar_one() -> Self::F {
        Self::F::one()
    }
    // Scalars
    fn scalar_add(f1: Self::F, f2: Self::F) -> Self::F {
        f1 + f2
    }
    fn scalar_sub(f1: Self::F, f2: Self::F) -> Self::F {
        f1 - f2
    }
    fn scalar_mul(f1: Self::F, f2: Self::F) -> Self::F {
        f1 * f2
    }
    fn scalar_div(f1: Self::F, f2: Self::F) -> Self::F {
        f1 / f2
    }
    fn scalar_pow(f1: Self::F, i: u64) -> Self::F {
        f1.pow(&[i])
    }
    fn scalar_dot(f1: Self::F, f2: Self::F) -> Self::F {
        f1 * f2
    }
    fn scalar_batch_div(f1: Vec<Self::F>, f2: Vec<Self::F>) -> Vec<Self::F> {
        let mut f2 = f2;
        ark_ff::fields::batch_inversion::<Self::F>(&mut f2);
        f1.par_iter().zip(f2.par_iter()).map(|(a, b)| *a / *b).collect()
    }
    // Univariates
    fn uni_add(a: Uni<Self::F>, b: Uni<Self::F>) -> Uni<Self::F> {
        a + b
    }
    fn uni_sub(a: Uni<Self::F>, b: Uni<Self::F>) -> Uni<Self::F> {
        a - b
    }
    fn uni_scalar_mul(a: Uni<Self::F>, b: Self::F) -> Uni<Self::F> {
        a * b
    }
    fn uni_mul(a: Uni<Self::F>, b: Uni<Self::F>) -> Uni<Self::F> {
        a * b
    }
    fn uni_div(a: Uni<Self::F>, b: Uni<Self::F>) -> Uni<Self::F> {
        a / b
    }
    fn uni_eval(a: Uni<Self::F>, b: Self::F) -> Self::F {
        a.evaluate(&b)
    }
    fn uni_coeffs(a: Vec<Self::F>) -> Uni<Self::F> {
        Uni::from_coefficients_vec(a)
    }
    fn uni_rand<R: Rng>(rng: &mut R, n: usize) -> Uni<Self::F> {
        <Uni<Self::F> as DenseUVPolynomial<Self::F>>::rand(n, rng)
    }
    fn uni_interpolate(a: Vec<Self::F>) -> Uni<Self::F> {
        let domain: GeneralEvaluationDomain<Self::F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        let mut a = a;
        domain.ifft_in_place(&mut a);
        Self::uni_coeffs(a)
    }
    // MLEs
    fn mle_add(a: Mle<Self::F>, b: Mle<Self::F>) -> Mle<Self::F> {
        a + b
    }
    fn mle_sub(a: Mle<Self::F>, b: Mle<Self::F>) -> Mle<Self::F> {
        a - b
    }
    fn mle_mul(a: Mle<Self::F>, b: Self::F) -> Mle<Self::F> {
        a * b
    }
    fn mle_eval(a: Mle<Self::F>, b: Vec<Self::F>) -> Self::F {
        a.evaluate(&b)
    }
    fn mle_rand<R: Rng>(rng: &mut R, num_vars: usize) -> Mle<Self::F> {
        <Mle<Self::F> as MultilinearExtension<Self::F>>::rand(num_vars, rng)
    }
    fn mle_evals(num_vars: usize, a: Vec<Self::F>) -> Mle<Self::F> {
        Mle::from_evaluations_vec(num_vars, a)
    }
    // Random and hashing
    fn scalar_rand<R: Rng + ?Sized>(rng: &mut R) -> Self::F {
        Self::F::rand(rng)
    }
    fn scalar_hash<H: Hasher>(f: Self::F, h: &mut H) {
        f.hash(h)
    }

    // Group constants
    fn group_zero1() -> Self::G1;
    fn group_zero2() -> Self::G2;
    fn group_zerot() -> Self::GT;

    // Groups
    fn group_add1(g1: Self::G1, g2: Self::G1) -> Self::G1;
    fn group_add2(g1: Self::G2, g2: Self::G2) -> Self::G2;
    fn group_addt(g1: Self::GT, g2: Self::GT) -> Self::GT;
    fn group_sub1(g1: Self::G1, g2: Self::G1) -> Self::G1;
    fn group_sub2(g1: Self::G2, g2: Self::G2) -> Self::G2;
    fn group_subt(g1: Self::GT, g2: Self::GT) -> Self::GT;
    fn scalar_group_mul1(g: Self::G1, f: Vec<Self::F>) -> Vec<Self::G1>;
    fn scalar_group_mul2(g: Self::G2, f: Vec<Self::F>) -> Vec<Self::G2>;
    fn scalar_group_mult(g: Self::GT, f: Vec<Self::F>) -> Vec<Self::GT>;
    fn scalar_group_dot1(g: Vec<Self::G1>, f: Vec<Self::F>) -> Self::G1;
    fn scalar_group_dot2(g: Vec<Self::G2>, f: Vec<Self::F>) -> Self::G2;
    fn scalar_group_dott(g: Vec<Self::GT>, f: Vec<Self::F>) -> Self::GT;
    fn billinear_map(g1: Self::G1, g2: Self::G2) -> Self::GT;
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1;
    fn group_rand2<R: Rng + ?Sized>(rng: &mut R) -> Self::G2;
    fn group_randt<R: Rng + ?Sized>(rng: &mut R) -> Self::GT;
    fn group_hash1<H: Hasher>(g: Self::G1, h: &mut H);
    fn group_hash2<H: Hasher>(g: Self::G2, h: &mut H);
    fn group_hasht<H: Hasher>(g: Self::GT, h: &mut H);
}

/// Object representing a Zippel configuration for fields
pub struct ArkField<F: FftField> {
    _field: PhantomData<F>,
}

/// For a signle field <F>
impl<F: FftField> ArkConfig for ArkField<F> {
    type F = F;
    type G1 = ();
    type G2 = ();
    type GT = ();

    // Group constants
    fn group_zero1() -> Self::G1 {
        unimplemented!()
    }
    fn group_zero2() -> Self::G2 {
        unimplemented!()
    }
    fn group_zerot() -> Self::GT {
        unimplemented!()
    }
    // Groups
    fn group_add1(_: Self::G1, _: Self::G1) -> Self::G1 {
        unimplemented!()
    }
    fn group_add2(_: Self::G2, _: Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_addt(_: Self::GT, _: Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn group_sub1(_: Self::G1, _: Self::G1) -> Self::G1 {
        unimplemented!()
    }
    fn group_sub2(_: Self::G2, _: Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_subt(_: Self::GT, _: Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn scalar_group_mul1(_: Self::G1, _: Vec<Self::F>) -> Vec<Self::G1> {
        unimplemented!()
    }
    fn scalar_group_mul2(_: Self::G2, _: Vec<Self::F>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn scalar_group_mult(_: Self::GT, _: Vec<Self::F>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn scalar_group_dot1(_: Vec<Self::G1>, _: Vec<Self::F>) -> Self::G1 {
        unimplemented!()
    }
    fn scalar_group_dot2(_: Vec<Self::G2>, _: Vec<Self::F>) -> Self::G2 {
        unimplemented!()
    }
    fn scalar_group_dott(_: Vec<Self::GT>, _: Vec<Self::F>) -> Self::GT {
        unimplemented!()
    }
    fn billinear_map(_: Self::G1, _: Self::G2) -> Self::GT {
        unimplemented!()
    }
    fn group_rand1<R: Rng + ?Sized>(_: &mut R) -> Self::G1 {
        unimplemented!()
    }
    fn group_rand2<R: Rng + ?Sized>(_: &mut R) -> Self::G2 {
        unimplemented!()
    }
    fn group_randt<R: Rng + ?Sized>(_: &mut R) -> Self::GT {
        unimplemented!()
    }
    fn group_hash1<H: Hasher>(_: Self::G1, _: &mut H) {
        unimplemented!()
    }
    fn group_hash2<H: Hasher>(_: Self::G2, _: &mut H) {
        unimplemented!()
    }
    fn group_hasht<H: Hasher>(_: Self::GT, _: &mut H) {
        unimplemented!()
    }
}


/// Object representing a Zippel configuration for Short-Weierstrass curves
pub struct ArkSWCurve<C: SWCurveConfig> {
    _curve: PhantomData<C>,
}

impl<C: SWCurveConfig> ArkConfig for ArkSWCurve<C> {
    type F = C::ScalarField;
    type G1 = SWAffine<C>;
    type G2 = ();
    type GT = ();

    // Group constants
    fn group_zero1() -> Self::G1 {
        Self::G1::zero()
    }
    fn group_zero2() -> Self::G2 {
        unimplemented!()
    }
    fn group_zerot() -> Self::GT {
        unimplemented!()
    }
    // Groups
    fn group_add2(_: Self::G2, _: Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_addt(_: Self::GT, _: Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn group_sub2(_: Self::G2, _: Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_subt(_: Self::GT, _: Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn scalar_group_mul2(_: Self::G2, _: Vec<Self::F>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn scalar_group_mult(_: Self::GT, _: Vec<Self::F>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn scalar_group_dot2(_: Vec<Self::G2>, _: Vec<Self::F>) -> Self::G2 {
        unimplemented!()
    }
    fn scalar_group_dott(_: Vec<Self::GT>, _: Vec<Self::F>) -> Self::GT {
        unimplemented!()
    }
    fn billinear_map(_: Self::G1, _: Self::G2) -> Self::GT {
        unimplemented!()
    }
    fn group_rand2<R: Rng + ?Sized>(_: &mut R) -> Self::G2 {
        unimplemented!()
    }
    fn group_randt<R: Rng + ?Sized>(_: &mut R) -> Self::GT {
        unimplemented!()
    }
    fn group_hash2<H: Hasher>(_: Self::G2, _: &mut H) {
        unimplemented!()
    }
    fn group_hasht<H: Hasher>(_: Self::GT, _: &mut H) {
        unimplemented!()
    }
    // Groups
    fn group_add1(g1: Self::G1, g2: Self::G1) -> Self::G1 {
        (g1 + g2).into()
    }
    fn group_sub1(g1: Self::G1, g2: Self::G1) -> Self::G1 {
        (g1 - g2).into()
    }
    fn scalar_group_mul1(g1: Self::G1, f1: Vec<Self::F>) -> Vec<Self::G1> {
        g1.into_group().batch_mul(&f1[..])
    }
    fn scalar_group_dot1(g1: Vec<Self::G1>, f1: Vec<Self::F>) -> Self::G1 {
        // TODO: What does Err<usize> mean here?
        C::msm(&g1[..], &f1[..]).unwrap().into()
    }
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1 {
        Self::G1::rand(rng)
    }
    fn group_hash1<H: Hasher>(g: Self::G1, h: &mut H) {
        g.hash(h)
    }
}

/// TODO: Object representing a Zippel configuration for twisted edwards curves
pub struct ArkTECurve<C: TECurveConfig> {
    _curve: PhantomData<C>,
}

impl<C: TECurveConfig> ArkConfig for ArkTECurve<C> {
    type F = C::ScalarField;
    type G1 = TEAffine<C>;
    type G2 = ();
    type GT = ();

    // Group constants
    fn group_zero1() -> Self::G1 {
        Self::G1::zero()
    }
    fn group_zero2() -> Self::G2 {
        unimplemented!()
    }
    fn group_zerot() -> Self::GT {
        unimplemented!()
    }
    // Groups
    fn group_add2(_: Self::G2, _: Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_addt(_: Self::GT, _: Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn group_sub2(_: Self::G2, _: Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_subt(_: Self::GT, _: Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn scalar_group_mul2(_: Self::G2, _: Vec<Self::F>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn scalar_group_mult(_: Self::GT, _: Vec<Self::F>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn scalar_group_dot2(_: Vec<Self::G2>, _: Vec<Self::F>) -> Self::G2 {
        unimplemented!()
    }
    fn scalar_group_dott(_: Vec<Self::GT>, _: Vec<Self::F>) -> Self::GT {
        unimplemented!()
    }
    fn billinear_map(_: Self::G1, _: Self::G2) -> Self::GT {
        unimplemented!()
    }
    fn group_rand2<R: Rng + ?Sized>(_: &mut R) -> Self::G2 {
        unimplemented!()
    }
    fn group_randt<R: Rng + ?Sized>(_: &mut R) -> Self::GT {
        unimplemented!()
    }
    fn group_hash2<H: Hasher>(_: Self::G2, _: &mut H) {
        unimplemented!()
    }
    fn group_hasht<H: Hasher>(_: Self::GT, _: &mut H) {
        unimplemented!()
    }
    // Groups
    fn group_add1(g1: Self::G1, g2: Self::G1) -> Self::G1 {
        (g1 + g2).into()
    }
    fn group_sub1(g1: Self::G1, g2: Self::G1) -> Self::G1 {
        (g1 - g2).into()
    }
    fn scalar_group_mul1(g1: Self::G1, f1: Vec<Self::F>) -> Vec<Self::G1> {
        g1.into_group().batch_mul(&f1[..])
    }
    fn scalar_group_dot1(g1: Vec<Self::G1>, f1: Vec<Self::F>) -> Self::G1 {
        // TODO: What does Err<usize> mean here?
        C::msm(&g1[..], &f1[..]).unwrap().into()
    }
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1 {
        Self::G1::rand(rng)
    }
    fn group_hash1<H: Hasher>(g: Self::G1, h: &mut H) {
        g.hash(h)
    }
}

/// Object representing a Zippel configuration for pairing friendly curves
pub struct ArkPairing<P: Pairing> {
    _pairing: PhantomData<P>,
}

/// For pairing friendly curves
impl<P: Pairing> ArkConfig for ArkPairing<P> {
    type F = P::ScalarField;
    type G1 = P::G1Affine;
    type G2 = P::G2Affine;
    type GT = PairingOutput<P>;

    // Group constants
    fn group_zero1() -> Self::G1 {
        Self::G1::zero()
    }
    fn group_zero2() -> Self::G2 {
        Self::G2::zero()
    }
    fn group_zerot() -> Self::GT {
        Self::GT::zero()
    }
    // Groups
    fn group_add1(g1: Self::G1, g2: Self::G1) -> Self::G1 {
        (g1 + g2).into()
    }
    fn group_add2(g1: Self::G2, g2: Self::G2) -> Self::G2 {
        (g1 + g2).into()
    }
    fn group_addt(gt1: Self::GT, gt2: Self::GT) -> Self::GT {
        (gt1 + gt2).into()
    }
    fn group_sub1(g1: Self::G1, g2: Self::G1) -> Self::G1 {
        (g1 - g2).into()
    }
    fn group_sub2(g1: Self::G2, g2: Self::G2) -> Self::G2 {
        (g1 - g2).into()
    }
    fn group_subt(gt1: Self::GT, gt2: Self::GT) -> Self::GT {
        (gt1 - gt2).into()
    }
    fn scalar_group_mul1(g1: Self::G1, f1: Vec<Self::F>) -> Vec<Self::G1> {
        P::G1::batch_mul(g1.into(), &f1)
    }
    fn scalar_group_mul2(g2: Self::G2, f2: Vec<Self::F>) -> Vec<Self::G2> {
        P::G2::batch_mul(g2.into(), &f2)
    }
    fn scalar_group_dot1(g1: Vec<Self::G1>, f1: Vec<Self::F>) -> Self::G1 {
        P::G1::msm(&g1[..], &f1[..]).unwrap().into()
    }
    fn scalar_group_dot2(g2: Vec<Self::G2>, f2: Vec<Self::F>) -> Self::G2 {
        P::G2::msm(&g2[..], &f2[..]).unwrap().into()
    }
    fn scalar_group_mult(gt: Self::GT, ft: Vec<Self::F>) -> Vec<Self::GT> {
        Self::GT::batch_mul(gt, &ft)
    }
    fn scalar_group_dott(gt: Vec<Self::GT>, ft: Vec<Self::F>) -> Self::GT {
        Self::GT::msm(&gt[..], &ft[..]).unwrap()
    }
    fn billinear_map(g1: Self::G1, g2: Self::G2) -> Self::GT {
        P::pairing(g1, g2)
    }
    // Random and hashes
    fn scalar_rand<R: Rng + ?Sized>(rng: &mut R) -> Self::F {
        Self::F::rand(rng)
    }
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1 {
        Self::G1::rand(rng)
    }
    fn group_rand2<R: Rng + ?Sized>(rng: &mut R) -> Self::G2 {
        Self::G2::rand(rng)
    }
    fn group_randt<R: Rng + ?Sized>(rng: &mut R) -> Self::GT {
        Self::GT::rand(rng)
    }
    fn scalar_hash<H: Hasher>(f: Self::F, h: &mut H) {
        f.hash(h)
    }
    fn group_hash1<H: Hasher>(g: Self::G1, h: &mut H) {
        g.hash(h)
    }
    fn group_hash2<H: Hasher>(g: Self::G2, h: &mut H) {
        g.hash(h)
    }
    fn group_hasht<H: Hasher>(g: Self::GT, h: &mut H) {
        g.hash(h)
    }
}

///Zippel arkworks configurations
pub type ArkBls12_381 = ArkPairing<ark_bls12_381::Config>;
pub type ArkCurve25519 = ArkTECurve<ark_curve25519::Curve25519Config>;
pub type ArkBn254 = ArkPairing<ark_bn254::Config>;
pub type ArkMNT4_298 = ArkPairing<ark_mnt4_298::Config>;
pub type ArkSecp256k1 = ArkSWCurve<ark_secp256k1::Config>;
pub type ArkPallas = ArkSWCurve<ark_pallas::PallasConfig>;
pub type ArkVesta = ArkSWCurve<ark_vesta::VestaConfig>;
pub type ArkEd25519 = ArkTECurve<ark_ed25519::EdwardsConfig>;

/// Prime Fields for fun and debugging
// Define the field configuration
#[derive(MontConfig)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
pub type F17 = Fp64<F17Config>;

#[derive(MontConfig)]
#[modulus = "65537"]
#[generator = "3"]
pub struct F65537Config;
pub type F65537 = Fp64<F65537Config>;

pub type ArkF17 = ArkField<F17>;
pub type ArkF65537 = ArkField<F65537>;

