use rand::Rng;
use std::hash::Hash;
use std::fmt;
use std::ops::{Add, Div, Mul, MulAssign, Neg, Sub};
use std::marker::PhantomData;
use core::hash::Hasher;
use rayon::prelude::*;

use ark_poly::{DenseMVPolynomial, DenseUVPolynomial, MultilinearExtension, Polynomial};
use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;
use ark_ff::{AdditiveGroup, BigInteger, Field, One, UniformRand, Zero};
use ark_ff::{Fp64, MontBackend, MontConfig, FftField};
use ark_ec::scalar_mul::{BatchMulPreprocessing, ScalarMul};
use ark_ec::{VariableBaseMSM, AffineRepr};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::models::short_weierstrass::{Affine as SWAffine, SWCurveConfig};
use ark_ec::models::twisted_edwards::{Affine as TEAffine, TECurveConfig};
use ark_ec::bls12::Bls12;
use ark_ec::models::bn::Bn;
use ark_ec::mnt4::MNT4;

/// Represents a type instantiation of a zippel program in Arkworks
pub trait ArkConfig {
    type F: FftField;
    type G1: Copy + Send + Sync;
    type G2: Copy + Send + Sync;
    type GT: Copy + Send + Sync;

    /// Field constants
    #[inline]
    fn scalar_zero() -> Self::F {
        Self::F::zero()
    }

    #[inline]
    fn scalar_one() -> Self::F {
        Self::F::one()
    }

    /// Scalar addition, saves result in f2
    #[inline]
    fn scalar_add(f1: &Self::F, f2: &mut Self::F) {
        *f2 += f1
    }

    /// Scalar negation in place
    #[inline]
    fn scalar_neg(f: &mut Self::F) {
        f.neg_in_place();
    }

    /// Scalar subtraction, saves result in f2
    #[inline]
    fn scalar_sub(f1: &Self::F, f2: &mut Self::F) {
        Self::scalar_neg(f2);
        Self::scalar_add(f1, f2);
    }

    /// Scalar multiplication, saves result in f2
    #[inline]
    fn scalar_mul(f1: &Self::F, f2: &mut Self::F) {
        *f2 *= f1
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn scalar_inv(f: &mut Self::F) {
        f.inverse_in_place();
    }

    /// Scalar division, saves result in f2
    #[inline]
    fn scalar_div(f1: &Self::F, f2: &mut Self::F) {
        Self::scalar_inv(f2);
        Self::scalar_mul(f1, f2);
    }

    /// Scalar exponentiation, saves result in f1
    #[inline]
    fn scalar_pow(f1: &mut Self::F, i: u64) {
        let mut i = i;
        while (i % 2) == 0 {
            f1.square_in_place();
            i /= 2;
        }
        *f1 = f1.pow(&[i as u64])
    }

    /// Random and hashing
    #[inline]
    fn scalar_rand<R: Rng + ?Sized>(rng: &mut R) -> Self::F {
        Self::F::rand(rng)
    }

    #[inline]
    fn scalar_hash<H: Hasher>(f: Self::F, h: &mut H) {
        f.hash(h)
    }

    /// Vector batch inversion, saves result in f2
    #[inline]
    fn scalar_vec_inv(f: &mut Vec<Self::F>) {
        ark_ff::fields::batch_inversion::<Self::F>(f);
    }

    /// Vector division by batch inversion, saves result in f2
    #[inline]
    fn scalar_vec_div(f1: &Vec<Self::F>, f2: &mut Vec<Self::F>) {
        Self::scalar_vec_inv(f2);
        ark_ff::fields::batch_inversion::<Self::F>(f2);
        f2.par_iter_mut()
        .zip(f1.par_iter())
        .for_each(|(a, b)| *a *= b);
    }

    #[inline]
    fn scalar_vec_rand<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<Self::F> {
        let mut v = vec![Self::scalar_zero(); n];
        v.iter_mut()
            .for_each(|x| *x = Self::scalar_rand(rng));
        v
    }

    /// Convert a scalar to a univariate polynomial of degree 0
    #[inline]
    fn into_uni(a: Self::F) -> Uni<Self::F> {
        Uni::from_coefficients_vec(vec![a])
    }

    /// Construct a univariate polynomial from its coefficients
    #[inline]
    fn uni_coeffs(a: Vec<Self::F>) -> Uni<Self::F> {
        Uni::from_coefficients_vec(a)
    }

    /// Add univariate polynomials, saves result in b
    #[inline]
    fn uni_add(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        *b += a;
    }

    /// Negate univariate polynomial in place
    #[inline]
    fn uni_neg(a: &mut Uni<Self::F>) {
        a.par_iter_mut().for_each(|x| { x.neg_in_place(); });
    }

    /// Subtract univariate polynomials, saves result in b
    #[inline]
    fn uni_sub(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        Self::uni_neg(b);
        *b += a;
    }

    /// Multiply univariate polynomials, saves result in b
    #[inline]
    fn uni_mul(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        // TODO: In place O(nlogn) multiplication for polynomials?
        *b = b.clone() * a;
    }

    /// Divide univariate polynomials, saves result in b
    #[inline]
    fn uni_div(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        // TODO: In place O(nlogn) division for polynomials?
        *b = a / b.clone();
    }

    /// Exponentiate univariate polynomial, saves result in f1
    #[inline]
    fn uni_pow(f1: &mut Uni<Self::F>, i: u64) {
        let mut i = i;
        let uni = f1.clone();
        while (i % 2) == 0 {
            Self::uni_mul(&uni, f1);
            i /= 2;
        }
        while i > 1 {
            Self::uni_mul(&uni, f1);
            i -= 1;
        }
    }

    /// Evaluate univariate polynomial at a point
    #[inline]
    fn uni_eval(a: Uni<Self::F>, b: Self::F) -> Self::F {
        a.evaluate(&b)
    }

    /// Random univariate polynomial, of degree n
    #[inline]
    fn uni_rand<R: Rng>(rng: &mut R, n: usize) -> Uni<Self::F> {
        <Uni<Self::F> as DenseUVPolynomial<Self::F>>::rand(n, rng)
    }

    /// Interpolate a vector of y-coefficients to a univariate polynomial
    #[inline]
    fn uni_interpolate(a: Vec<Self::F>) -> Uni<Self::F> {
        let domain: GeneralEvaluationDomain<Self::F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        let mut a = a;
        domain.ifft_in_place(&mut a);
        Self::uni_coeffs(a)
    }

    /// Convert a scalar to a multilinear extension with 0 variables
    #[inline]
    fn into_mle(a: Self::F) -> Mle<Self::F> {
        Mle::from_evaluations_vec(0, vec![a])
    }

    /// Add multilinear extensions, saves result in b
    #[inline]
    fn mle_add(a: &Mle<Self::F>, b: &mut Mle<Self::F>) {
        *b += a;
    }

    /// Negate multilinear extension in-place
    #[inline]
    fn mle_neg(b: &mut Mle<Self::F>) {
        b.iter_mut().par_bridge().for_each(|x| { x.neg_in_place(); });
    }

    /// Subtract multilinear extensions, saves result in b
    #[inline]
    fn mle_sub(a: &Mle<Self::F>, b: &mut Mle<Self::F>) {
        Self::mle_neg(b);
        *b += a;
    }

    /// Multiply multilinear extension by scalar, saves result in b
    #[inline]
    fn mle_mul(a: &Self::F, b: &mut Mle<Self::F>) {
        *b *= a
    }

    /// Divide multilinear extension by scalar, saves result in b
    #[inline]
    fn mle_div(a: &Self::F, b: &mut Mle<Self::F>) {
        let mut a = a.clone();
        Self::scalar_inv(&mut a);
        Self::mle_mul(&a, b);
    }

    /// Divide multilinear extension by scalar, saves result in b
    #[inline]
    fn mle_eval(a: Mle<Self::F>, b: Vec<Self::F>) -> Self::F {
        a.evaluate(&b)
    }

    /// Random multilinear extension, of degree n
    #[inline]
    fn mle_rand<R: Rng>(rng: &mut R, num_vars: usize) -> Mle<Self::F> {
        <Mle<Self::F> as MultilinearExtension<Self::F>>::rand(num_vars, rng)
    }

    /// Evaluate multilinear extension at a point
    #[inline]
    fn mle_evals(num_vars: usize, a: Vec<Self::F>) -> Mle<Self::F> {
        Mle::from_evaluations_vec(num_vars, a)
    }

    /// Hash an MLE
    #[inline]
    fn mle_hash<H: Hasher>(f: Mle<Self::F>, h: &mut H) {
        f.hash(h)
    }

    /// Printing
    fn scalar_fmt(a: &Self::F, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", a)
    }

    fn uni_fmt(a: &Uni<Self::F>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", a.coeffs[0])?;
        let mut i = 1;
        for c in a.coeffs.iter() {
            write!(f, "{}x^{} + ", c, i)?;
            i += 1;
        }
        Ok(())
    }

    fn mle_fmt(a: &Mle<Self::F>, f: &mut fmt::Formatter) -> fmt::Result {
        // Utility to convert evaluations over boolean hypercube into coefficient form
        fn mobius_transform<F: FftField>(evaluations: &mut [F], n: usize) {
            for i in 0..n {
                for mask in 0..(1 << n) {
                    if (mask & (1 << i)) != 0 {
                        evaluations[mask] = evaluations[mask] - evaluations[mask ^ (1 << i)];
                    }
                }
            }
        }

        // Utility to convert mask into readable monomials.
        fn mask_to_monomial(mask: usize, n: usize) -> String {
            if mask == 0 { return "1".to_string(); }
            let mut terms = vec![];
            for i in 0..n {
                if (mask & (1 << i)) != 0 {
                    terms.push(format!("x{}", i + 1));
                }
            }
            terms.join(" * ")
        }
        let mut evals = a.evaluations.clone();
        mobius_transform(&mut evals, a.num_vars);
        write!(f, "(", )?;
        for mask in 0..(1 << a.num_vars) {
            let coef = evals[mask];
            if coef.is_zero() {
                continue;
            } else {
                write!(f, "{} * {}", coef, mask_to_monomial(mask, a.num_vars))?;
            }
        }
        write!(f, ")")
    }

    /// Group constants
    fn group_zero1() -> Self::G1;
    fn group_zero2() -> Self::G2;
    fn group_zerot() -> Self::GT;

    /// Group operations
    fn group_add1(g1: &Self::G1, g2: &mut Self::G1);
    fn group_add2(g1: &Self::G2, g2: &mut Self::G2);
    fn group_addt(g1: &Self::GT, g2: &mut Self::GT);
    fn group_neg1(g: &mut Self::G1);
    fn group_neg2(g: &mut Self::G2);
    fn group_negt(g: &mut Self::GT);
    fn group_mul1(f: &Self::F, g: &mut Self::G1);
    fn group_mul2(f: &Self::F, g: &mut Self::G2);
    fn group_mult(f: &Self::F, g: &mut Self::GT);

    #[inline]
    fn group_sub1(g1: &Self::G1, g2: &mut Self::G1) {
        Self::group_neg1(g2);
        Self::group_add1(g1, g2);
    }

    #[inline]
    fn group_sub2(g1: &Self::G2, g2: &mut Self::G2) {
        Self::group_neg2(g2);
        Self::group_add2(g1, g2);
    }

    #[inline]
    fn group_subt(g1: &Self::GT, g2: &mut Self::GT) {
        Self::group_negt(g2);
        Self::group_addt(g1, g2);
    }


    fn billinear_map(g1: &Self::G1, g2: &Self::G2) -> Self::GT;

    #[inline]
    fn billinear_vec_mul(g1: &Vec<Self::G1>, g2: &Vec<Self::G2>) -> Vec<Self::GT> {
        g1.par_iter()
            .zip(g2.par_iter())
            .map(|(g1, g2)|
                Self::billinear_map(g1, g2))
            .collect()
    }
    #[inline]
    fn billinear_vec_dot(g1: &Vec<Self::G1>, g2: &Vec<Self::G2>) -> Self::GT {
        g1.par_iter()
            .zip(g2.par_iter())
            .fold_with(Self::group_zerot(), |acc, (g1, g2)| {
                let mut gt = Self::billinear_map(g1, g2);
                Self::group_addt(&acc, &mut gt);
                gt
            }).reduce(
                || Self::group_zerot(),
                |acc, mut gt| {
                    Self::group_addt(&acc, &mut gt);
                    gt
                })
    }

    /// Random group elements and hashing
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1;
    fn group_rand2<R: Rng + ?Sized>(rng: &mut R) -> Self::G2;
    fn group_randt<R: Rng + ?Sized>(rng: &mut R) -> Self::GT;

    #[inline]
    fn group_vec_rand1<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<Self::G1> {
        let mut v = vec![Self::group_zero1(); n];
        v.iter_mut()
            .for_each(|x| *x = Self::group_rand1(rng));
        v
    }

    #[inline]
    fn group_vec_rand2<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<Self::G2> {
        let mut v = vec![Self::group_zero2(); n];
        v.iter_mut()
            .for_each(|x| *x = Self::group_rand2(rng));
        v
    }

    #[inline]
    fn group_vec_randt<R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<Self::GT> {
        let mut v = vec![Self::group_zerot(); n];
        v.iter_mut()
            .for_each(|x| *x = Self::group_randt(rng));
        v
    }
    fn group_hash1<H: Hasher>(g: &Self::G1, h: &mut H);
    fn group_hash2<H: Hasher>(g: &Self::G2, h: &mut H);
    fn group_hasht<H: Hasher>(g: &Self::GT, h: &mut H);

    /// Group vec operations
    fn scalar_group_mul1(g: &Self::G1, f: &Vec<Self::F>) -> Vec<Self::G1>;
    fn scalar_group_mul2(g: &Self::G2, f: &Vec<Self::F>) -> Vec<Self::G2>;
    fn scalar_group_mult(g: &Self::GT, f: &Vec<Self::F>) -> Vec<Self::GT>;
    fn scalar_group_dot1(g: &Vec<Self::G1>, f: &Vec<Self::F>) -> Self::G1;
    fn scalar_group_dot2(g: &Vec<Self::G2>, f: &Vec<Self::F>) -> Self::G2;
    fn scalar_group_dott(g: &Vec<Self::GT>, f: &Vec<Self::F>) -> Self::GT;

    /// Group printing
    fn group_fmt1(g: &Self::G1, f: &mut fmt::Formatter) -> fmt::Result;
    fn group_fmt2(g: &Self::G2, f: &mut fmt::Formatter) -> fmt::Result;
    fn group_fmtt(g: &Self::GT, f: &mut fmt::Formatter) -> fmt::Result;

}

/// Object representing a Zippel configuration for fields
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct ArkField<F: FftField> {
    _field: PhantomData<F>,
}

impl<F: FftField> ArkField<F> {
    /// Create a new field configuration
    pub fn new() -> Self {
        Self { _field: PhantomData }
    }
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
    fn group_add1(_: &Self::G1, _: &mut Self::G1) -> Self::G1 {
        unimplemented!()
    }
    fn group_add2(_: &Self::G2, _: &mut Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_addt(_: &Self::GT, _: &mut Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn group_sub1(_: &Self::G1, _: &mut Self::G1) -> Self::G1 {
        unimplemented!()
    }
    fn group_sub2(_: &Self::G2, _: &mut Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_subt(_: &Self::GT, _: &mut Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn group_mul1(_: &Self::F, _: &mut Self::G1) -> Self::G1 {
        unimplemented!()
    }
    fn group_mul2(_: &Self::F, _: &mut Self::G2) -> Self::G2 {
        unimplemented!()
    }
    fn group_mult(_: &Self::F, _: &mut Self::GT) -> Self::GT {
        unimplemented!()
    }
    fn scalar_group_mul1(_: &Self::G1, _: &Vec<Self::F>) -> Vec<Self::G1> {
        unimplemented!()
    }
    fn scalar_group_mul2(_: &Self::G2, _: &Vec<Self::F>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn scalar_group_mult(_: &Self::GT, _: &Vec<Self::F>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn scalar_group_dot1(_: &Vec<Self::G1>, _: &Vec<Self::F>) -> Self::G1 {
        unimplemented!()
    }
    fn scalar_group_dot2(_: &Vec<Self::G2>, _: &Vec<Self::F>) -> Self::G2 {
        unimplemented!()
    }
    fn scalar_group_dott(_: &Vec<Self::GT>, _: &Vec<Self::F>) -> Self::GT {
        unimplemented!()
    }
    fn billinear_map(_: &Self::G1, _: &Self::G2) -> Self::GT {
        unimplemented!()
    }
    fn group_neg1(_: &mut Self::G1) {
        unimplemented!()
    }
    fn group_neg2(_: &mut Self::G2) {
        unimplemented!()
    }
    fn group_negt(_: &mut Self::GT) {
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
    fn group_hash1<H: Hasher>(_: &Self::G1, _: &mut H) {
        unimplemented!()
    }
    fn group_hash2<H: Hasher>(_: &Self::G2, _: &mut H) {
        unimplemented!()
    }
    fn group_hasht<H: Hasher>(_: &Self::GT, _: &mut H) {
        unimplemented!()
    }
    fn group_fmt1(_: &Self::G1, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
    fn group_fmt2(_: &Self::G2, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
    fn group_fmtt(_: &Self::GT, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}


/// Object representing a Zippel configuration for Short-Weierstrass curves
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct ArkSWCurve<C: SWCurveConfig> {
    _curve: PhantomData<C>,
}

impl<C: SWCurveConfig> ArkSWCurve<C> {
    /// Create a new short-weierstrass curve configuration
    pub fn new() -> Self {
        Self { _curve: PhantomData }
    }
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
    fn group_add2(_: &Self::G2, _: &mut Self::G2) {
        unimplemented!()
    }
    fn group_addt(_: &Self::GT, _: &mut Self::GT) {
        unimplemented!()
    }
    fn group_neg2(_: &mut Self::G2) {
        unimplemented!()
    }
    fn group_negt(_: &mut Self::GT) {
        unimplemented!()
    }
    fn group_mul2(_: &Self::F, _: &mut Self::G2) {
        unimplemented!()
    }
    fn group_mult(_: &Self::F, _: &mut Self::GT) {
        unimplemented!()
    }
    fn scalar_group_mul2(_: &Self::G2, _: &Vec<Self::F>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn scalar_group_mult(_: &Self::GT, _: &Vec<Self::F>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn scalar_group_dot2(_: &Vec<Self::G2>, _: &Vec<Self::F>) -> Self::G2 {
        unimplemented!()
    }
    fn scalar_group_dott(_: &Vec<Self::GT>, _: &Vec<Self::F>) -> Self::GT {
        unimplemented!()
    }
    fn billinear_map(_: &Self::G1, _: &Self::G2) -> Self::GT {
        unimplemented!()
    }
    fn group_rand2<R: Rng + ?Sized>(_: &mut R) -> Self::G2 {
        unimplemented!()
    }
    fn group_randt<R: Rng + ?Sized>(_: &mut R) -> Self::GT {
        unimplemented!()
    }
    fn group_hash2<H: Hasher>(_: &Self::G2, _: &mut H) {
        unimplemented!()
    }
    fn group_hasht<H: Hasher>(_: &Self::GT, _: &mut H) {
        unimplemented!()
    }
    #[inline]
    fn group_add1(g1: &Self::G1, g2: &mut Self::G1) {
        *g2 = (*g1 + *g2).into();
    }
    #[inline]
    fn group_neg1(g: &mut Self::G1) {
        *g = -(*g);
    }
    #[inline]
    fn group_mul1(f: &Self::F, g: &mut Self::G1) {
        *g = g.mul(f).into();
    }
    #[inline]
    fn scalar_group_mul1(g1: &Self::G1, f1: &Vec<Self::F>) -> Vec<Self::G1> {
        g1.into_group().batch_mul(&f1[..])
    }
    #[inline]
    fn scalar_group_dot1(g1: &Vec<Self::G1>, f1: &Vec<Self::F>) -> Self::G1 {
        // TODO: What does Err<usize> mean here?
        C::msm(&g1[..], &f1[..]).unwrap().into()
    }
    #[inline]
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1 {
        Self::G1::rand(rng)
    }
    #[inline]
    fn group_hash1<H: Hasher>(g: &Self::G1, h: &mut H) {
        g.hash(h)
    }

    fn group_fmt1(g: &Self::G1, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
    fn group_fmt2(_: &Self::G2, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
    fn group_fmtt(_: &Self::GT, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

/// Object representing a Zippel configuration for twisted edwards curves
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct ArkTECurve<C: TECurveConfig> {
    _curve: PhantomData<C>,
}

impl<C: TECurveConfig> ArkTECurve<C> {
    /// Create a new twisted edwards curve configuration
    pub fn new() -> Self {
        Self { _curve: PhantomData }
    }
}

impl<C: TECurveConfig> ArkConfig for ArkTECurve<C> {
    type F = C::ScalarField;
    type G1 = TEAffine<C>;
    type G2 = ();
    type GT = ();

    #[inline]
    fn group_zero1() -> Self::G1 {
        Self::G1::zero()
    }
    fn group_zero2() -> Self::G2 {
        unimplemented!()
    }
    fn group_zerot() -> Self::GT {
        unimplemented!()
    }
    fn group_add2(_: &Self::G2, _: &mut Self::G2) {
        unimplemented!()
    }
    fn group_addt(_: &Self::GT, _: &mut Self::GT) {
        unimplemented!()
    }
    fn group_neg2(_: &mut Self::G2) {
        unimplemented!()
    }
    fn group_negt(_: &mut Self::GT) {
        unimplemented!()
    }
    fn group_mul2(_: &Self::F, _: &mut Self::G2) {
        unimplemented!()
    }
    fn group_mult(_: &Self::F, _: &mut Self::GT) {
        unimplemented!()
    }
    fn scalar_group_mul2(_: &Self::G2, _: &Vec<Self::F>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn scalar_group_mult(_: &Self::GT, _: &Vec<Self::F>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn scalar_group_dot2(_: &Vec<Self::G2>, _: &Vec<Self::F>) -> Self::G2 {
        unimplemented!()
    }
    fn scalar_group_dott(_: &Vec<Self::GT>, _: &Vec<Self::F>) -> Self::GT {
        unimplemented!()
    }
    fn billinear_map(_: &Self::G1, _: &Self::G2) -> Self::GT {
        unimplemented!()
    }
    fn group_rand2<R: Rng + ?Sized>(_: &mut R) -> Self::G2 {
        unimplemented!()
    }
    fn group_randt<R: Rng + ?Sized>(_: &mut R) -> Self::GT {
        unimplemented!()
    }
    fn group_hash2<H: Hasher>(_: &Self::G2, _: &mut H) {
        unimplemented!()
    }
    fn group_hasht<H: Hasher>(_: &Self::GT, _: &mut H) {
        unimplemented!()
    }
    #[inline]
    fn group_add1(g1: &Self::G1, g2: &mut Self::G1) {
        *g2 = (*g1 + *g2).into();
    }
    #[inline]
    fn group_neg1(g: &mut Self::G1) {
        *g = -(*g);
    }
    #[inline]
    fn group_mul1(f: &Self::F, g: &mut Self::G1) {
        *g = g.mul(f).into();
    }
    #[inline]
    fn scalar_group_mul1(g1: &Self::G1, f1: &Vec<Self::F>) -> Vec<Self::G1> {
        g1.into_group().batch_mul(&f1[..])
    }
    #[inline]
    fn scalar_group_dot1(g1: &Vec<Self::G1>, f1: &Vec<Self::F>) -> Self::G1 {
        // TODO: What does Err<usize> mean here?
        C::msm(&g1[..], &f1[..]).unwrap().into()
    }
    #[inline]
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1 {
        Self::G1::rand(rng)
    }
    #[inline]
    fn group_hash1<H: Hasher>(g: &Self::G1, h: &mut H) {
        g.hash(h)
    }
    #[inline]
    fn group_fmt1(g: &Self::G1, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
    #[inline]
    fn group_fmt2(_: &Self::G2, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
    #[inline]
    fn group_fmtt(_: &Self::GT, _: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

/// Object representing a Zippel configuration for pairing friendly curves
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct ArkPairing<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> ArkPairing<P> {
    /// Create a new pairing configuration
    pub fn new() -> Self {
        Self { _pairing: PhantomData }
    }
}

/// For pairing friendly curves
impl<P: Pairing> ArkConfig for ArkPairing<P> {
    type F = P::ScalarField;
    type G1 = P::G1Affine;
    type G2 = P::G2Affine;
    type GT = PairingOutput<P>;

    #[inline]
    fn group_zero1() -> Self::G1 {
        Self::G1::zero()
    }
    #[inline]
    fn group_zero2() -> Self::G2 {
        Self::G2::zero()
    }
    #[inline]
    fn group_zerot() -> Self::GT {
        Self::GT::zero()
    }
    #[inline]
    fn group_add1(g1: &Self::G1, g2: &mut Self::G1) {
        *g2 = (*g1 + *g2).into();
    }
    #[inline]
    fn group_add2(g1: &Self::G2, g2: &mut Self::G2) {
        *g2 = (*g1 + *g2).into();
    }
    #[inline]
    fn group_addt(g1: &Self::GT, g2: &mut Self::GT) {
        *g2 = (*g1 + *g2).into();
    }
    #[inline]
    fn group_neg1(g: &mut Self::G1) {
        *g = (Self::G1::zero() - *g).into();
    }
    #[inline]
    fn group_neg2(g: &mut Self::G2) {
        *g = (Self::G2::zero() - *g).into();
    }
    #[inline]
    fn group_negt(g: &mut Self::GT) {
        *g = -(*g);
    }
    #[inline]
    fn group_mul1(f: &Self::F, g: &mut Self::G1) {
        *g = g.mul(f).into();
    }
    #[inline]
    fn group_mul2(f: &Self::F, g: &mut Self::G2) {
        *g = g.mul(f).into();
    }
    #[inline]
    fn group_mult(f: &Self::F, g: &mut Self::GT) {
        *g = g.mul(f).into();
    }
    #[inline]
    fn scalar_group_mul1(g1: &Self::G1, f1: &Vec<Self::F>) -> Vec<Self::G1> {
        P::G1::batch_mul((*g1).into(), f1)
    }
    #[inline]
    fn scalar_group_mul2(g2: &Self::G2, f2: &Vec<Self::F>) -> Vec<Self::G2> {
        P::G2::batch_mul((*g2).into(), f2)
    }
    #[inline]
    fn scalar_group_dot1(g1: &Vec<Self::G1>, f1: &Vec<Self::F>) -> Self::G1 {
        P::G1::msm(&g1[..], &f1[..]).unwrap().into()
    }
    #[inline]
    fn scalar_group_dot2(g2: &Vec<Self::G2>, f2: &Vec<Self::F>) -> Self::G2 {
        P::G2::msm(&g2[..], &f2[..]).unwrap().into()
    }
    #[inline]
    fn scalar_group_mult(gt: &Self::GT, ft: &Vec<Self::F>) -> Vec<Self::GT> {
        Self::GT::batch_mul(*gt, ft)
    }
    #[inline]
    fn scalar_group_dott(gt: &Vec<Self::GT>, ft: &Vec<Self::F>) -> Self::GT {
        Self::GT::msm(&gt[..], &ft[..]).unwrap()
    }
    #[inline]
    fn billinear_map(g1: &Self::G1, g2: &Self::G2) -> Self::GT {
        P::pairing(g1, g2)
    }
    #[inline]
    fn scalar_rand<R: Rng + ?Sized>(rng: &mut R) -> Self::F {
        Self::F::rand(rng)
    }
    #[inline]
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1 {
        Self::G1::rand(rng)
    }
    #[inline]
    fn group_rand2<R: Rng + ?Sized>(rng: &mut R) -> Self::G2 {
        Self::G2::rand(rng)
    }
    #[inline]
    fn group_randt<R: Rng + ?Sized>(rng: &mut R) -> Self::GT {
        Self::GT::rand(rng)
    }
    #[inline]
    fn scalar_hash<H: Hasher>(f: Self::F, h: &mut H) {
        f.hash(h)
    }
    #[inline]
    fn group_hash1<H: Hasher>(g: &Self::G1, h: &mut H) {
        g.hash(h)
    }
    #[inline]
    fn group_hash2<H: Hasher>(g: &Self::G2, h: &mut H) {
        g.hash(h)
    }
    #[inline]
    fn group_hasht<H: Hasher>(g: &Self::GT, h: &mut H) {
        g.hash(h)
    }
    #[inline]
    fn group_fmt1(g: &Self::G1, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
    #[inline]
    fn group_fmt2(g: &Self::G2, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
    #[inline]
    fn group_fmtt(g: &Self::GT, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "    );{}", g)
    }
}

#[derive(MontConfig, Clone, Copy, Eq, PartialEq)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
pub type F17 = Fp64<F17Config>;

#[derive(MontConfig, Clone, Copy, Eq, PartialEq)]
#[modulus = "65537"]
#[generator = "3"]
pub struct F65537Config;
pub type F65537 = Fp64<F65537Config>;

/// Zippel arkworks configurations
pub type ArkBls12_381 = ArkPairing<Bls12<ark_bls12_381::Config>>;
pub type ArkCurve25519 = ArkTECurve<ark_curve25519::Curve25519Config>;
pub type ArkBn254 = ArkPairing<Bn<ark_bn254::Config>>;
pub type ArkMNT4_298 = ArkPairing<MNT4<ark_mnt4_298::Config>>;
pub type ArkSecp256k1 = ArkSWCurve<ark_secp256k1::Config>;
pub type ArkPallas = ArkSWCurve<ark_pallas::PallasConfig>;
pub type ArkVesta = ArkSWCurve<ark_vesta::VestaConfig>;
pub type ArkEd25519 = ArkTECurve<ark_ed25519::EdwardsConfig>;
pub type ArkF17 = ArkField<F17>;
pub type ArkF65537 = ArkField<F65537>;

