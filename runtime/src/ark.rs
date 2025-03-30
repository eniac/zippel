use rand::Rng;
use std::hash::Hash;
use std::fmt;
use std::marker::PhantomData;
use core::hash::Hasher;
use rayon::prelude::*;

use ark_poly::{DenseMVPolynomial, DenseUVPolynomial, MultilinearExtension, Polynomial};
use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;
use ark_ff::{AdditiveGroup, Field, One, UniformRand, Zero};
use ark_ff::{Fp64, MontBackend, MontConfig, FftField};
use ark_ec::scalar_mul::{BatchMulPreprocessing, ScalarMul};
use ark_ec::{VariableBaseMSM, AffineRepr};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::models::short_weierstrass::{Affine as SWAffine, SWCurveConfig};
use ark_ec::models::twisted_edwards::{Affine as TEAffine, TECurveConfig};

/// Represents a type instantiation of a zippel program in Arkworks
pub trait ArkConfig  {
    type F: FftField;
    type G1;
    type G2;
    type GT;

    /// Field constants
    fn scalar_zero() -> Self::F {
        Self::F::zero()
    }
    fn scalar_one() -> Self::F {
        Self::F::one()
    }
    /// Scalar addition, saves result in f2
    fn scalar_add(f1: &Self::F, f2: &mut Self::F) {
        *f2 += f1
    }
    /// Scalar subtraction, saves result in f2
    fn scalar_sub(f1: &Self::F, f2: &mut Self::F) {
        f2.neg_in_place();
        *f2 += f1
    }
    /// Scalar multiplication, saves result in f2
    fn scalar_mul(f1: &Self::F, f2: &mut Self::F) {
        *f2 *= f1
    }
    /// Scalar division, saves result in f2
    fn scalar_div(f1: &Self::F, f2: &mut Self::F) {
        f2.inverse_in_place();
        *f2 *= f1
    }
    /// Scalar exponentiation, saves result in f1
    fn scalar_pow(f1: &mut Self::F, i: u64) {
        let mut i = i;
        while (i % 2) == 0 {
            f1.square_in_place();
            i /= 2;
        }
        *f1 = f1.pow(&[i])
    }
    /// Random and hashing
    fn scalar_rand<R: Rng + ?Sized>(rng: &mut R) -> Self::F {
        Self::F::rand(rng)
    }
    fn scalar_hash<H: Hasher>(f: Self::F, h: &mut H) {
        f.hash(h)
    }
    /// Vector (pairwise) addition, saves result in f2
    fn scalar_vec_add(f1: &Vec<Self::F>, f2: &mut Vec<Self::F>) {
        f2.par_iter_mut().zip(f1.par_iter()).for_each(|(a, b)| *a += b);
    }
    /// Vector (pairwise subtraction), saves result in f2
    fn scalar_vec_sub(f1: &Vec<Self::F>, f2: &mut Vec<Self::F>) {
        f2.par_iter_mut().zip(f1.par_iter()).for_each(|(a, b)| *a -= b);
    }
    /// Scalar-vector multiplication, saves result in f2
    fn scalar_vec_mul(f1: &Self::F, f2: &mut Vec<Self::F>) {
        f2.par_iter_mut().for_each(|a| *a *= f1);
    }
    /// Hadamard product of two vectors, saves result in f2
    fn scalar_vec_prod(f1: &Vec<Self::F>, f2: &mut Vec<Self::F>) {
        f2.par_iter_mut().zip(f1.par_iter()).for_each(|(a, b)| *a *= b);
    }
    /// Inner (dot) product of two vectors
    fn scalar_vec_dot(f1: &Vec<Self::F>, f2: &Vec<Self::F>) -> Self::F {
        f1.par_iter().zip(f2.par_iter()).map(|(a, b)| *a * *b).sum()
    }
    /// Vector division by batch inversion, saves result in f2
    fn scalar_vec_div(f1: &Vec<Self::F>, f2: &mut Vec<Self::F>) {
        ark_ff::fields::batch_inversion::<Self::F>(f2);
        f2.par_iter_mut().zip(f1.par_iter()).for_each(|(a, b)| *a *= b);
    }
    /// Convert a scalar to a univariate polynomial of degree 0
    fn into_uni(a: Self::F) -> Uni<Self::F> {
        Uni::from_coefficients_vec(vec![a])
    }
    /// Construct a univariate polynomial from its coefficients
    fn uni_coeffs(a: Vec<Self::F>) -> Uni<Self::F> {
        Uni::from_coefficients_vec(a)
    }
    /// Add univariate polynomials, saves result in b
    fn uni_add(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        *b += a;
    }
    /// Subtract univariate polynomials, saves result in b
    fn uni_sub(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        b.par_iter_mut().for_each(|x| { x.neg_in_place(); });
        *b += a;
    }
    /// Multiply univariate polynomials, saves result in b
    fn uni_mul(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        // TODO: In place O(nlogn) multiplication for polynomials?
        *b = b.clone() * a;
    }
    /// Divide univariate polynomials, saves result in b
    fn uni_div(a: &Uni<Self::F>, b: &mut Uni<Self::F>) {
        // TODO: In place O(nlogn) division for polynomials?
        *b = a / b.clone();
    }
    /// Evaluate univariate polynomial at a point
    fn uni_eval(a: Uni<Self::F>, b: Self::F) -> Self::F {
        a.evaluate(&b)
    }
    /// Random univariate polynomial, of degree n
    fn uni_rand<R: Rng>(rng: &mut R, n: usize) -> Uni<Self::F> {
        <Uni<Self::F> as DenseUVPolynomial<Self::F>>::rand(n, rng)
    }
    /// Interpolate a vector of y-coefficients to a univariate polynomial
    fn uni_interpolate(a: Vec<Self::F>) -> Uni<Self::F> {
        let domain: GeneralEvaluationDomain<Self::F> = GeneralEvaluationDomain::new(a.len()).unwrap();
        let mut a = a;
        domain.ifft_in_place(&mut a);
        Self::uni_coeffs(a)
    }
    fn scalar_uni_add(a: Self::F, b: &mut Uni<Self::F>) {
        Self::uni_add(&Self::into_uni(a), b);
    }
    fn scalar_uni_sub(a: Self::F, b: &mut Uni<Self::F>) {
        Self::uni_sub(&Self::into_uni(a), b);
    }

    /// Convert a scalar to a multilinear extension with 0 variables
    fn into_mle(a: Self::F) -> Mle<Self::F> {
        Mle::from_evaluations_vec(0, vec![a])
    }
    /// Add multilinear extensions, saves result in b
    fn mle_add(a: &Mle<Self::F>, b: &mut Mle<Self::F>) {
        *b += a;
    }
    /// Subtract multilinear extensions, saves result in b
    fn mle_sub(a: &Mle<Self::F>, b: &mut Mle<Self::F>) {
        b.iter_mut().par_bridge().for_each(|x| { x.neg_in_place(); });
        *b += a;
    }
    /// Multiply multilinear extension by scalar, saves result in b
    fn mle_mul(a: &Self::F, b: &mut Mle<Self::F>) {
        *b *= a
    }
    /// Divide multilinear extension by scalar, saves result in b
    fn mle_eval(a: Mle<Self::F>, b: Vec<Self::F>) -> Self::F {
        a.evaluate(&b)
    }
    /// Random multilinear extension, of degree n
    fn mle_rand<R: Rng>(rng: &mut R, num_vars: usize) -> Mle<Self::F> {
        <Mle<Self::F> as MultilinearExtension<Self::F>>::rand(num_vars, rng)
    }
    /// Evaluate multilinear extension at a point
    fn mle_evals(num_vars: usize, a: Vec<Self::F>) -> Mle<Self::F> {
        Mle::from_evaluations_vec(num_vars, a)
    }
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
    fn group_add1(g1: Self::G1, g2: Self::G1) -> Self::G1;
    fn group_add2(g1: Self::G2, g2: Self::G2) -> Self::G2;
    fn group_addt(g1: Self::GT, g2: Self::GT) -> Self::GT;
    fn group_sub1(g1: Self::G1, g2: Self::G1) -> Self::G1;
    fn group_sub2(g1: Self::G2, g2: Self::G2) -> Self::G2;
    fn group_subt(g1: Self::GT, g2: Self::GT) -> Self::GT;
    fn billinear_map(g1: Self::G1, g2: Self::G2) -> Self::GT;
    fn group_rand1<R: Rng + ?Sized>(rng: &mut R) -> Self::G1;
    fn group_rand2<R: Rng + ?Sized>(rng: &mut R) -> Self::G2;
    fn group_randt<R: Rng + ?Sized>(rng: &mut R) -> Self::GT;
    fn group_hash1<H: Hasher>(g: Self::G1, h: &mut H);
    fn group_hash2<H: Hasher>(g: Self::G2, h: &mut H);
    fn group_hasht<H: Hasher>(g: Self::GT, h: &mut H);

    /// Group vec operations
    fn group_vec_add1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1>;
    fn group_vec_add2(g1: Vec<Self::G2>, g2: Vec<Self::G2>) -> Vec<Self::G2>;
    fn group_vec_addt(g1: Vec<Self::GT>, g2: Vec<Self::GT>) -> Vec<Self::GT>;
    fn group_vec_sub1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1>;
    fn group_vec_sub2(g1: Vec<Self::G2>, g2: Vec<Self::G2>) -> Vec<Self::G2>;
    fn group_vec_subt(g1: Vec<Self::GT>, g2: Vec<Self::GT>) -> Vec<Self::GT>;
    fn scalar_group_mul1(g: Self::G1, f: Vec<Self::F>) -> Vec<Self::G1>;
    fn scalar_group_mul2(g: Self::G2, f: Vec<Self::F>) -> Vec<Self::G2>;
    fn scalar_group_mult(g: Self::GT, f: Vec<Self::F>) -> Vec<Self::GT>;
    fn scalar_group_dot1(g: Vec<Self::G1>, f: Vec<Self::F>) -> Self::G1;
    fn scalar_group_dot2(g: Vec<Self::G2>, f: Vec<Self::F>) -> Self::G2;
    fn scalar_group_dott(g: Vec<Self::GT>, f: Vec<Self::F>) -> Self::GT;
    fn billinear_vec_map(g1: Vec<Self::G1>, g2: Vec<Self::G2>) -> Vec<Self::GT>;

    /// Group printing
    fn group_fmt1(g: &Self::G1, f: &mut fmt::Formatter) -> fmt::Result;
    fn group_fmt2(g: &Self::G2, f: &mut fmt::Formatter) -> fmt::Result;
    fn group_fmtt(g: &Self::GT, f: &mut fmt::Formatter) -> fmt::Result;
}

/// Object representing a Zippel configuration for fields
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
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
    fn group_vec_add1(_: Vec<Self::G1>, _: Vec<Self::G1>) -> Vec<Self::G1> {
        unimplemented!()
    }
    fn group_vec_add2(_: Vec<Self::G2>, _: Vec<Self::G2>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn group_vec_addt(_: Vec<Self::GT>, _: Vec<Self::GT>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn group_vec_sub1(_: Vec<Self::G1>, _: Vec<Self::G1>) -> Vec<Self::G1> {
        unimplemented!()
    }
    fn group_vec_sub2(_: Vec<Self::G2>, _: Vec<Self::G2>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn group_vec_subt(_: Vec<Self::GT>, _: Vec<Self::GT>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn billinear_vec_map(_: Vec<Self::G1>, _: Vec<Self::G2>) -> Vec<Self::GT> {
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    fn group_vec_add1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_add1(*a, *b)).collect()
    }
    fn group_vec_sub1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_sub1(*a, *b)).collect()
    }
    fn group_vec_add2(_: Vec<Self::G2>, _: Vec<Self::G2>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn group_vec_addt(_: Vec<Self::GT>, _: Vec<Self::GT>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn group_vec_sub2(_: Vec<Self::G2>, _: Vec<Self::G2>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn group_vec_subt(_: Vec<Self::GT>, _: Vec<Self::GT>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn billinear_vec_map(_: Vec<Self::G1>, _: Vec<Self::G2>) -> Vec<Self::GT> {
        unimplemented!()
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
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
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
    fn group_vec_add1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_add1(*a, *b)).collect()
    }
    fn group_vec_sub1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_sub1(*a, *b)).collect()
    }
    fn group_vec_add2(_: Vec<Self::G2>, _: Vec<Self::G2>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn group_vec_addt(_: Vec<Self::GT>, _: Vec<Self::GT>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn group_vec_sub2(_: Vec<Self::G2>, _: Vec<Self::G2>) -> Vec<Self::G2> {
        unimplemented!()
    }
    fn group_vec_subt(_: Vec<Self::GT>, _: Vec<Self::GT>) -> Vec<Self::GT> {
        unimplemented!()
    }
    fn billinear_vec_map(_: Vec<Self::G1>, _: Vec<Self::G2>) -> Vec<Self::GT> {
        unimplemented!()
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

/// Object representing a Zippel configuration for pairing friendly curves
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
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
    fn group_vec_add1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_add1(*a, *b)).collect()
    }
    fn group_vec_sub1(g1: Vec<Self::G1>, g2: Vec<Self::G1>) -> Vec<Self::G1> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_sub1(*a, *b)).collect()
    }
    fn group_vec_add2(g1: Vec<Self::G2>, g2: Vec<Self::G2>) -> Vec<Self::G2> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_add2(*a, *b)).collect()
    }
    fn group_vec_addt(gt1: Vec<Self::GT>, gt2: Vec<Self::GT>) -> Vec<Self::GT> {
        gt1.par_iter().zip(gt2.par_iter()).map(|(a, b)| Self::group_addt(*a, *b)).collect()
    }
    fn group_vec_sub2(g1: Vec<Self::G2>, g2: Vec<Self::G2>) -> Vec<Self::G2> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::group_sub2(*a, *b)).collect()
    }
    fn group_vec_subt(gt1: Vec<Self::GT>, gt2: Vec<Self::GT>) -> Vec<Self::GT> {
        gt1.par_iter().zip(gt2.par_iter()).map(|(a, b)| Self::group_subt(*a, *b)).collect()
    }
    fn billinear_vec_map(g1: Vec<Self::G1>, g2: Vec<Self::G2>) -> Vec<Self::GT> {
        g1.par_iter().zip(g2.par_iter()).map(|(a, b)| Self::billinear_map(*a, *b)).collect()
    }
    fn group_fmt1(g: &Self::G1, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
    fn group_fmt2(g: &Self::G2, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
    }
    fn group_fmtt(g: &Self::GT, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", g)
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

