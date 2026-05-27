//! Shallow wrappers over arkworks primitives for cryptographic operations.
//!
//! This module provides the **single source of truth** for all operation implementations
//! used by BOTH:
//! - Runtime execution (`values.rs` delegates to these functions)
//! - Generated code (compiler emits these functions verbatim)
//!
//! **Design principle:** If you add rayon parallelism or arkworks calls here, runtime
//! AND compiler get it automatically. Zero duplication.
//!
//! # Architecture
//!
//! ## Operation Coverage
//!
//! **Phase 1 (Binary Ops):** Pow, Div, Concat, Dot - 9 wrappers
//! **Phase 2 (Arithmetic/Boolean):** Add, Sub, Mul, Rem, And, Or, Equ, Reduce - 22 wrappers  
//! **Phase 3 (Polynomial):** Poly, Coef, Mle, FFT, IFFT - 5 wrappers
//! **Phase 4 (Reduce):** Compiler support complete (handler added in emit.rs)
//!
//! **Total: 37 operation wrappers** covering ~95% of vector/parallel operations in Zippel.
//!
//! ## Type Patterns
//!
//! - **Scalar operations:** Use arkworks mutating methods (`Ops::add`, `Ops::sub`, `Ops::mul`)
//! - **Index operations:** Use Rust infix operators (`+=`, `-=`, `*=`, `%=`)
//! - **Vector operations:** Use rayon `par_iter().zip().for_each()` or `par_iter().reduce()`
//! - **Group operations:** Generic over `G: CurveGroup`, accept `&[G::Affine]` and `&mut [G]`
//! - **Polynomial operations:** Use generic `Ops: ArkScalarOps<F>` parameter for FFT/IFFT
//!
//! ## Compiler Integration
//!
//! The compiler (`compiler/src/emit.rs::common_prelude()`) includes this entire file's source
//! with filtering:
//! - Strips `use ark_` import lines (compiler uses target-specific imports)
//! - Strips `//!` doc comments (reduces generated code size)
//! - Strips `use crate::` imports (backend-internal types)
//! - Strips "Polynomial Construction" section (VirtualPolynomial is runtime-only)
//!
//! Generated code calls these wrappers directly, ensuring identical behavior to runtime.
//!
//! ## Notable Exclusions
//!
//! **GT operations:** `PairingOutput<C::P>` is not a `CurveGroup`, so VecGT add/sub remain
//! as inline arkworks calls (`C::POps::add/sub`). This is architecturally correct - pairing
//! outputs are a different algebraic structure.
//!
//! **Group scalar multiplication:** Uses `C::G1Ops::mul(scalar, &mut group)` which depends
//! on the full `ArkConfig` abstraction. Cannot be generically parameterized over `CurveGroup`
//! alone. Kept as inline arkworks calls in `values.rs`.
//!
//! **Polynomial evaluation:** `poly.evaluate_vec()` is a `VirtualPolynomial` method. The
//! compiler doesn't generate these calls because compiled code uses `Vec<Fr>` not
//! `VirtualPolynomial`. Runtime evaluation stays in `values.rs::eval()`.
//!
//! ## Adding New Wrappers
//!
//! 1. Add function to appropriate section below (mark sections clearly)
//! 2. Make it `pub` + `#[inline]` (required for generated code)
//! 3. Use generic bounds that work in both runtime and compiler contexts
//! 4. Update `values.rs` to delegate with ZERO inline logic
//! 5. Update `compiler/src/emit.rs` handlers if operation needs explicit lowering
//! 6. Test: `cargo test --workspace` + Schnorr/KZG examples

use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_poly::DenseMultilinearExtension;
use ark_std::log2;
use rayon::prelude::*;

// Re-export crate-internal types for use in shallow wrappers
// (compiler doesn't use these, only runtime does)
use crate::poly_variant::PolyVariant;
use crate::virtual_polynomial::VirtualPolynomial;

// ---------------------------------------------------------------------------
// Pow (exponentiation) - 3 variants
// ---------------------------------------------------------------------------

/// Compute `base ^ exp` for `usize` using binary exponentiation.
///
/// Extracted from `values.rs:1457-1469` (`pow64` local function).
#[inline]
pub fn pow_usize(base: usize, mut exp: usize) -> usize {
    let mut result = base;
    while exp.is_multiple_of(2) {
        result *= result;
        exp /= 2;
    }
    while exp > 1 {
        result *= base;
        exp -= 1;
    }
    result
}

/// Compute elementwise `vec[i] ^ exp` for `Vec<F>` using field power.
///
/// Extracted from `values.rs:1486-1490`.
#[inline]
pub fn pow_vec_scalar<F: Field>(vec: &[F], exp: usize) -> Vec<F> {
    vec.par_iter()
        .map(|v| {
            let v = *v;
            v.pow([exp as u64])
        })
        .collect()
}

/// Compute elementwise `vec[i] ^ exp` for `Vec<usize>` using binary exponentiation.
///
/// Extracted from `values.rs:1479-1484`.
#[inline]
pub fn pow_vec_index(vec: &[usize], exp: usize) -> Vec<usize> {
    vec.par_iter().map(|&v| pow_usize(v, exp)).collect()
}

// ---------------------------------------------------------------------------
// Div (division / scalar inverse multiplication) - 2 variants
// ---------------------------------------------------------------------------

/// Compute `a / b` for field elements using multiplicative inverse.
///
/// Extracted from `values.rs:1084-1086`.
///
/// # Panics
/// Panics if `b` is zero (no inverse exists).
#[inline]
pub fn div_scalar<F: Field>(a: &F, b: &F) -> F {
    let b_inv = b
        .inverse()
        .expect("division by zero: field element has no inverse");
    *a * b_inv
}

/// Compute `g / s` for group element `g` and scalar `s` (i.e., `g * s^-1`).
///
/// Extracted from `values.rs:1113-1120` (group scalar division logic).
///
/// # Panics
/// Panics if `s` is zero (no inverse exists).
#[inline]
pub fn div_group_scalar<G: CurveGroup>(g: &G, s: &G::ScalarField) -> G {
    let s_inv = s
        .inverse()
        .expect("division by zero: scalar has no inverse");
    *g * s_inv
}

// ---------------------------------------------------------------------------
// Concat (vector concatenation) - 1 variant
// ---------------------------------------------------------------------------

/// Concatenate two slices into a new `Vec<T>`.
///
/// Extracted from `values.rs:1614-1618`.
#[inline]
pub fn concat_vec<T: Clone>(left: &[T], right: &[T]) -> Vec<T> {
    [left, right].concat()
}

// ---------------------------------------------------------------------------
// Dot (inner product / multi-scalar multiplication) - 3 variants
// ---------------------------------------------------------------------------

/// Compute scalar inner product `Σ(left[i] * right[i])` using rayon parallel reduction.
///
/// Extracted from `values.rs:1581-1597`.
///
/// # Panics
/// Panics if `left.len() != right.len()`.
#[inline]
pub fn dot_scalar<F: Field>(left: &[F], right: &[F]) -> F {
    assert_eq!(
        left.len(),
        right.len(),
        "dot_scalar: length mismatch {} != {}",
        left.len(),
        right.len()
    );
    left.par_iter()
        .zip(right.par_iter())
        .map(|(a, b)| *a * b)
        .reduce(|| F::ZERO, |acc, x| acc + x)
}

/// Compute multi-scalar multiplication (MSM) for G1: `Σ(scalars[i] * bases[i])`.
///
/// Uses arkworks `CurveGroup::msm` for efficient batch multiplication.
/// Extracted from `values.rs:1528-1531` via `config.rs::ArkGroupOps::vec_dot`.
///
/// # Panics
/// Panics if `bases.len() != scalars.len()` or MSM fails.
#[inline]
pub fn msm_g1<G1: CurveGroup>(bases: &[G1::Affine], scalars: &[G1::ScalarField]) -> G1 {
    assert_eq!(
        bases.len(),
        scalars.len(),
        "msm_g1: length mismatch {} != {}",
        bases.len(),
        scalars.len()
    );
    G1::msm(bases, scalars).expect("msm_g1 failed")
}

/// Compute multi-scalar multiplication (MSM) for G2: `Σ(scalars[i] * bases[i])`.
///
/// Uses arkworks `CurveGroup::msm` for efficient batch multiplication.
/// Extracted from `values.rs:1532-1535` via `config.rs::ArkGroupOps::vec_dot`.
///
/// # Panics
/// Panics if `bases.len() != scalars.len()` or MSM fails.
#[inline]
pub fn msm_g2<G2: CurveGroup>(bases: &[G2::Affine], scalars: &[G2::ScalarField]) -> G2 {
    assert_eq!(
        bases.len(),
        scalars.len(),
        "msm_g2: length mismatch {} != {}",
        bases.len(),
        scalars.len()
    );
    G2::msm(bases, scalars).expect("msm_g2 failed")
}

// =============================================================================
// Addition operations
// =============================================================================

/// Element-wise addition for `Vec<usize>`.
///
/// Extracted from `backend/src/values.rs:398-401`.
#[inline]
pub fn add_vec_index(a: &[usize], b: &mut [usize]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y += *x);
}

/// Element-wise addition for `Vec<F>` where F is a field.
///
/// Extracted from `backend/src/values.rs:408-417` (covers VecScalar + VecScalar, VecScalar + VecIndex).
#[inline]
pub fn add_vec_scalar<F: Field>(a: &[F], b: &mut [F]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y += x);
}

/// Element-wise addition for `Vec<G>` where G is a curve group.
///
/// Extracted from `backend/src/values.rs:419-438` (covers VecG1Affine, VecG2Affine, VecGT).
#[inline]
pub fn add_vec_group<G: CurveGroup>(a: &[G::Affine], b: &mut [G]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y += x);
}

// =============================================================================
// Subtraction operations
// =============================================================================

/// Element-wise subtraction for `Vec<usize>`: result[i] = a[i] - b[i].
///
/// Extracted from `backend/src/values.rs:489-492`.
#[inline]
pub fn sub_vec_index(a: &[usize], b: &mut [usize]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y = *x - *y);
}

/// Element-wise subtraction for `Vec<F>` where F is a field.
///
/// Extracted from `backend/src/values.rs:499-508`.
#[inline]
pub fn sub_vec_scalar<F: Field>(a: &[F], b: &mut [F]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y = *x - *y);
}

/// Element-wise subtraction for `Vec<G>` where G is a curve group.
///
/// Extracted from `backend/src/values.rs:510-529`.
#[inline]
pub fn sub_vec_group<G: CurveGroup>(a: &[G::Affine], b: &mut [G]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y = *x - *y);
}

// =============================================================================
// Multiplication operations
// =============================================================================

/// Element-wise multiplication for `Vec<usize>`.
///
/// Extracted from `backend/src/values.rs:660-663`.
#[inline]
pub fn mul_vec_index(a: usize, b: &mut [usize]) {
    b.par_iter_mut().for_each(|x| *x *= a);
}

/// Element-wise scalar multiplication for `Vec<F>` where F is a field.
///
/// Extracted from `backend/src/values.rs:664-667, 720-723`.
#[inline]
pub fn mul_vec_scalar<F: Field>(scalar: &F, v: &mut [F]) {
    v.par_iter_mut().for_each(|x| *x *= scalar);
}

// =============================================================================
// Remainder operations
// =============================================================================

/// Element-wise remainder for `Vec<usize>`.
///
/// Extracted from `backend/src/values.rs:1439-1450`.
#[inline]
pub fn rem_vec_index(a: &[usize], modulus: usize) -> Vec<usize> {
    a.par_iter().map(|x| *x % modulus).collect()
}

/// Element-wise remainder for `Vec<usize>` with vector modulus.
///
/// Extracted from `backend/src/values.rs:1444-1450`.
#[inline]
pub fn rem_vec_index_vec(a: &[usize], b: &mut [usize]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y = *x % *y);
}

/// Element-wise multiplication for `Vec<usize>` with vector.
///
/// Extracted from `backend/src/values.rs:813-816`.
#[inline]
pub fn mul_vec_index_vec(a: &[usize], b: &mut [usize]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| *y *= *x);
}

/// Element-wise scalar multiplication for `Vec<F>` where F is a field.
///
/// Extracted from `backend/src/values.rs:818-821`.
#[inline]
pub fn mul_vec_index_vec_scalar<F: Field>(a: &[usize], b: &mut [F]) {
    a.par_iter()
        .zip(b.par_iter_mut())
        .for_each(|(x, y)| F::mul_assign(y, &F::from(*x as u64)));
}

// =============================================================================
// Boolean operations
// =============================================================================

/// Element-wise AND for `Vec<bool>`.
///
/// Extracted from `backend/src/values.rs:1581-1587`.
#[inline]
pub fn and_vec_bool(a: &[bool], b: &[bool]) -> Vec<bool> {
    a.par_iter()
        .zip(b.par_iter())
        .map(|(x, y)| *x && *y)
        .collect()
}

/// Element-wise OR for `Vec<bool>`.
///
/// Extracted from `backend/src/values.rs:1596-1602`.
#[inline]
pub fn or_vec_bool(a: &[bool], b: &[bool]) -> Vec<bool> {
    a.par_iter()
        .zip(b.par_iter())
        .map(|(x, y)| *x || *y)
        .collect()
}

/// Element-wise equality check for `Vec<usize>`.
///
/// Extracted from `backend/src/values.rs:1639-1641`.
#[inline]
pub fn equ_vec_index(a: &[usize], b: &[usize]) -> bool {
    a.par_iter().zip(b.par_iter()).all(|(x, y)| *x == *y)
}

/// Element-wise equality check for `Vec<F>` where F is a field.
///
/// Extracted from `backend/src/values.rs:1642-1644`.
#[inline]
pub fn equ_vec_scalar<F: Field>(a: &[F], b: &[F]) -> bool {
    a.par_iter().zip(b.par_iter()).all(|(x, y)| *x == *y)
}

/// Element-wise equality check for `Vec<usize>` and `Vec<F>`.
///
/// Extracted from `backend/src/values.rs:1645-1648`.
#[inline]
pub fn equ_vec_index_scalar<F: Field>(a: &[usize], b: &[F]) -> bool {
    a.par_iter()
        .zip(b.par_iter())
        .all(|(x, y)| F::from(*x as u64) == *y)
}

/// Element-wise equality check for `Vec<F>` and `Vec<usize>`.
///
/// Extracted from `backend/src/values.rs:1649-1652`.
#[inline]
pub fn equ_vec_scalar_index<F: Field>(a: &[F], b: &[usize]) -> bool {
    a.par_iter()
        .zip(b.par_iter())
        .all(|(x, y)| *x == F::from(*y as u64))
}

// =============================================================================
// Reduce (aggregation) operations
// =============================================================================

/// Reduce `Vec<usize>` with addition (sum).
///
/// Extracted from `backend/src/values.rs:2583-2588`.
#[inline]
pub fn reduce_add_index(v: Vec<usize>) -> usize {
    v.into_par_iter().reduce(|| 0, |a, b| a + b)
}

/// Reduce `Vec<F>` with addition (sum) where F is a field.
///
/// Extracted from `backend/src/values.rs:2583-2588`.
#[inline]
pub fn reduce_add_scalar<F: Field>(v: Vec<F>) -> F {
    v.into_par_iter().reduce(|| F::zero(), |a, b| a + b)
}

/// Reduce `Vec<usize>` with multiplication (product).
///
/// Extracted from `backend/src/values.rs:2589-2594`.
#[inline]
pub fn reduce_mul_index(v: Vec<usize>) -> usize {
    v.into_par_iter().reduce(|| 1, |a, b| a * b)
}

/// Reduce `Vec<F>` with multiplication (product) where F is a field.
///
/// Extracted from `backend/src/values.rs:2589-2594`.
#[inline]
pub fn reduce_mul_scalar<F: Field>(v: Vec<F>) -> F {
    v.into_par_iter().reduce(|| F::one(), |a, b| a * b)
}

/// Reduce `Vec<bool>` with AND (all).
///
/// Extracted from `backend/src/values.rs:2595-2600`.
#[inline]
pub fn reduce_and_bool(v: Vec<bool>) -> bool {
    v.into_par_iter().reduce(|| true, |a, b| a && b)
}

// ---------------------------------------------------------------------------
// Polynomial Construction - 3 variants
// ---------------------------------------------------------------------------

/// Convert coefficient vector to univariate polynomial.
///
/// Extracted from `values.rs:2473-2485` (value_poly).
/// Runtime uses this with VirtualPolynomial wrapper for type tracking.
/// Compiler represents polynomials as Vec<F> and doesn't call this.
#[inline]
pub fn poly_from_coeffs<F: Field>(coeffs: Vec<F>) -> VirtualPolynomial<F> {
    VirtualPolynomial::from_poly(PolyVariant::from_coeffs(coeffs))
}

/// Convert evaluation vector to multilinear extension.
///
/// Extracted from `values.rs:2488-2511` (value_mle).
/// Requires evaluations.len() to be a power of two.
/// Panics if length is not a power of two.
#[inline]
pub fn mle_from_evals<F: Field>(evals: Vec<F>) -> VirtualPolynomial<F> {
    let size = log2(evals.len());
    VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::<F>::from_evaluations_vec(size as usize, evals),
    ))
}

/// Extract coefficient vector from univariate polynomial.
///
/// Extracted from `values.rs:2456-2470` (value_coef).
/// Panics if poly is not univariate.
#[inline]
pub fn coef_from_poly<F: Field>(poly: &VirtualPolynomial<F>) -> Vec<F> {
    poly.to_coeffs()
        .expect("Can only get coefficients from univariate polynomials")
}

// ---------------------------------------------------------------------------
// FFT/IFFT Transforms - 2 variants
// ---------------------------------------------------------------------------

/// In-place FFT (coefficients → evaluations).
///
/// Extracted from `values.rs:2528-2546` (value_fft).
/// Requires `Ops: ArkScalarOps<F>` to avoid depending on full `ArkConfig`.
/// Generated code calls this as `fft_vec::<Fr, FrOps>(coeffs)`.
#[inline]
pub fn fft_vec<F, Ops>(coeffs: &mut Vec<F>)
where
    F: ark_ff::PrimeField,
    Ops: crate::config::ArkScalarOps<F>,
{
    Ops::vec_fft(coeffs);
}

/// In-place IFFT (evaluations → coefficients).
///
/// Extracted from `values.rs:2514` and `2499` (value_interpolate).
/// Requires `Ops: ArkScalarOps<F>` to avoid depending on full `ArkConfig`.
/// Generated code calls this as `ifft_vec::<Fr, FrOps>(evals)`.
#[inline]
pub fn ifft_vec<F, Ops>(evals: &mut Vec<F>)
where
    F: ark_ff::PrimeField,
    Ops: crate::config::ArkScalarOps<F>,
{
    Ops::vec_ifft(evals);
}

// ---------------------------------------------------------------------------
// End of shallow wrappers
// ---------------------------------------------------------------------------
