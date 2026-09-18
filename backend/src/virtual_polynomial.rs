use crate::optimization::record_selected_eval_interpolation_fallback;
use crate::{PolyError, PolyVariant};
use ark_ff::{Field, PrimeField};
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use ark_serialize::{CanonicalSerialize, SerializationError};
use lang::typ::CRange;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::ops::{Add, Mul, Sub};
use std::sync::Arc;

/// Wrapper around `Arc<PolyVariant<F>>` that hashes and compares by
/// **pointer identity** instead of by content. The default derived
/// `Hash` on `PolyVariant` walks the entire `DenseMle.evaluations`
/// vector, which is O(N²) work for our R1CS matrices (a 16M-entry
/// MLE hashes 16M field elements — ~1.7s at M=12 per `from_poly` call).
/// In practice, `flattened_polys` is deduped by identity: zippel reuses
/// the same `Arc` via clone when the same poly appears in multiple
/// products, never by re-constructing identical content. So pointer
/// hashing gives the same dedupe behavior for all realistic cases at
/// near-zero cost.
struct ArcPtr<F: Field>(Arc<PolyVariant<F>>);

impl<F: Field> Clone for ArcPtr<F> {
    fn clone(&self) -> Self {
        ArcPtr(Arc::clone(&self.0))
    }
}

impl<F: Field> PartialEq for ArcPtr<F> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<F: Field> Eq for ArcPtr<F> {}

impl<F: Field> Hash for ArcPtr<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.0) as usize).hash(state);
    }
}

impl<F: Field> fmt::Debug for ArcPtr<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArcPtr({:p})", Arc::as_ptr(&self.0))
    }
}

/// Static selected-evaluation shape carried by typed graph/runtime code.
/// Runtime values can lose arity when they are constants or typed zeroes, so
/// selected eval validates against this shape instead of guessing from the
/// polynomial payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SelectedEvalShape {
    /// Arity of the polynomial the selected evaluation is applied to.
    pub input_num_vars: usize,
    /// Arity of the residual polynomial left after the non-selected variables
    /// are fixed; equals the length of the free range.
    pub output_num_vars: usize,
    /// Degree bound used to size the interpolation used when the free range
    /// is a single variable.
    pub max_degree: usize,
}

impl SelectedEvalShape {
    /// Build a selected-evaluation shape from the statically known arities and
    /// degree bound.
    pub fn new(input_num_vars: usize, output_num_vars: usize, max_degree: usize) -> Self {
        SelectedEvalShape {
            input_num_vars,
            output_num_vars,
            max_degree,
        }
    }
}

fn interpolate_univariate_from_points<F: PrimeField>(points: &[F], evals: &[F]) -> Vec<F> {
    let n = points.len();
    assert_eq!(n, evals.len(), "point/eval length mismatch");
    assert!(n > 0, "cannot interpolate empty point set");

    let mut prod = vec![F::one()];
    for &x in points {
        let mut next = vec![F::zero(); prod.len() + 1];
        for (i, &c) in prod.iter().enumerate() {
            next[i] -= c * x;
            next[i + 1] += c;
        }
        prod = next;
    }

    let mut coeffs = vec![F::zero(); n];
    for i in 0..n {
        let xi = points[i];
        let mut denom = F::one();
        for (j, &xj) in points.iter().enumerate() {
            if i != j {
                denom *= xi - xj;
            }
        }
        assert!(!denom.is_zero(), "interpolation points must be distinct");

        let qi = divide_by_x_minus_a(&prod, xi);
        let scale = evals[i] * denom.inverse().unwrap();
        for (k, qk) in qi.iter().enumerate() {
            coeffs[k] += *qk * scale;
        }
    }

    coeffs
}

fn divide_by_x_minus_a<F: PrimeField>(p: &[F], a: F) -> Vec<F> {
    assert!(p.len() >= 2, "polynomial degree must be at least 1");
    let n = p.len() - 1;
    let mut q = vec![F::zero(); n];
    q[n - 1] = p[n];
    for k in (1..n).rev() {
        q[k - 1] = p[k] + a * q[k];
    }
    q
}

fn unit_constant_with_declared_degree<F: PrimeField>(
    scalar: F,
    max_degree: usize,
) -> VirtualPolynomial<F> {
    let mut coeffs = vec![F::zero(); max_degree + 1];
    coeffs[0] = scalar;
    let mut result =
        VirtualPolynomial::from_poly(PolyVariant::DenseUni(DensePolynomial { coeffs }));
    result.num_variables = Some(1);
    result
}

fn univariate_factor_coeffs<F: PrimeField>(poly: &PolyVariant<F>) -> Option<Vec<F>> {
    match poly {
        PolyVariant::DenseMle(mle) if mle.evaluations.len() == 2 => {
            let v0 = mle.evaluations[0];
            let v1 = mle.evaluations[1];
            Some(vec![v0, v1 - v0])
        }
        PolyVariant::DenseMle(mle) if mle.evaluations.len() == 1 => Some(vec![mle.evaluations[0]]),
        PolyVariant::SparseMle { num_vars: 1, evals } => {
            let mut values = [F::zero(), F::zero()];
            for (idx, value) in evals {
                if *idx < 2 {
                    values[*idx] += *value;
                }
            }
            Some(vec![values[0], values[1] - values[0]])
        }
        PolyVariant::SparseMle { num_vars: 0, evals } => {
            let value = evals.iter().map(|(_, value)| *value).sum();
            Some(vec![value])
        }
        PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => poly.to_coeffs(),
        _ => None,
    }
}

pub(crate) fn add_coeffs_assign<F: Field>(target: &mut Vec<F>, addend: &[F]) {
    if target.len() < addend.len() {
        target.resize(addend.len(), F::zero());
    }
    for (target_coeff, addend_coeff) in target.iter_mut().zip(addend.iter()) {
        *target_coeff += *addend_coeff;
    }
}

pub(crate) fn mul_coeffs<F: Field>(left: &[F], right: &[F]) -> Vec<F> {
    if left.is_empty() || right.is_empty() {
        return vec![F::zero()];
    }
    let mut result = vec![F::zero(); left.len() + right.len() - 1];
    for (i, left_coeff) in left.iter().enumerate() {
        for (j, right_coeff) in right.iter().enumerate() {
            result[i + j] += *left_coeff * *right_coeff;
        }
    }
    trim_trailing_zero_coeffs(&mut result);
    result
}

pub(crate) fn trim_trailing_zero_coeffs<F: Field>(coeffs: &mut Vec<F>) {
    while coeffs.len() > 1 && coeffs.last().is_some_and(|coeff| coeff.is_zero()) {
        coeffs.pop();
    }
    if coeffs.is_empty() {
        coeffs.push(F::zero());
    }
}

/// Virtual Polynomial - represents a polynomial as a sum of products of base polynomials.
/// This is useful for sum-check protocols and allows flexible representation
/// of polynomial products without explicitly computing the full expansion.
///
/// Based on HyperPlonk's virtual polynomial implementation but adapted to use PolyVariant
/// instead of DenseMultilinearExtension.
///
/// A virtual polynomial is a sum of products:
/// $$ \sum_{i=0}^{n} c_i \cdot \prod_{j=0}^{m_i} P_{ij} $$
///
/// Example: f = c0 * f0 * f1 * f2 + c1 * f3 * f4
/// - products stores: [(c0, [0, 1, 2]), (c1, [3, 4])]
/// - flattened_polys stores: [f0, f1, f2, f3, f4]
#[derive(Debug, Clone)]
pub struct VirtualPolynomial<F: Field> {
    /// List of products as (coefficient, indices into flattened_polys)
    pub products: Vec<(F, Vec<usize>)>,
    /// Flattened list of all unique polynomials referenced by products
    pub flattened_polys: Vec<Arc<PolyVariant<F>>>,
    /// Lookup table mapping polynomial Arc to their indices.
    /// Hashed by Arc pointer (see `ArcPtr`) — content hashing on the
    /// DenseMle variant would walk the full 2^n-entry evaluation vector
    /// every insert/lookup, blowing up for matrix-sized MLEs.
    poly_pointers_lookup: HashMap<ArcPtr<F>, usize>,
    /// Number of variables (for multivariate polynomials)
    pub num_variables: Option<usize>,
}

impl<F: ark_ff::PrimeField> VirtualPolynomial<F> {
    /// Create a new empty virtual polynomial
    pub fn new() -> Self {
        VirtualPolynomial {
            products: Vec::new(),
            flattened_polys: Vec::new(),
            poly_pointers_lookup: HashMap::new(),
            num_variables: None,
        }
    }

    /// Create a virtual polynomial from a single polynomial with coefficient 1
    pub fn from_poly(poly: PolyVariant<F>) -> Self {
        let poly_arc = Arc::new(poly);
        let mut hm = HashMap::new();
        hm.insert(ArcPtr(Arc::clone(&poly_arc)), 0);

        VirtualPolynomial {
            products: vec![(F::one(), vec![0])],
            flattened_polys: vec![poly_arc],
            poly_pointers_lookup: hm,
            num_variables: None,
        }
    }

    /// Create a virtual polynomial from a scalar constant
    pub fn from_scalar(scalar: F) -> Self {
        if scalar.is_zero() {
            VirtualPolynomial::new()
        } else {
            VirtualPolynomial {
                products: vec![(scalar, vec![])],
                flattened_polys: vec![],
                poly_pointers_lookup: HashMap::new(),
                num_variables: None,
            }
        }
    }

    /// Create a typed zero polynomial that preserves the declared arity.
    pub fn zero_with_num_vars(num_vars: usize) -> Self {
        VirtualPolynomial {
            products: Vec::new(),
            flattened_polys: Vec::new(),
            poly_pointers_lookup: HashMap::new(),
            num_variables: Some(num_vars),
        }
    }

    /// Create a typed constant polynomial that preserves the declared arity.
    pub fn constant_with_num_vars(scalar: F, num_vars: usize) -> Self {
        if scalar.is_zero() {
            VirtualPolynomial::zero_with_num_vars(num_vars)
        } else {
            VirtualPolynomial {
                products: vec![(scalar, vec![])],
                flattened_polys: vec![],
                poly_pointers_lookup: HashMap::new(),
                num_variables: Some(num_vars),
            }
        }
    }

    /// Fix the first `points.len()` variables of every factor independently,
    /// without expanding the sum of products.
    ///
    /// This is the fast path for products of multilinear extensions: each
    /// factor is partially evaluated in parallel and the product structure is
    /// preserved, so no `MleMultiplication` normalization is ever needed. The
    /// declared arity shrinks by `points.len()`, and is dropped entirely once
    /// no products remain.
    ///
    /// # Errors
    /// Propagates [`PolyVariant::evaluate_or_fix_mle`] failures, i.e.
    /// [`PolyError::DimensionMismatch`] if `points` is longer than a factor's
    /// arity and [`PolyError::RequiresMle`] if a factor is not a multilinear
    /// encoding.
    pub fn fix_first_mle_variables_factorwise(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        if points.is_empty() {
            return Ok(self.clone());
        }

        let new_flattened: Vec<Arc<PolyVariant<F>>> = self
            .flattened_polys
            .par_iter()
            .map(|poly_arc| -> Result<Arc<PolyVariant<F>>, PolyError<F>> {
                let fixed_variant = (**poly_arc).evaluate_or_fix_mle(points)?;
                Ok(Arc::new(fixed_variant))
            })
            .collect::<Result<_, _>>()?;

        let mut new_lookup = HashMap::new();
        for (idx, poly) in new_flattened.iter().enumerate() {
            new_lookup.insert(ArcPtr(Arc::clone(poly)), idx);
        }

        let mut result = VirtualPolynomial {
            products: self.products.clone(),
            flattened_polys: new_flattened,
            poly_pointers_lookup: new_lookup,
            num_variables: self.num_variables.map(|n| n.saturating_sub(points.len())),
        };

        if result.products.is_empty() {
            result.num_variables = None;
        }

        Ok(result)
    }

    /// Conservative degree bound for the virtual sum-of-products form.
    ///
    /// This avoids normalizing products of MLE factors (which is intentionally
    /// unsupported in the fast path) while still giving selected unit-range
    /// evaluation enough interpolation points to recover the residual
    /// univariate polynomial.
    pub fn degree_bound(&self) -> usize {
        self.products
            .iter()
            .map(|(_, indices)| {
                indices
                    .iter()
                    .map(|&idx| self.flattened_polys[idx].degree())
                    .sum::<usize>()
            })
            .max()
            .unwrap_or(0)
    }

    /// Fix all variables outside a selected free range, using the static
    /// shape from type inference/lowering rather than runtime payload arity.
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if `free_range` is not a
    /// unit-step, non-empty range inside `shape.input_num_vars`, if its length
    /// disagrees with `shape.output_num_vars`, or if `fixed` does not supply
    /// one value per non-selected variable. Also propagates the errors of
    /// [`Self::normalize`] and of the underlying `PolyVariant` restriction.
    pub fn fix_variables_except_range_with_shape(
        &self,
        shape: SelectedEvalShape,
        free_range: CRange,
        fixed: &[F],
    ) -> Result<Self, PolyError<F>> {
        let free_len = free_range.len();
        if free_range.step() != 1
            || free_range.start() >= free_range.end()
            || free_range.end() > shape.input_num_vars
            || free_len == 0
            || free_len != shape.output_num_vars
            || fixed.len() != shape.input_num_vars - free_len
        {
            return Err(PolyError::DimensionMismatch {
                polynomial: PolyVariant::from_scalar(F::zero()),
                expected: shape.input_num_vars.saturating_sub(free_len),
                actual: fixed.len(),
            });
        }

        if self.is_zero() {
            if shape.output_num_vars == 1 {
                return Ok(unit_constant_with_declared_degree(
                    F::zero(),
                    shape.max_degree,
                ));
            }
            return Ok(VirtualPolynomial::zero_with_num_vars(shape.output_num_vars));
        }
        if let Some(scalar) = self.to_scalar() {
            if shape.output_num_vars == 1 {
                return Ok(unit_constant_with_declared_degree(scalar, shape.max_degree));
            }
            return Ok(VirtualPolynomial::constant_with_num_vars(
                scalar,
                shape.output_num_vars,
            ));
        }

        if shape.output_num_vars == 1 {
            return self.fix_variables_except_unit_range_by_interpolation(shape, free_range, fixed);
        }

        if self
            .flattened_polys
            .iter()
            .all(|poly| poly.is_multivariate() && poly.num_vars() == shape.input_num_vars)
        {
            let new_flattened: Vec<Arc<PolyVariant<F>>> = self
                .flattened_polys
                .par_iter()
                .map(|poly| {
                    poly.fix_variables_except_range(shape.input_num_vars, free_range.clone(), fixed)
                        .map(Arc::new)
                })
                .collect::<Result<_, _>>()?;

            let mut new_lookup = HashMap::new();
            for (idx, poly) in new_flattened.iter().enumerate() {
                new_lookup.insert(ArcPtr(Arc::clone(poly)), idx);
            }
            let mut result = VirtualPolynomial {
                products: self.products.clone(),
                flattened_polys: new_flattened,
                poly_pointers_lookup: new_lookup,
                num_variables: Some(shape.output_num_vars),
            };
            result.simplify();
            return Ok(result);
        }

        let restricted = self.normalize()?.fix_variables_except_range(
            shape.input_num_vars,
            free_range,
            fixed,
        )?;
        let mut result = VirtualPolynomial::from_poly(restricted);
        result.num_variables = Some(shape.output_num_vars);
        Ok(result)
    }

    /// Compatibility helper for tests and non-selected-eval callers. The input
    /// arity is derived from the selected-eval call shape (`fixed.len() +
    /// free_range.len()`), not from potentially untyped constant payloads.
    ///
    /// # Errors
    /// Propagates [`Self::fix_variables_except_range_with_shape`].
    pub fn fix_variables_except_range(
        &self,
        free_range: CRange,
        fixed: &[F],
    ) -> Result<Self, PolyError<F>> {
        let shape = SelectedEvalShape::new(
            fixed.len() + free_range.len(),
            free_range.len(),
            self.degree_bound(),
        );
        self.fix_variables_except_range_with_shape(shape, free_range, fixed)
    }

    fn fix_variables_except_unit_range_by_interpolation(
        &self,
        shape: SelectedEvalShape,
        free_range: CRange,
        fixed: &[F],
    ) -> Result<Self, PolyError<F>> {
        record_selected_eval_interpolation_fallback();
        let degree = shape.max_degree.max(self.degree_bound());
        let points: Vec<F> = (0..=degree).map(|i| F::from(i as u64)).collect();
        let evals: Vec<F> = points
            .par_iter()
            .map(|t| {
                let mut full_point = Vec::with_capacity(shape.input_num_vars);
                let mut fixed_idx = 0usize;
                for var_idx in 0..shape.input_num_vars {
                    if var_idx >= free_range.start() && var_idx < free_range.end() {
                        full_point.push(*t);
                    } else {
                        full_point.push(fixed[fixed_idx]);
                        fixed_idx += 1;
                    }
                }
                self.evaluate_mv(&full_point)
            })
            .collect::<Result<_, _>>()?;

        let coeffs = interpolate_univariate_from_points(&points, &evals);
        let mut result = VirtualPolynomial::from_poly(PolyVariant::DenseUni(
            DensePolynomial::from_coefficients_vec(coeffs),
        ));
        result.num_variables = Some(1);
        Ok(result)
    }

    /// Sum a batch of univariate virtual polynomials into one dense
    /// univariate polynomial without preserving the per-tail product-of-MLE
    /// representation. This is a private reduce(+) fast path for explicit
    /// sumcheck rounds after selected MLE factors have been restricted to the
    /// current unit variable.
    pub(crate) fn sum_univariate_products_dense(polys: &[Self]) -> Option<Self> {
        if polys.is_empty() {
            return None;
        }

        let mut total = vec![F::zero()];
        for poly in polys {
            let coeffs = poly.univariate_products_coeffs()?;
            add_coeffs_assign(&mut total, &coeffs);
        }
        trim_trailing_zero_coeffs(&mut total);

        let mut result = VirtualPolynomial::from_poly(PolyVariant::DenseUni(
            DensePolynomial::from_coefficients_vec(total),
        ));
        result.num_variables = Some(1);
        Some(result)
    }

    fn univariate_products_coeffs(&self) -> Option<Vec<F>> {
        if let Some(num_vars) = self.num_variables
            && num_vars != 1
        {
            return None;
        }

        let mut total = vec![F::zero()];
        for (coefficient, indices) in &self.products {
            let mut term = vec![*coefficient];
            for &idx in indices {
                let factor = univariate_factor_coeffs(self.flattened_polys[idx].as_ref())?;
                term = mul_coeffs(&term, &factor);
            }
            add_coeffs_assign(&mut total, &term);
        }
        trim_trailing_zero_coeffs(&mut total);
        Some(total)
    }

    /// Add a product of polynomials to this virtual polynomial
    /// The polynomials will be multiplied together, then multiplied by the coefficient
    ///
    /// # Errors
    /// Currently infallible — the `Result` exists so callers can stay uniform
    /// with the other mutating builders.
    pub fn add_poly_list(
        &mut self,
        poly_list: impl IntoIterator<Item = Arc<PolyVariant<F>>>,
        coefficient: F,
    ) -> Result<(), PolyError<F>> {
        let poly_list: Vec<Arc<PolyVariant<F>>> = poly_list.into_iter().collect();
        let mut indexed_product = Vec::with_capacity(poly_list.len());

        if poly_list.is_empty() && !coefficient.is_zero() {
            // This is a scalar term
            self.products.push((coefficient, vec![]));
            return Ok(());
        }

        for poly in poly_list {
            let key = ArcPtr(Arc::clone(&poly));
            if let Some(&index) = self.poly_pointers_lookup.get(&key) {
                indexed_product.push(index)
            } else {
                let curr_index = self.flattened_polys.len();
                self.flattened_polys.push(poly);
                self.poly_pointers_lookup.insert(key, curr_index);
                indexed_product.push(curr_index);
            }
        }

        self.products.push((coefficient, indexed_product));
        Ok(())
    }

    /// Multiply this virtual polynomial by another polynomial
    ///
    /// # Errors
    /// Currently infallible — the `Result` exists so callers can stay uniform
    /// with the other mutating builders.
    pub fn mul_by_poly(
        &mut self,
        poly: Arc<PolyVariant<F>>,
        coefficient: F,
    ) -> Result<(), PolyError<F>> {
        // Check if this polynomial already exists
        let key = ArcPtr(Arc::clone(&poly));
        let poly_index = match self.poly_pointers_lookup.get(&key) {
            Some(&p) => p,
            None => {
                self.poly_pointers_lookup
                    .insert(key, self.flattened_polys.len());
                self.flattened_polys.push(poly);
                self.flattened_polys.len() - 1
            }
        };

        // Multiply each product by the polynomial and coefficient
        for (prod_coef, indices) in self.products.iter_mut() {
            indices.push(poly_index);
            *prod_coef *= coefficient;
        }

        Ok(())
    }

    /// Multiply two virtual polynomials
    pub fn mul_virtual(&self, other: &Self) -> Self {
        let mut result = VirtualPolynomial::new();
        result.num_variables = self.num_variables.or(other.num_variables);

        for (coeff1, indices1) in &self.products {
            for (coeff2, indices2) in &other.products {
                let new_coeff = *coeff1 * *coeff2;

                // Collect all polynomials from both products
                let mut poly_list = Vec::new();
                for &idx in indices1 {
                    poly_list.push(self.flattened_polys[idx].clone());
                }
                for &idx in indices2 {
                    poly_list.push(other.flattened_polys[idx].clone());
                }

                result.add_poly_list(poly_list, new_coeff).ok();
            }
        }
        result
    }

    /// Add two virtual polynomials
    pub fn add_virtual(&mut self, other: &Self) {
        for (coeff, indices) in &other.products {
            let poly_list: Vec<_> = indices
                .iter()
                .map(|&idx| other.flattened_polys[idx].clone())
                .collect();

            self.add_poly_list(poly_list, *coeff).ok();
        }
    }

    /// Negate all coefficients
    pub fn neg_virtual(&mut self) {
        for (coeff, _) in &mut self.products {
            *coeff = -*coeff;
        }
    }

    /// Multiply by a scalar
    pub fn mul_scalar(&mut self, scalar: F) {
        if scalar.is_zero() {
            self.products.clear();
        } else {
            for (coeff, _) in &mut self.products {
                *coeff *= scalar;
            }
        }
    }

    /// Evaluate the virtual polynomial at a point
    ///
    /// # Panics
    /// Panics if any factor is a multivariate encoding, since a single-point
    /// univariate evaluation is then the wrong shape.
    pub fn evaluate_uv(&self, point: &F) -> F {
        self.products
            .iter()
            .map(|(coeff, indices)| {
                let prod = indices
                    .iter()
                    .map(|&idx| self.flattened_polys[idx].evaluate(&vec![*point]))
                    .fold(F::one(), |acc, val| acc * val);
                *coeff * prod
            })
            .sum()
    }

    /// Evaluate multivariate - the virtual polynomial at a multidimensional point
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if `point` disagrees with the
    /// declared arity, and propagates per-factor evaluation failures.
    pub fn evaluate_mv(&self, point: &[F]) -> Result<F, PolyError<F>> {
        if let Some(num_vars) = self.num_variables
            && point.len() != num_vars
        {
            return Err(PolyError::DimensionMismatch {
                polynomial: PolyVariant::from_scalar(F::zero()),
                expected: num_vars,
                actual: point.len(),
            });
        }

        let mut result = F::zero();
        for (coeff, indices) in &self.products {
            let mut prod = *coeff;
            for &idx in indices {
                prod *= self.flattened_polys[idx].evaluate_mv(point)?;
            }
            result += prod;
        }
        Ok(result)
    }

    /// Sum-of-products evaluation at a boolean hypercube vertex (little-endian
    /// table index). Mirrors `evaluate_mv` without constructing a field point.
    ///
    /// # Panics
    /// Panics if a factor is neither an MLE encoding nor a degree-0
    /// univariate, or if `index` is outside a factor's evaluation table.
    pub fn evaluate_at_boolean_index(&self, index: usize) -> F {
        let mut result = F::zero();
        for (coeff, indices) in &self.products {
            let mut prod = *coeff;
            for &idx in indices {
                prod *= self.flattened_polys[idx].evaluate_at_boolean_index(index);
            }
            result += prod;
        }
        result
    }

    /// Check if the virtual polynomial is zero
    pub fn is_zero(&self) -> bool {
        self.products.is_empty() || self.products.iter().all(|(coeff, _)| coeff.is_zero())
    }

    /// Simplify by removing zero terms
    pub fn simplify(&mut self) {
        self.products.retain(|(coeff, _)| !coeff.is_zero());
    }

    /// Try to convert to scalar (non-consuming)
    pub fn to_scalar(&self) -> Option<F> {
        // Check if all referenced polynomials are constants
        for poly_arc in &self.flattened_polys {
            poly_arc.to_scalar()?;
        }

        // All polynomials are constants, so we can evaluate the sum of products
        let mut result = F::zero();
        for (coeff, indices) in &self.products {
            let mut term = *coeff;
            for &idx in indices {
                // We know this is a constant, so extract it
                {
                    let scalar = self.flattened_polys[idx].to_scalar()?;
                    term *= scalar;
                }
            }
            result += term;
        }
        Some(result)
    }

    /// Try to convert to vector (non-consuming)
    pub fn to_vec(&self) -> Option<Vec<F>> {
        // Only if this is a single polynomial reference with coefficient 1
        if self.products.len() == 1 {
            let (coeff, indices) = &self.products[0];
            if indices.len() == 1 && *coeff == F::one() {
                return self.flattened_polys[indices[0]].to_vec();
            }
        }
        None
    }

    /// Convert virtual polynomial into a scalar constant if it is constant, otherwise return None
    /// A virtual polynomial is constant if all polynomials it references are constants
    pub fn into_scalar(self) -> Option<F> {
        // Check if all referenced polynomials are constants
        for poly_arc in &self.flattened_polys {
            poly_arc.as_ref().clone().into_scalar()?;
        }

        // All polynomials are constants, so we can evaluate the sum of products
        let mut result = F::zero();
        for (coeff, indices) in &self.products {
            let mut term = *coeff;
            for &idx in indices {
                // We know this is a constant, so extract it
                {
                    let scalar = self.flattened_polys[idx].as_ref().clone().into_scalar()?;
                    term *= scalar;
                }
            }
            result += term;
        }
        Some(result)
    }

    /// Add a scalar to the polynomial
    pub fn poly_add_scalar(&self, scalar: F) -> Self {
        let mut result = self.clone();
        result.add_poly_list(vec![], scalar).ok();
        result
    }

    /// Add two polynomials
    ///
    /// # Errors
    /// Currently infallible: addition merges the two sums of products without
    /// normalizing, so no shape violation can arise.
    pub fn poly_add(&self, other: &Self) -> Result<Self, PolyError<F>> {
        let mut result = self.clone();
        result.add_virtual(other);
        Ok(result)
    }

    /// Subtract a scalar from the polynomial
    pub fn poly_sub_scalar(&self, scalar: F) -> Self {
        self.poly_add_scalar(-scalar)
    }

    /// Subtract two polynomials
    ///
    /// # Errors
    /// Currently infallible: subtraction negates and merges the sums of
    /// products without normalizing.
    pub fn poly_sub(&self, other: &Self) -> Result<Self, PolyError<F>> {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        let mut result = self.clone();
        result.add_virtual(&other_neg);
        Ok(result)
    }

    /// Multiply by a scalar
    pub fn poly_mul_scalar(&self, scalar: F) -> Self {
        let mut result = self.clone();
        result.mul_scalar(scalar);
        result
    }

    /// Multiply two polynomials
    ///
    /// # Errors
    /// Currently infallible: multiplication distributes the two sums of
    /// products and never normalizes.
    pub fn poly_mul(&self, other: &Self) -> Result<Self, PolyError<F>> {
        Ok(self.mul_virtual(other))
    }

    /// Subtract polynomial from scalar (scalar - poly)
    ///
    /// # Errors
    /// Propagates [`Self::poly_sub`].
    pub fn scalar_sub_poly(scalar: F, poly: &Self) -> Result<Self, PolyError<F>> {
        let scalar_vp = VirtualPolynomial::from_scalar(scalar);
        scalar_vp.poly_sub(poly)
    }

    /// Normalize the virtual polynomial to a single PolyVariant
    /// This expands the sum-of-products into a single polynomial
    ///
    /// # Errors
    /// Returns [`PolyError::MleMultiplication`] when a product contains two
    /// multilinear factors (their product is not multilinear, so the virtual
    /// form cannot be collapsed), plus any other
    /// [`PolyVariant::poly_mul`]/[`PolyVariant::poly_add`] failure such as
    /// [`PolyError::UnsupportedOperation`] between incompatible encodings.
    pub fn normalize(&self) -> Result<PolyVariant<F>, PolyError<F>> {
        if self.products.is_empty() {
            // Empty virtual polynomial = zero polynomial
            return Ok(PolyVariant::from_scalar(F::zero()));
        }

        // Start with zero polynomial
        let mut result: Option<PolyVariant<F>> = None;

        for (coeff, indices) in &self.products {
            // Compute the product of all polynomials in this term
            let mut term_result: Option<PolyVariant<F>> = None;

            for &idx in indices {
                let poly = &**self.flattened_polys.get(idx).ok_or_else(|| {
                    PolyError::UnsupportedOperation {
                        op: lang::ast::BinOp::Mul,
                        left: PolyVariant::from_scalar(F::zero()),
                        right: PolyVariant::from_scalar(F::zero()),
                    }
                })?;

                term_result = Some(match term_result {
                    None => poly.clone(),
                    Some(acc) => acc.poly_mul(poly)?,
                });
            }

            // Multiply by coefficient
            let term = match term_result {
                None => PolyVariant::from_scalar(*coeff), // Just the scalar
                Some(poly) if *coeff == F::one() => poly,
                Some(poly) => poly.poly_mul_scalar(*coeff),
            };

            // Add to accumulator
            result = Some(match result {
                None => term,
                Some(acc) => acc.poly_add(&term)?,
            });
        }

        Ok(result.unwrap_or_else(|| PolyVariant::from_scalar(F::zero())))
    }

    // Wrapper methods that delegate to normalized PolyVariant

    /// Whether the normalized polynomial is univariate.
    ///
    /// Answers from the declared arity when one is recorded, and otherwise
    /// falls back to normalizing; a normalization failure degrades to the
    /// arity reported by [`Self::num_vars`].
    pub fn is_univariate(&self) -> bool {
        if let Some(num_vars) = self.num_variables {
            return num_vars == 1;
        }
        self.normalize()
            .map(|p| p.is_univariate())
            .unwrap_or_else(|_| self.num_vars() == Some(1))
    }

    /// Whether the normalized polynomial is multilinear.
    ///
    /// A declared arity together with a degree bound of at most one is
    /// sufficient; otherwise the sum of products is normalized, and a
    /// normalization failure answers `false`.
    pub fn is_multilinear(&self) -> bool {
        if self.num_variables.is_some() && self.degree_bound() <= 1 {
            return true;
        }
        self.normalize()
            .map(|p| p.is_multilinear())
            .unwrap_or(false)
    }

    /// Declared arity, falling back to the arity of the first factor when it
    /// is multivariate. `None` means the arity is unknown (for instance a
    /// purely scalar or univariate virtual polynomial).
    pub fn num_vars(&self) -> Option<usize> {
        self.num_variables.or_else(|| {
            if let Some(poly) = self.flattened_polys.first() {
                if poly.is_multivariate() {
                    Some(poly.num_vars())
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    /// Degree of the normalized polynomial, or `0` if it cannot be normalized.
    pub fn degree(&self) -> usize {
        self.normalize().map(|p| p.degree()).unwrap_or(0)
    }

    /// Coefficients of the normalized polynomial, or `None` if it does not
    /// normalize to a univariate encoding.
    pub fn to_coeffs(&self) -> Option<Vec<F>> {
        self.normalize().ok().and_then(|p| p.to_coeffs())
    }

    /// Evaluate the normalized univariate polynomial at every point, returning
    /// the results as a virtual polynomial wrapping an MLE.
    ///
    /// # Errors
    /// Propagates [`Self::normalize`] and
    /// [`PolyVariant::try_evaluate_vec`] failures, notably
    /// [`PolyError::VectorEvaluationRequiresUnivariate`].
    pub fn try_evaluate_vec(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        // Normalize and evaluate at all points, returning errors instead of
        // silently converting normalization/evaluation failures into zero.
        let normalized = self.normalize()?;
        let evaluated = normalized.try_evaluate_vec(points)?;
        Ok(VirtualPolynomial::from_poly(evaluated))
    }

    /// Infallible wrapper around [`Self::try_evaluate_vec`].
    ///
    /// # Panics
    /// Panics if normalization fails or the normalized polynomial is not
    /// univariate; use [`Self::try_evaluate_vec`] to handle those cases.
    pub fn evaluate_vec(&self, points: &[F]) -> Self {
        self.try_evaluate_vec(points)
            .expect("VirtualPolynomial::evaluate_vec failed; use try_evaluate_vec to handle errors")
    }

    /// Evaluate or partially fix the leading variables, keeping the virtual
    /// form whenever possible.
    ///
    /// Typed zeroes and constants are answered directly from the declared
    /// arity, a product made purely of `DenseMle` factors takes the
    /// factor-wise fast path, and anything else falls back to normalizing.
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if more points are supplied
    /// than the declared arity, and otherwise propagates
    /// [`Self::normalize`] and [`PolyVariant::evaluate_or_fix_mle`].
    pub fn evaluate_or_fix_mle(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        if let Some(num_vars) = self.num_variables
            && (self.is_zero() || self.to_scalar().is_some())
        {
            if points.len() > num_vars {
                return Err(PolyError::DimensionMismatch {
                    polynomial: PolyVariant::from_scalar(F::zero()),
                    expected: num_vars,
                    actual: points.len(),
                });
            }
            let scalar = self.to_scalar().unwrap_or_else(F::zero);
            return if points.len() == num_vars {
                Ok(VirtualPolynomial::from_scalar(scalar))
            } else {
                Ok(VirtualPolynomial::constant_with_num_vars(
                    scalar,
                    num_vars - points.len(),
                ))
            };
        }

        if let Some(num_vars) = self.num_vars()
            && points.len() < num_vars
            && self
                .flattened_polys
                .iter()
                .all(|poly| matches!(&**poly, PolyVariant::DenseMle(_)))
        {
            return self.fix_first_mle_variables_factorwise(points);
        }

        let normalized = self.normalize()?;
        let result = normalized.evaluate_or_fix_mle(points)?;
        Ok(VirtualPolynomial::from_poly(result))
    }

    /// Divide two virtual polynomials by normalizing both sides first.
    ///
    /// # Errors
    /// Propagates [`Self::normalize`] on either operand, and
    /// [`PolyVariant::poly_div`] failures such as
    /// [`PolyError::DivisionByZero`] or [`PolyError::DivisionNotApplicable`].
    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError<F>>
    where
        F: ark_ff::PrimeField,
    {
        let self_norm = self.normalize()?;
        let other_norm = other.normalize()?;
        let result = self_norm.poly_div(&other_norm)?;
        Ok(VirtualPolynomial::from_poly(result))
    }

    /// Divide by a scalar by multiplying with its inverse, which keeps the
    /// sum-of-products form intact.
    ///
    /// # Errors
    /// Returns [`PolyError::DivisionByZero`] if `scalar` has no inverse.
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>>
    where
        F: ark_ff::PrimeField,
    {
        let inv = scalar.inverse().ok_or_else(|| PolyError::DivisionByZero {
            v: PolyVariant::from_scalar(scalar),
        })?;
        Ok(self.poly_mul_scalar(inv))
    }

    /// Dividing a scalar by a virtual polynomial is not supported.
    ///
    /// # Errors
    /// Always returns [`PolyError::DivisionNotApplicable`], after propagating
    /// a [`Self::normalize`] failure on `poly` if one occurs.
    pub fn scalar_div_poly(scalar: F, poly: &Self) -> Result<Self, PolyError<F>> {
        let divisor = poly.normalize()?;
        Err(PolyError::DivisionNotApplicable {
            v1: PolyVariant::from_scalar(scalar),
            v2: divisor,
        })
    }
}

impl<F: ark_ff::PrimeField> CanonicalSerialize for VirtualPolynomial<F> {
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        _compress: ark_serialize::Compress,
    ) -> Result<(), SerializationError> {
        match self.normalize() {
            Ok(normalized) => {
                0u8.serialize_compressed(&mut writer)?;
                normalized.serialize_compressed(&mut writer)
            }
            Err(_) => {
                // Sum-of-products / non-normal shapes (e.g. products from poly_mul) may not
                // collapse to a single PolyVariant; encode the explicit VP representation so
                // transcript hashing of public Poly values (e.g. sumcheck) cannot fail.
                1u8.serialize_compressed(&mut writer)?;

                match self.num_variables {
                    Some(n) => {
                        true.serialize_compressed(&mut writer)?;
                        (n as u64).serialize_compressed(&mut writer)?;
                    }
                    None => {
                        false.serialize_compressed(&mut writer)?;
                    }
                }

                (self.products.len() as u64).serialize_compressed(&mut writer)?;
                for (coeff, indices) in &self.products {
                    coeff.serialize_compressed(&mut writer)?;
                    (indices.len() as u64).serialize_compressed(&mut writer)?;
                    for &idx in indices {
                        (idx as u64).serialize_compressed(&mut writer)?;
                    }
                }

                (self.flattened_polys.len() as u64).serialize_compressed(&mut writer)?;
                for poly_arc in &self.flattened_polys {
                    match poly_arc.as_ref() {
                        PolyVariant::DenseUni(p) => {
                            0u8.serialize_compressed(&mut writer)?;
                            p.serialize_compressed(&mut writer)?;
                        }
                        PolyVariant::SparseUni(p) => {
                            1u8.serialize_compressed(&mut writer)?;
                            p.serialize_compressed(&mut writer)?;
                        }
                        PolyVariant::DenseMle(m) => {
                            2u8.serialize_compressed(&mut writer)?;
                            m.serialize_compressed(&mut writer)?;
                        }
                        PolyVariant::SparseMultivariate(p) => {
                            3u8.serialize_compressed(&mut writer)?;
                            p.serialize_compressed(&mut writer)?;
                        }
                        PolyVariant::SparseMle { num_vars, evals } => {
                            4u8.serialize_compressed(&mut writer)?;
                            (*num_vars as u64).serialize_compressed(&mut writer)?;
                            (evals.len() as u64).serialize_compressed(&mut writer)?;
                            for (idx, val) in evals {
                                (*idx as u64).serialize_compressed(&mut writer)?;
                                val.serialize_compressed(&mut writer)?;
                            }
                        }
                    }
                }

                Ok(())
            }
        }
    }

    fn serialized_size(&self, _compress: ark_serialize::Compress) -> usize {
        // This is approximate - we'd need to normalize to get exact size
        // For now, return a reasonable estimate
        std::mem::size_of::<F>() * (self.products.len() + self.flattened_polys.len())
    }
}

impl<F: ark_ff::PrimeField> Default for VirtualPolynomial<F> {
    fn default() -> Self {
        VirtualPolynomial::new()
    }
}

impl<F: ark_ff::PrimeField> Add for VirtualPolynomial<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.add_virtual(&other);
        result
    }
}

impl<F: ark_ff::PrimeField> Sub for VirtualPolynomial<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        other_neg.add_virtual(&self);
        other_neg
    }
}

impl<F: ark_ff::PrimeField> Add for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn add(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.add_virtual(other);
        result
    }
}

impl<F: ark_ff::PrimeField> Sub for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        other_neg.add_virtual(self);
        other_neg
    }
}

impl<F: ark_ff::PrimeField> Mul for VirtualPolynomial<F> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let result = self.clone();
        result.mul_virtual(&other);
        result
    }
}

impl<F: ark_ff::PrimeField> Mul for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn mul(self, other: Self) -> Self::Output {
        let result = self.clone();
        result.mul_virtual(other)
    }
}

impl<F: PrimeField> PartialEq for VirtualPolynomial<F> {
    fn eq(&self, other: &Self) -> bool {
        // Normalize both and compare the result for semantic equality
        match (self.normalize(), other.normalize()) {
            (Ok(p1), Ok(p2)) => p1 == p2,
            (Err(_), Err(_)) => {
                // Both failed to normalize — canonicalize and compare structurally.
                // Resolve indices to actual polynomials, sort factors within each
                // product, merge like terms, remove zeros, then compare.
                type CanonProduct<F> = (F, Vec<PolyVariant<F>>);

                let canonicalize = |vp: &VirtualPolynomial<F>| -> Vec<CanonProduct<F>> {
                    let mut prods: Vec<CanonProduct<F>> = vp
                        .products
                        .iter()
                        .map(|(coeff, indices)| {
                            let mut polys: Vec<PolyVariant<F>> = indices
                                .iter()
                                .map(|&idx| (*vp.flattened_polys[idx]).clone())
                                .collect();
                            polys.sort();
                            (*coeff, polys)
                        })
                        .collect();
                    // Sort by polynomial factors first so like terms are adjacent
                    prods.sort_by(|(_, p1), (_, p2)| p1.cmp(p2));
                    // Merge products with the same polynomial factors
                    let mut merged: Vec<CanonProduct<F>> = Vec::new();
                    for (coeff, polys) in prods {
                        if let Some(last) = merged.last_mut()
                            && last.1 == polys
                        {
                            last.0 += coeff;
                            continue;
                        }
                        merged.push((coeff, polys));
                    }
                    // Remove zero-coefficient products
                    merged.retain(|(c, _)| !c.is_zero());
                    merged
                };

                canonicalize(self) == canonicalize(other)
            }
            _ => false, // One normalized, one didn't
        }
    }
}

impl<F: PrimeField> Eq for VirtualPolynomial<F> {}

impl<F: ark_ff::PrimeField> PartialOrd for VirtualPolynomial<F>
where
    F: ark_ff::PrimeField,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: ark_ff::PrimeField> Ord for VirtualPolynomial<F>
where
    F: ark_ff::PrimeField,
{
    fn cmp(&self, other: &Self) -> Ordering {
        // First compare by number of products
        match self.products.len().cmp(&other.products.len()) {
            Ordering::Equal => {}
            ord => return ord,
        }

        // Then compare product by product
        for ((c1, indices1), (c2, indices2)) in self.products.iter().zip(other.products.iter()) {
            // Compare coefficients
            match c1.into_bigint().cmp(&c2.into_bigint()) {
                Ordering::Equal => {}
                ord => return ord,
            }

            // Compare number of indices
            match indices1.len().cmp(&indices2.len()) {
                Ordering::Equal => {}
                ord => return ord,
            }

            // Compare indices (polynomials)
            for (idx1, idx2) in indices1.iter().zip(indices2.iter()) {
                match idx1.cmp(idx2) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
            }
        }

        Ordering::Equal
    }
}

impl<F: ark_ff::PrimeField> fmt::Display for VirtualPolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.products.is_empty() {
            return write!(f, "0");
        }

        let mut first = true;
        for (coeff, indices) in &self.products {
            if !first {
                write!(f, " + ")?;
            }
            first = false;

            write!(f, "{:?}", coeff)?;
            if !indices.is_empty() {
                write!(f, "*")?;
                for (i, &idx) in indices.iter().enumerate() {
                    if i > 0 {
                        write!(f, "*")?;
                    }
                    if let Some(poly) = self.flattened_polys.get(idx) {
                        write!(f, "({})", poly)?;
                    } else {
                        write!(f, "(P{})", idx)?;
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArkBls12_381, ArkConfig, ArkScalarOps, Value, values::marginalize};
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, univariate::DensePolynomial};
    use ark_std::test_rng;
    use lang::ast::BinOp;

    // ========== Test Helpers ==========
    fn create_vp_from_scalar(val: u64) -> VirtualPolynomial<Fr> {
        VirtualPolynomial::from_scalar(Fr::from(val))
    }

    fn create_vp_from_poly_univariate(coeffs: Vec<u64>) -> VirtualPolynomial<Fr> {
        let coeffs_fr: Vec<Fr> = coeffs.iter().map(|&c| Fr::from(c)).collect();
        let poly = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs_fr));
        VirtualPolynomial::from_poly(poly)
    }

    fn create_vp_from_mle(evals: Vec<u64>, num_vars: usize) -> VirtualPolynomial<Fr> {
        let evals_fr: Vec<Fr> = evals.iter().map(|&e| Fr::from(e)).collect();
        let mle = PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
            num_vars, evals_fr,
        ));
        VirtualPolynomial::from_poly(mle)
    }

    fn assert_vp_eq(a: &VirtualPolynomial<Fr>, b: &VirtualPolynomial<Fr>, msg: &str) {
        // Evaluate at several random points to verify equality
        let mut rng = test_rng();
        for _ in 0..10 {
            let point = Fr::rand(&mut rng);
            let eval_a = a.evaluate_uv(&point);
            let eval_b = b.evaluate_uv(&point);
            assert_eq!(
                eval_a, eval_b,
                "{}: evaluation mismatch at point {:?}",
                msg, point
            );
        }
    }

    fn explicit_round_poly(poly: &VirtualPolynomial<Fr>, num_vars: usize) -> VirtualPolynomial<Fr> {
        let mut round_poly = VirtualPolynomial::new();
        for tail_index in 0..(1usize << (num_vars - 1)) {
            let tail: Vec<Fr> = (0..(num_vars - 1))
                .map(|j| Fr::from(((tail_index >> j) & 1) as u64))
                .collect();
            let selected = poly
                .fix_variables_except_range(CRange::singleton(0), &tail)
                .unwrap();
            round_poly.add_virtual(&selected);
        }
        round_poly
    }

    fn explicit_round_evals(
        poly: &VirtualPolynomial<Fr>,
        num_vars: usize,
        max_degree: usize,
    ) -> Vec<Fr> {
        let round_poly = explicit_round_poly(poly, num_vars);
        (0..=max_degree)
            .map(|t| round_poly.evaluate_uv(&Fr::from(t as u64)))
            .collect()
    }

    fn eval_coeffs(coeffs: &[Fr], point: Fr) -> Fr {
        coeffs
            .iter()
            .rev()
            .fold(Fr::zero(), |acc, coeff| acc * point + *coeff)
    }

    fn direct_unit_selected_coeffs(
        product: &VirtualPolynomial<Fr>,
        fixed_tail: &[Fr],
        degree: usize,
    ) -> Vec<Fr> {
        let points: Vec<Fr> = (0..=degree).map(|i| Fr::from(i as u64)).collect();
        let evals: Vec<Fr> = points
            .iter()
            .map(|t| {
                let mut point = Vec::with_capacity(1 + fixed_tail.len());
                point.push(*t);
                point.extend_from_slice(fixed_tail);
                product.evaluate_mv(&point).unwrap()
            })
            .collect();
        let mut coeffs = interpolate_univariate_from_points(&points, &evals);
        trim_trailing_zero_coeffs(&mut coeffs);
        coeffs
    }

    #[test]
    fn test_selected_unit_eval_matches_direct_evaluation_for_mle_product() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4], 2);
        let b = create_vp_from_mle(vec![5, 7, 11, 13], 2);
        let product = a.poly_mul(&b).unwrap();
        let fixed_tail = vec![Fr::from(3u64)];

        let selected = product
            .fix_variables_except_range(CRange::singleton(0), &fixed_tail)
            .unwrap();

        for t in [0u64, 1, 2, 5] {
            let point = vec![Fr::from(t), fixed_tail[0]];
            let direct = product.evaluate_mv(&point).unwrap();
            let selected_eval = selected.evaluate_uv(&Fr::from(t));
            assert_eq!(selected_eval, direct, "selected eval mismatch at t={t}");
        }
    }

    #[test]
    fn test_selected_unit_eval_of_mle_product_materializes_coefficient_univariate() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();
        let fixed_tail = vec![Fr::from(3u64), Fr::from(5u64)];

        let selected = product
            .fix_variables_except_range_with_shape(
                SelectedEvalShape::new(3, 1, 2),
                CRange::singleton(0),
                &fixed_tail,
            )
            .unwrap();

        assert_eq!(selected.num_vars(), Some(1));
        assert!(
            selected.flattened_polys.len() == 1
                && matches!(
                    selected.flattened_polys[0].as_ref(),
                    PolyVariant::DenseUni(_)
                ),
            "unit selected eval over MLE products must materialize a coefficient-compatible DenseUni"
        );
        let coeffs = selected
            .to_coeffs()
            .expect("unit selected eval must expose univariate coefficients");
        assert_eq!(
            coeffs,
            direct_unit_selected_coeffs(&product, &fixed_tail, 2)
        );

        for t in [0u64, 1, 2, 7] {
            let point = vec![Fr::from(t), fixed_tail[0], fixed_tail[1]];
            let direct = product.evaluate_mv(&point).unwrap();
            let selected_eval = selected.evaluate_uv(&Fr::from(t));
            assert_eq!(selected_eval, direct, "selected eval mismatch at t={t}");
            assert_eq!(
                eval_coeffs(&coeffs, Fr::from(t)),
                direct,
                "selected coefficients mismatch at t={t}"
            );
        }
    }

    #[test]
    fn test_coef_after_unit_selected_eval_of_mle_product_returns_coefficients() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();
        let fixed_tail = vec![Fr::from(3u64), Fr::from(5u64)];

        let coeff_value = Value::<ArkBls12_381>::Poly(product.clone())
            .value_eval_selected(
                CRange::singleton(0),
                Value::VecScalar(fixed_tail.clone()),
                SelectedEvalShape::new(3, 1, 2),
            )
            .value_coef();

        let Value::VecScalar(coeffs) = coeff_value else {
            panic!("coef after unit selected eval should return VecScalar coefficients");
        };
        assert_eq!(
            coeffs,
            direct_unit_selected_coeffs(&product, &fixed_tail, 2)
        );

        for t in [0u64, 1, 2, 7] {
            let point = vec![Fr::from(t), fixed_tail[0], fixed_tail[1]];
            let direct = product.evaluate_mv(&point).unwrap();
            assert_eq!(
                eval_coeffs(&coeffs, Fr::from(t)),
                direct,
                "coef-selected polynomial mismatch at t={t}"
            );
        }
    }

    #[test]
    fn test_fft_after_unit_selected_eval_of_mle_product_returns_evaluations() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();
        let fixed_tail = vec![Fr::from(3u64), Fr::from(5u64)];

        let selected_value = Value::<ArkBls12_381>::Poly(product.clone()).value_eval_selected(
            CRange::singleton(0),
            Value::VecScalar(fixed_tail.clone()),
            SelectedEvalShape::new(3, 1, 2),
        );

        let mut expected_fft = direct_unit_selected_coeffs(&product, &fixed_tail, 2);
        <<ArkBls12_381 as ArkConfig>::FOps as ArkScalarOps<Fr>>::vec_fft(&mut expected_fft);

        let fft_value = selected_value.value_fft();
        let Value::VecScalar(actual_fft) = fft_value else {
            panic!("fft after unit selected eval should return VecScalar evaluations");
        };
        assert_eq!(actual_fft.len(), expected_fft.len());
        assert_eq!(actual_fft, expected_fft);
    }

    #[test]
    fn test_reduce_of_boolean_selected_mle_products_collapses_to_dense_univariate() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();

        let selected_terms = (0..4usize)
            .map(|tail_index| {
                let tail: Vec<Fr> = (0..2)
                    .map(|j| Fr::from(((tail_index >> j) & 1) as u64))
                    .collect();
                Value::<ArkBls12_381>::Poly(
                    product
                        .fix_variables_except_range(CRange::singleton(0), &tail)
                        .unwrap(),
                )
            })
            .collect::<Vec<_>>();

        let reduced = Value::<ArkBls12_381>::Vec(selected_terms).value_reduce(BinOp::Add);
        let Value::Poly(round_poly) = reduced else {
            panic!("expected reduced polynomial");
        };

        assert_eq!(round_poly.num_vars(), Some(1));
        assert!(
            round_poly.flattened_polys.len() == 1
                && matches!(
                    round_poly.flattened_polys[0].as_ref(),
                    PolyVariant::DenseUni(_)
                ),
            "sum of selected MLE-product tails should materialize a compact DenseUni round polynomial"
        );

        let expected = explicit_round_evals(&product, 3, 2);
        let actual = (0..=2)
            .map(|t| round_poly.evaluate_uv(&Fr::from(t as u64)))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_prefix_eval_fixes_mle_product_factorwise() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();
        let r0 = Fr::from(5u64);
        let residual = product.evaluate_or_fix_mle(&[r0]).unwrap();

        for (x1, x2) in [(0u64, 0u64), (1, 0), (0, 1), (3, 4)] {
            let direct = product
                .evaluate_mv(&[r0, Fr::from(x1), Fr::from(x2)])
                .unwrap();
            let residual_eval = residual.evaluate_mv(&[Fr::from(x1), Fr::from(x2)]).unwrap();
            assert_eq!(
                residual_eval, direct,
                "prefix residual mismatch at ({x1}, {x2})"
            );
        }
    }

    #[test]
    fn test_prefix_eval_leaves_product_univariate_when_one_variable_remains() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();
        let r0 = Fr::from(5u64);
        let r1 = Fr::from(7u64);
        let residual = product.evaluate_or_fix_mle(&[r0, r1]).unwrap();
        assert!(residual.is_univariate());

        for t in [0u64, 1, 6] {
            let direct = product.evaluate_mv(&[r0, r1, Fr::from(t)]).unwrap();
            let residual_eval = residual.evaluate_uv(&Fr::from(t));
            assert_eq!(residual_eval, direct, "univariate residual mismatch at {t}");
        }
    }

    #[test]
    fn test_repeated_prefix_eval_matches_direct_for_deep_mle_product() {
        let base = create_vp_from_mle((1..=256).collect(), 8);
        let mut product = base.clone();
        for _ in 1..6 {
            product = product.poly_mul(&base).unwrap();
        }

        let prefix: Vec<Fr> = (2u64..=7).map(Fr::from).collect();
        let mut residual = product.clone();
        for r in &prefix {
            residual = residual.evaluate_or_fix_mle(&[*r]).unwrap();
        }

        for (x6, x7) in [(0u64, 0u64), (1, 0), (0, 1), (3, 5)] {
            let mut full_point = prefix.clone();
            full_point.push(Fr::from(x6));
            full_point.push(Fr::from(x7));
            let direct = product.evaluate_mv(&full_point).unwrap();
            let residual_eval = residual.evaluate_mv(&[Fr::from(x6), Fr::from(x7)]).unwrap();
            assert_eq!(
                residual_eval, direct,
                "deep repeated prefix residual mismatch at ({x6}, {x7})"
            );
        }
    }

    #[test]
    fn test_deep_explicit_final_round_consistency() {
        let base = create_vp_from_mle((1..=256).collect(), 8);
        let mut product = base.clone();
        for _ in 1..6 {
            product = product.poly_mul(&base).unwrap();
        }

        let mut rng = test_rng();
        let prefix: Vec<Fr> = (0..6).map(|_| Fr::rand(&mut rng)).collect();
        let mut curr_poly = product.clone();
        for r in &prefix {
            curr_poly = curr_poly.evaluate_or_fix_mle(&[*r]).unwrap();
        }

        let round_poly = explicit_round_poly(&curr_poly, 2);
        let final_challenge = Fr::rand(&mut rng);
        let prev_eval = round_poly.evaluate_uv(&final_challenge);
        let final_poly = curr_poly.evaluate_or_fix_mle(&[final_challenge]).unwrap();
        let ev0 = final_poly.evaluate_uv(&Fr::from(0u64));
        let ev1 = final_poly.evaluate_uv(&Fr::from(1u64));
        assert_eq!(prev_eval, ev0 + ev1);
    }

    #[test]
    fn test_explicit_round_eval_matches_marginalize_reference_for_small_product() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
        let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
        let product = a.poly_mul(&b).unwrap();
        let max_degree = 2;

        let explicit_round0 = explicit_round_evals(&product, 3, max_degree);
        let (legacy_round0, _) = marginalize::<ArkBls12_381>(&product, 3, max_degree, 0, None);
        assert_eq!(explicit_round0, legacy_round0);

        let r1 = Fr::from(5u64);
        let residual = product.evaluate_or_fix_mle(&[r1]).unwrap();
        let explicit_round1 = explicit_round_evals(&residual, 2, max_degree);
        let (legacy_round1, legacy_residual) =
            marginalize::<ArkBls12_381>(&product, 3, max_degree, 1, Some(r1));
        assert_eq!(explicit_round1, legacy_round1);

        for (x1, x2) in [(0u64, 0u64), (1, 0), (0, 1), (3, 4)] {
            assert_eq!(
                residual.evaluate_mv(&[Fr::from(x1), Fr::from(x2)]).unwrap(),
                legacy_residual
                    .evaluate_mv(&[Fr::from(x1), Fr::from(x2)])
                    .unwrap()
            );
        }
    }

    #[test]
    fn test_explicit_round_eval_matches_marginalize_reference_for_degree10_product() {
        let num_vars = 8;
        let max_degree = 10;
        let mut rng = test_rng();
        let evals: Vec<Fr> = (0..(1usize << num_vars))
            .map(|_| Fr::rand(&mut rng))
            .collect();
        let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
            DenseMultilinearExtension::from_evaluations_vec(num_vars, evals),
        ));
        let mut product = base.clone();
        for _ in 1..max_degree {
            product = product.poly_mul(&base).unwrap();
        }

        let explicit_round0 = explicit_round_evals(&product, num_vars, max_degree);
        let reduced_terms = (0..(1usize << (num_vars - 1)))
            .map(|tail_index| {
                let tail: Vec<Fr> = (0..(num_vars - 1))
                    .map(|j| Fr::from(((tail_index >> j) & 1) as u64))
                    .collect();
                Value::<ArkBls12_381>::Poly(
                    product
                        .fix_variables_except_range(CRange::singleton(0), &tail)
                        .unwrap(),
                )
            })
            .collect::<Vec<_>>();
        let reduced_round0 =
            match Value::<ArkBls12_381>::Vec(reduced_terms).value_reduce(BinOp::Add) {
                Value::Poly(poly) => (0..=max_degree)
                    .map(|t| poly.evaluate_uv(&Fr::from(t as u64)))
                    .collect::<Vec<_>>(),
                other => panic!("expected reduced polynomial, got {other}"),
            };
        assert_eq!(explicit_round0, reduced_round0);
        let (legacy_round0, _) =
            marginalize::<ArkBls12_381>(&product, num_vars, max_degree, 0, None);
        assert_eq!(explicit_round0, legacy_round0);

        let r1 = Fr::from(5u64);
        let residual = product.evaluate_or_fix_mle(&[r1]).unwrap();
        let explicit_round1 = explicit_round_evals(&residual, num_vars - 1, max_degree);
        let (legacy_round1, _) =
            marginalize::<ArkBls12_381>(&product, num_vars, max_degree, 1, Some(r1));
        assert_eq!(explicit_round1, legacy_round1);
    }

    #[test]
    fn test_explicit_sumcheck_round_chain_consistency_degree6_num_vars8() {
        let num_vars = 8;
        let max_degree = 6;
        let mut rng = test_rng();
        let evals: Vec<Fr> = (0..(1usize << num_vars))
            .map(|_| Fr::rand(&mut rng))
            .collect();
        let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
            DenseMultilinearExtension::from_evaluations_vec(num_vars, evals),
        ));
        let mut curr_poly = base.clone();
        for _ in 1..max_degree {
            curr_poly = curr_poly.poly_mul(&base).unwrap();
        }

        let mut prev_eval: Option<Fr> = None;
        let mut current_vars = num_vars;
        for round in 0..num_vars {
            let evs = if current_vars == 1 {
                (0..=max_degree)
                    .map(|t| curr_poly.evaluate_uv(&Fr::from(t as u64)))
                    .collect::<Vec<_>>()
            } else {
                explicit_round_evals(&curr_poly, current_vars, max_degree)
            };
            if let Some(prev) = prev_eval {
                assert_eq!(
                    prev,
                    evs[0] + evs[1],
                    "sumcheck consistency failed at round {round}"
                );
            }
            let g = crate::values::round_univariate_from_marginalize_evals::<Fr>(&evs);
            let challenge = Fr::from((round + 5) as u64);
            prev_eval = Some(g.evaluate_uv(&challenge));
            if current_vars > 1 {
                curr_poly = curr_poly.evaluate_or_fix_mle(&[challenge]).unwrap();
                current_vars -= 1;
            }
        }
    }

    #[test]
    fn test_selected_wide_eval_matches_direct_evaluation_for_dense_mle() {
        let p = create_vp_from_mle((1u64..=16).collect(), 4);
        let fixed = vec![Fr::from(5u64), Fr::from(7u64)]; // variables 0 and 3
        let selected = p
            .fix_variables_except_range_with_shape(
                SelectedEvalShape::new(4, 2, 1),
                CRange::from_raw(1, 1, 3),
                &fixed,
            )
            .unwrap();

        assert_eq!(selected.num_vars(), Some(2));
        for (x1, x2) in [(0u64, 0u64), (1, 0), (0, 1), (2, 3)] {
            let direct = p
                .evaluate_mv(&[fixed[0], Fr::from(x1), Fr::from(x2), fixed[1]])
                .unwrap();
            let selected_eval = selected.evaluate_mv(&[Fr::from(x1), Fr::from(x2)]).unwrap();
            assert_eq!(
                selected_eval, direct,
                "wide selected eval mismatch at ({x1}, {x2})"
            );
        }
    }

    #[test]
    fn test_selected_eval_typed_zero_preserves_output_arity() {
        let zero = VirtualPolynomial::<Fr>::zero_with_num_vars(3);
        let selected = zero
            .fix_variables_except_range_with_shape(
                SelectedEvalShape::new(3, 1, 5),
                CRange::singleton(0),
                &[Fr::from(2u64), Fr::from(3u64)],
            )
            .unwrap();

        assert_eq!(selected.num_vars(), Some(1));
        assert_eq!(selected.evaluate_uv(&Fr::from(11u64)), Fr::from(0u64));
        assert_eq!(selected.to_coeffs().unwrap().len(), 6);
    }

    #[test]
    fn selected_eval_unit_zero_preserves_declared_degree_slots() {
        let degree = 7usize;
        let zero = VirtualPolynomial::<Fr>::zero_with_num_vars(3);
        let selected_value = Value::<ArkBls12_381>::Poly(zero).value_eval_selected(
            CRange::singleton(0),
            Value::VecScalar(vec![Fr::from(2u64), Fr::from(3u64)]),
            SelectedEvalShape::new(3, 1, degree),
        );

        let Value::VecScalar(coeffs) = selected_value.value_coef() else {
            panic!("coef after unit selected zero should return VecScalar");
        };
        assert_eq!(coeffs.len(), degree + 1);
        assert!(coeffs.iter().all(|c| c.is_zero()));

        let Value::VecScalar(evals) = selected_value.value_fft() else {
            panic!("fft after unit selected zero should return VecScalar");
        };
        assert_eq!(evals.len(), degree + 1);
        assert!(evals.iter().all(|v| v.is_zero()));
    }

    #[test]
    fn selected_eval_unit_constant_preserves_declared_degree_slots() {
        let degree = 7usize;
        let scalar = Fr::from(9u64);
        let constant = VirtualPolynomial::<Fr>::constant_with_num_vars(scalar, 3);
        let selected_value = Value::<ArkBls12_381>::Poly(constant).value_eval_selected(
            CRange::singleton(0),
            Value::VecScalar(vec![Fr::from(2u64), Fr::from(3u64)]),
            SelectedEvalShape::new(3, 1, degree),
        );

        let Value::VecScalar(coeffs) = selected_value.value_coef() else {
            panic!("coef after unit selected constant should return VecScalar");
        };
        assert_eq!(coeffs.len(), degree + 1);
        assert_eq!(coeffs[0], scalar);
        assert!(coeffs[1..].iter().all(|c| c.is_zero()));

        let Value::VecScalar(evals) = selected_value.value_fft() else {
            panic!("fft after unit selected constant should return VecScalar");
        };
        assert_eq!(evals.len(), degree + 1);
        assert!(evals.iter().all(|v| *v == scalar));
    }

    #[test]
    fn test_selected_eval_typed_constant_wide_range_preserves_output_arity() {
        let constant = VirtualPolynomial::<Fr>::constant_with_num_vars(Fr::from(9u64), 4);
        let selected = constant
            .fix_variables_except_range_with_shape(
                SelectedEvalShape::new(4, 2, 7),
                CRange::from_raw(1, 1, 3),
                &[Fr::from(2u64), Fr::from(5u64)],
            )
            .unwrap();

        assert_eq!(selected.num_vars(), Some(2));
        assert_eq!(
            selected
                .evaluate_mv(&[Fr::from(7u64), Fr::from(11u64)])
                .unwrap(),
            Fr::from(9u64)
        );
    }

    // ========== Ring Axiom Tests: Addition ==========

    #[test]
    fn test_addition_associativity() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]); // 1 + 2x + 3x^2
        let b = create_vp_from_poly_univariate(vec![4, 5]); // 4 + 5x
        let c = create_vp_from_scalar(7);

        let left = a.poly_add(&b.poly_add(&c).unwrap()).unwrap();
        let right = a.poly_add(&b).unwrap().poly_add(&c).unwrap();

        assert_vp_eq(&left, &right, "Addition associativity: (a+b)+c = a+(b+c)");
    }

    #[test]
    fn test_addition_commutativity() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let b = create_vp_from_poly_univariate(vec![4, 5]);

        let left = a.poly_add(&b).unwrap();
        let right = b.poly_add(&a).unwrap();

        assert_vp_eq(&left, &right, "Addition commutativity: a+b = b+a");
    }

    #[test]
    fn test_addition_identity() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let zero = VirtualPolynomial::new(); // Zero polynomial

        let result = a.poly_add(&zero).unwrap();

        assert_vp_eq(&result, &a, "Addition identity: a+0 = a");
    }

    #[test]
    fn test_addition_inverse() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let zero = VirtualPolynomial::new();

        let mut neg_a = a.clone();
        neg_a.neg_virtual();
        let result = a.poly_add(&neg_a).unwrap();

        assert_vp_eq(&result, &zero, "Addition inverse: a+(-a) = 0");
    }

    #[test]
    fn test_scalar_addition() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let scalar = Fr::from(5u64);

        let result = a.poly_add_scalar(scalar);
        let expected = create_vp_from_poly_univariate(vec![6, 2, 3]); // (1+5) + 2x + 3x^2

        assert_vp_eq(&result, &expected, "Scalar addition");
    }

    // ========== Ring Axiom Tests: Multiplication ==========

    #[test]
    fn test_multiplication_associativity() {
        let a = create_vp_from_poly_univariate(vec![1, 2]); // 1 + 2x
        let b = create_vp_from_poly_univariate(vec![3, 4]); // 3 + 4x
        let c = create_vp_from_scalar(5);

        let left = a.poly_mul(&b.poly_mul(&c).unwrap()).unwrap();
        let right = a.poly_mul(&b).unwrap().poly_mul(&c).unwrap();

        assert_vp_eq(
            &left,
            &right,
            "Multiplication associativity: (a*b)*c = a*(b*c)",
        );
    }

    #[test]
    fn test_multiplication_identity() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let one = create_vp_from_scalar(1);

        let result = a.poly_mul(&one).unwrap();

        assert_vp_eq(&result, &a, "Multiplication identity: a*1 = a");
    }

    #[test]
    fn test_multiplication_zero() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let zero = VirtualPolynomial::new();

        let result = a.poly_mul(&zero).unwrap();

        assert_vp_eq(&result, &zero, "Multiplication by zero: a*0 = 0");
    }

    #[test]
    fn test_scalar_multiplication() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let scalar = Fr::from(5u64);

        let result = a.poly_mul_scalar(scalar);
        let expected = create_vp_from_poly_univariate(vec![5, 10, 15]);

        assert_vp_eq(&result, &expected, "Scalar multiplication");
    }

    // ========== Ring Axiom Tests: Distributivity ==========

    #[test]
    fn test_left_distributivity() {
        let a = create_vp_from_poly_univariate(vec![1, 2]);
        let b = create_vp_from_poly_univariate(vec![3, 4]);
        let c = create_vp_from_scalar(5);

        // a * (b + c)
        let left = a.poly_mul(&b.poly_add(&c).unwrap()).unwrap();

        // a*b + a*c
        let right = a
            .poly_mul(&b)
            .unwrap()
            .poly_add(&a.poly_mul(&c).unwrap())
            .unwrap();

        assert_vp_eq(&left, &right, "Left distributivity: a*(b+c) = a*b + a*c");
    }

    #[test]
    fn test_right_distributivity() {
        let a = create_vp_from_poly_univariate(vec![1, 2]);
        let b = create_vp_from_poly_univariate(vec![3, 4]);
        let c = create_vp_from_scalar(5);

        // (a + b) * c
        let left = a.poly_add(&b).unwrap().poly_mul(&c).unwrap();

        // a*c + b*c
        let right = a
            .poly_mul(&c)
            .unwrap()
            .poly_add(&b.poly_mul(&c).unwrap())
            .unwrap();

        assert_vp_eq(&left, &right, "Right distributivity: (a+b)*c = a*c + b*c");
    }

    // ========== Subtraction Tests ==========

    #[test]
    fn test_subtraction_as_inverse() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
        let b = create_vp_from_poly_univariate(vec![4, 5]);

        let sub_result = a.poly_sub(&b).unwrap();

        let mut neg_b = b.clone();
        neg_b.neg_virtual();
        let add_neg_result = a.poly_add(&neg_b).unwrap();

        assert_vp_eq(
            &sub_result,
            &add_neg_result,
            "Subtraction as inverse: a-b = a+(-b)",
        );
    }

    #[test]
    fn test_scalar_subtraction() {
        let a = create_vp_from_poly_univariate(vec![10, 2, 3]);
        let scalar = Fr::from(5u64);

        let result = a.poly_sub_scalar(scalar);
        let expected = create_vp_from_poly_univariate(vec![5, 2, 3]); // (10-5) + 2x + 3x^2

        assert_vp_eq(&result, &expected, "Scalar subtraction");
    }

    // ========== Division Refusal Tests ==========

    #[test]
    fn test_scalar_div_poly_refuses_nonconstant_divisor_without_subtracting() {
        let scalar = Fr::from(10u64);
        let poly = create_vp_from_poly_univariate(vec![3, 2]); // 3 + 2x

        let err = VirtualPolynomial::scalar_div_poly(scalar, &poly).unwrap_err();

        match err {
            PolyError::DivisionNotApplicable { v1, v2 } => {
                assert_eq!(v1, PolyVariant::from_scalar(scalar));
                assert_eq!(v2, poly.normalize().unwrap());
            }
            other => panic!("expected DivisionNotApplicable, got {other:?}"),
        }
    }

    #[test]
    fn test_scalar_div_poly_refuses_constant_polynomial_divisor() {
        let scalar = Fr::from(10u64);
        let constant_poly = create_vp_from_poly_univariate(vec![2]);

        let err = VirtualPolynomial::scalar_div_poly(scalar, &constant_poly).unwrap_err();

        assert!(
            matches!(err, PolyError::DivisionNotApplicable { .. }),
            "scalar / constant-polynomial should mirror source typing and be refused, got {err:?}"
        );
    }

    // ========== Checked Vector Evaluation Tests ==========

    #[test]
    fn test_try_evaluate_vec_happy_path() {
        let poly = create_vp_from_poly_univariate(vec![1, 2]); // 1 + 2x
        let points = vec![Fr::from(0u64), Fr::from(3u64)];

        let evaluated = poly.try_evaluate_vec(&points).unwrap();

        assert_eq!(
            evaluated.to_vec().unwrap(),
            vec![Fr::from(1u64), Fr::from(7u64)]
        );
    }

    #[test]
    fn test_try_evaluate_vec_normalization_failure_returns_error() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4], 2);
        let b = create_vp_from_mle(vec![5, 6, 7, 8], 2);
        let product = a.poly_mul(&b).unwrap();

        let err = product
            .try_evaluate_vec(&[Fr::from(0u64), Fr::from(1u64)])
            .unwrap_err();

        assert!(
            matches!(err, PolyError::MleMultiplication { .. }),
            "normalization failure should be returned, not converted to zero; got {err:?}"
        );
    }

    #[test]
    fn test_poly_variant_try_evaluate_vec_rejects_non_univariate_without_panic() {
        let mle = PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
            1,
            vec![Fr::from(1u64), Fr::from(2u64)],
        ));

        let err = mle.try_evaluate_vec(&[Fr::from(0u64)]).unwrap_err();

        assert!(
            matches!(err, PolyError::VectorEvaluationRequiresUnivariate { .. }),
            "non-univariate vector evaluation should return a typed error, got {err:?}"
        );
    }

    // ========== Virtual Polynomial Specific Tests ==========

    #[test]
    fn test_product_representation() {
        // Create a virtual polynomial as a product: (1 + 2x) * (3 + 4x)
        let poly1 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(1u64),
            Fr::from(2u64),
        ]));
        let poly2 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(3u64),
            Fr::from(4u64),
        ]));

        let mut vp = VirtualPolynomial::new();
        vp.add_poly_list(vec![Arc::new(poly1), Arc::new(poly2)], Fr::one())
            .unwrap();

        // Expected: 3 + 10x + 8x^2
        let expected = create_vp_from_poly_univariate(vec![3, 10, 8]);

        assert_vp_eq(&vp, &expected, "Product representation");
    }

    #[test]
    fn test_normalize_simple() {
        let a = create_vp_from_poly_univariate(vec![1, 2, 3]);

        // Normalize should give back the same polynomial
        let normalized = a.normalize().unwrap();
        let expected = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
        ]));

        assert_eq!(normalized, expected, "Normalize simple polynomial");
    }

    #[test]
    fn test_normalize_product() {
        // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
        let poly1 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(1u64),
            Fr::from(2u64),
        ]));
        let poly2 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(3u64),
            Fr::from(4u64),
        ]));

        let mut vp = VirtualPolynomial::new();
        vp.add_poly_list(vec![Arc::new(poly1), Arc::new(poly2)], Fr::one())
            .unwrap();

        let normalized = vp.normalize().unwrap();

        // Check the result evaluates correctly
        let point = Fr::from(5u64);
        let eval = normalized.evaluate(&vec![point]);

        // (1 + 2*5) * (3 + 4*5) = 11 * 23 = 253
        assert_eq!(eval, Fr::from(253u64), "Normalize product evaluation");
    }

    #[test]
    fn test_mul_by_poly() {
        let poly1 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(1u64),
            Fr::from(2u64),
        ]));
        let poly2 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![
            Fr::from(3u64),
            Fr::from(4u64),
        ]));

        let mut vp = VirtualPolynomial::from_poly(poly1);
        vp.mul_by_poly(Arc::new(poly2), Fr::from(2u64)).unwrap();

        // Should be 2 * (1 + 2x) * (3 + 4x) = 2 * (3 + 10x + 8x^2) = 6 + 20x + 16x^2
        let expected = create_vp_from_poly_univariate(vec![6, 20, 16]);

        assert_vp_eq(&vp, &expected, "mul_by_poly");
    }

    // ========== MLE Tests ==========

    #[test]
    fn test_mle_addition() {
        let a = create_vp_from_mle(vec![1, 2, 3, 4], 2); // 2-var MLE
        let b = create_vp_from_mle(vec![5, 6, 7, 8], 2);

        let result = a.poly_add(&b).unwrap();
        let expected = create_vp_from_mle(vec![6, 8, 10, 12], 2);

        // Compare by evaluating at random points
        let mut rng = test_rng();
        for _ in 0..10 {
            let point = vec![Fr::rand(&mut rng), Fr::rand(&mut rng)];
            let eval_result = result.evaluate_mv(&point).unwrap();
            let eval_expected = expected.evaluate_mv(&point).unwrap();
            assert_eq!(eval_result, eval_expected, "MLE addition mismatch");
        }
    }

    #[test]
    fn test_zero_polynomial() {
        let zero = VirtualPolynomial::<Fr>::new();

        assert!(zero.is_zero(), "Zero polynomial should report is_zero");

        let point = Fr::from(42u64);
        assert_eq!(
            zero.evaluate_uv(&point),
            Fr::zero(),
            "Zero polynomial evaluates to zero"
        );
    }

    #[test]
    fn test_simplify() {
        let mut vp = VirtualPolynomial::new();

        // Add terms with zero coefficients
        vp.products.push((Fr::zero(), vec![]));
        vp.products.push((Fr::from(5u64), vec![]));
        vp.products.push((Fr::zero(), vec![]));

        vp.simplify();

        assert_eq!(
            vp.products.len(),
            1,
            "Simplify should remove zero coefficients"
        );
        assert_eq!(
            vp.products[0].0,
            Fr::from(5u64),
            "Simplify should keep non-zero coefficients"
        );
    }
}
