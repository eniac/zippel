//! Partial evaluation and sumcheck rounds over a [`VirtualPolynomial`]: fixing
//! variables factor by factor, and summing a product of multilinear factors over the
//! hypercube in all but one variable.

use crate::Field;
use crate::poly::variant::{DenseUni, check_free_range};
use crate::{DivisionByZero, PolyError, PolyVariant};
use lang::typ::CRange;
use rayon::prelude::*;
use std::collections::HashMap;

use super::{SelectedEvalShape, VirtualPolynomial};

/// Coefficients of the polynomial of degree below `points.len()` taking
/// `evals[i]` at `points[i]` (Lagrange form, `O(n^2)`).
///
/// # Errors
/// [`DivisionByZero`] if the points are not distinct.
///
/// # Panics
/// Panics if the points are empty or of a different count than `evals`.
pub(crate) fn interpolate_univariate_from_points<F: Field>(
    points: &[F],
    evals: &[F],
) -> Result<Vec<F>, DivisionByZero> {
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
        let denom_inv = denom.inverse().ok_or(DivisionByZero)?;

        let qi = divide_by_x_minus_a(&prod, xi);
        let scale = evals[i] * denom_inv;
        for (k, qk) in qi.iter().enumerate() {
            coeffs[k] += *qk * scale;
        }
    }

    Ok(coeffs)
}

fn divide_by_x_minus_a<F: Field>(p: &[F], a: F) -> Vec<F> {
    assert!(p.len() >= 2, "polynomial degree must be at least 1");
    let n = p.len() - 1;
    let mut q = vec![F::zero(); n];
    q[n - 1] = p[n];
    for k in (1..n).rev() {
        q[k - 1] = p[k] + a * q[k];
    }
    q
}

fn univariate_factor_coeffs<F: Field>(poly: &PolyVariant<F>) -> Option<Vec<F>> {
    match poly {
        PolyVariant::DenseMle(mle) if mle.evals().len() == 2 => {
            let v0 = mle.evals()[0];
            let v1 = mle.evals()[1];
            Some(vec![v0, v1 - v0])
        }
        PolyVariant::DenseMle(mle) if mle.evals().len() == 1 => Some(vec![mle.evals()[0]]),
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

fn add_coeffs_assign<F: Field>(target: &mut Vec<F>, addend: &[F]) {
    if target.len() < addend.len() {
        target.resize(addend.len(), F::zero());
    }
    for (target_coeff, addend_coeff) in target.iter_mut().zip(addend.iter()) {
        *target_coeff += *addend_coeff;
    }
}

/// Products whose coefficient count is at most this are multiplied out
/// schoolbook by `sum_univariate_products_dense` (sumcheck round polynomials:
/// a few degree-1 factors). Larger ones go through `sum_products_eval_form`.
const SCHOOLBOOK_PRODUCT_LEN: usize = 64;

/// One `c · Π f` term: the coefficient and each factor's coefficient vector,
/// keyed by the factor's source polynomial so shared factors are FFT'd once.
type KeyedProduct<F> = (F, Vec<(*const PolyVariant<F>, Vec<F>)>);

/// Coefficients of `Σ c · Π f` over univariate products given as coefficient
/// vectors, computed in evaluation form: every distinct factor (keyed by its
/// source polynomial) is FFT'd once over a domain large enough for the
/// biggest product, products are summed pointwise, and one inverse FFT gives
/// the coefficients. Same polynomial as multiplying out each product, in
/// O(k · n log n) instead of O(n^2) per product.
///
/// # Panics
/// Panics if the field has no FFT domain for the biggest product.
fn sum_products_eval_form<F: Field>(products: &[KeyedProduct<F>]) -> Vec<F> {
    let num_coeffs = products
        .iter()
        .map(|(_, factors)| factors.iter().map(|(_, c)| c.len() - 1).sum::<usize>() + 1)
        .max()
        .unwrap_or(1);
    let size = num_coeffs.next_power_of_two();
    let mut evals: HashMap<*const PolyVariant<F>, Vec<F>> = HashMap::new();
    let mut acc = vec![F::zero(); size];
    for (coefficient, factors) in products {
        for (key, coeffs) in factors {
            evals.entry(*key).or_insert_with(|| {
                let mut v = coeffs.clone();
                v.resize(size, F::zero());
                F::fft(&mut v);
                v
            });
        }
        let factor_evals: Vec<&[F]> = factors
            .iter()
            .map(|(key, _)| evals[key].as_slice())
            .collect();
        acc.par_iter_mut().enumerate().for_each(|(k, a)| {
            let mut t = *coefficient;
            for f in &factor_evals {
                t *= f[k];
            }
            *a += t;
        });
    }
    F::ifft(&mut acc);
    trim_trailing_zero_coeffs(&mut acc);
    acc
}

fn mul_coeffs<F: Field>(left: &[F], right: &[F]) -> Vec<F> {
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

pub(super) fn trim_trailing_zero_coeffs<F: Field>(coeffs: &mut Vec<F>) {
    while coeffs.last().is_some_and(F::is_zero) {
        coeffs.pop();
    }
    if coeffs.is_empty() {
        coeffs.push(F::zero());
    }
}

/// Tails at or above this count are summed in parallel by
/// [`VirtualPolynomial::sum_over_hypercube_except`].
const PARALLEL_TAIL_THRESHOLD: usize = 1024;

/// A multilinear factor's evaluation table, read at paired indices that differ
/// only in the selected variable's bit.
#[derive(Clone, Copy)]
enum MleTable<'a, F> {
    Dense(&'a [F]),
    /// A `SparseMle`'s entries, duplicates summed (see [`sparse_mle_map`]).
    Sparse(&'a HashMap<usize, F>),
}

/// A `SparseMle`'s entries by index, duplicates summed; `None` for other
/// encodings.
fn sparse_mle_map<F: Field>(poly: &PolyVariant<F>) -> Option<HashMap<usize, F>> {
    let PolyVariant::SparseMle { evals, .. } = poly else {
        return None;
    };
    let mut map = HashMap::with_capacity(evals.len());
    for &(i, v) in evals {
        *map.entry(i).or_insert_with(F::zero) += v;
    }
    Some(map)
}

impl<F: Field> MleTable<'_, F> {
    #[inline]
    fn pair(&self, (zero, one): (usize, usize)) -> (F, F) {
        match self {
            MleTable::Dense(evals) => (evals[zero], evals[one]),
            MleTable::Sparse(map) => {
                let at = |i| map.get(&i).copied().unwrap_or_else(F::zero);
                (at(zero), at(one))
            }
        }
    }
}

/// Adds, for each product (factor indices `products[j]`, sums at `offsets[j]..`), its value
/// at `t = 0..=k` (`k` factors) at tail pair `pair` into `acc`. Each factor is
/// `(1 - t)·f(0, b) + t·f(1, b)`, its values at successive `t` written to `vals` (stride
/// `points`) by repeated addition.
// Always inlined into the per-tail fold: left to the heuristics, this kernel was
// measured up to 50% slower after unrelated changes elsewhere in the crate.
#[inline(always)]
fn add_products_at_tail<F: Field>(
    acc: &mut [F],
    vals: &mut [F],
    tables: &[MleTable<F>],
    products: &[&[usize]],
    offsets: &[usize],
    points: usize,
    pair: (usize, usize),
) {
    for (table, vals) in tables.iter().zip(vals.chunks_exact_mut(points)) {
        let (v0, v1) = table.pair(pair);
        let step = v1 - v0;
        vals[0] = v0;
        for t in 1..points {
            vals[t] = vals[t - 1] + step;
        }
    }
    for (indices, &offset) in products.iter().zip(offsets) {
        for t in 0..=indices.len() {
            let value = match indices.split_first() {
                Some((&first, rest)) => rest
                    .iter()
                    .fold(vals[first * points + t], |v, &i| v * vals[i * points + t]),
                None => F::one(),
            };
            acc[offset + t] += value;
        }
    }
}

impl<F: Field> VirtualPolynomial<F> {
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
    /// Propagates [`PolyVariant::evaluate_or_fix`] failures, i.e.
    /// [`PolyError::DimensionMismatch`] if `points` is longer than a factor's
    /// arity and [`PolyError::RequiresMle`] if a factor is not a multilinear
    /// encoding.
    pub fn fix_first_mle_variables_factorwise(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        if points.is_empty() {
            return Ok(self.clone());
        }
        let num_variables = if self.products.is_empty() {
            None
        } else {
            self.num_variables.map(|n| n.saturating_sub(points.len()))
        };
        self.map_factors(|poly| poly.evaluate_or_fix(points), num_variables)
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
        check_free_range(shape.input_num_vars, &free_range, fixed.len())?;
        if free_range.len() != shape.output_num_vars {
            return Err(PolyError::DimensionMismatch {
                expected: shape.input_num_vars.saturating_sub(free_range.len()),
                actual: fixed.len(),
            });
        }

        let constant = if self.is_zero() {
            Some(F::zero())
        } else {
            self.to_scalar()
        };
        if let Some(scalar) = constant {
            return Ok(if shape.output_num_vars == 1 {
                Self::univariate(vec![scalar])
            } else {
                VirtualPolynomial::constant_with_num_vars(scalar, shape.output_num_vars)
            });
        }

        if shape.output_num_vars == 1 {
            return self.fix_variables_except_unit_range_by_interpolation(shape, free_range, fixed);
        }

        if self
            .flattened_polys
            .iter()
            .all(|poly| poly.is_multivariate() && poly.num_vars() == shape.input_num_vars)
        {
            let mut result = self.map_factors(
                |poly| {
                    poly.fix_variables_except_range(shape.input_num_vars, free_range.clone(), fixed)
                },
                Some(shape.output_num_vars),
            )?;
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
        let degree = shape.max_degree.max(self.degree_bound());
        let points: Vec<F> = (0..=degree).map(|i| F::from(i as u64)).collect();
        let evals: Vec<F> = points
            .par_iter()
            .map(|t| {
                let mut full_point = Vec::with_capacity(shape.input_num_vars);
                full_point.extend_from_slice(&fixed[..free_range.start()]);
                full_point.push(*t);
                full_point.extend_from_slice(&fixed[free_range.start()..]);
                self.evaluate_mv(&full_point)
            })
            .collect::<Result<_, _>>()?;

        Ok(Self::univariate(
            interpolate_univariate_from_points(&points, &evals)
                .expect("the points 0..=degree are distinct"),
        ))
    }

    /// The univariate polynomial with coefficients `coeffs`, declared as
    /// having one variable.
    pub(super) fn univariate(coeffs: Vec<F>) -> Self {
        let mut result = VirtualPolynomial::from_poly(PolyVariant::DenseUni(DenseUni::new(coeffs)));
        result.num_variables = Some(1);
        result
    }

    /// The sumcheck round polynomial over `free_variable`, summing over the
    /// Boolean assignments to all other variables, for `self` in
    /// `tail_num_vars + 1` variables; `max_degree` is the declared degree
    /// bound, raised to [`Self::degree_bound`] if that is larger.
    ///
    /// Sums of products of multilinear factors are summed directly, pair by
    /// pair of table entries; anything else is evaluated at `t = 0..=degree`
    /// and interpolated.
    ///
    /// # Panics
    /// Panics if `free_variable > tail_num_vars`, if `tail_num_vars` exceeds
    /// the `usize` bit width, or if a factor has the wrong arity.
    pub fn sum_over_hypercube_except(
        &self,
        free_variable: usize,
        tail_num_vars: usize,
        max_degree: usize,
    ) -> Self {
        assert!(free_variable <= tail_num_vars);
        let tail_count = 1usize
            .checked_shl(tail_num_vars as u32)
            .expect("hypercube tail arity exceeds usize bit width");
        let degree = max_degree.max(self.degree_bound());
        let coeffs = self
            .tail_sum_of_mle_products(free_variable, tail_num_vars, tail_count, degree)
            .unwrap_or_else(|| {
                self.tail_sum_by_interpolation(free_variable, tail_num_vars, tail_count, degree)
            });
        Self::univariate(coeffs)
    }

    /// [`Self::sum_over_hypercube_except`] when every factor is a multilinear
    /// extension in `tail_num_vars + 1` variables: each product contributes
    /// `c · Π ((1 - t)·f(0, b) + t·f(1, b))` for every tail `b`, kept to
    /// `degree + 1` coefficients. `None` for any other factor.
    pub(super) fn tail_sum_of_mle_products(
        &self,
        free_variable: usize,
        tail_num_vars: usize,
        tail_count: usize,
        degree: usize,
    ) -> Option<Vec<F>> {
        let num_vars = tail_num_vars + 1;
        if !self.factors().all(|p| {
            matches!(p, PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. })
                && p.num_vars() == num_vars
        }) {
            return None;
        }
        let sparse_maps: Vec<Option<HashMap<usize, F>>> = self
            .flattened_polys
            .par_iter()
            .map(|poly| sparse_mle_map(poly))
            .collect();
        let tables: Vec<MleTable<F>> = self
            .flattened_polys
            .iter()
            .zip(&sparse_maps)
            .map(|(poly, map)| match (poly.as_ref(), map) {
                (PolyVariant::DenseMle(mle), _) => MleTable::Dense(mle.evals()),
                (_, Some(map)) => MleTable::Sparse(map),
                _ => unreachable!("checked multilinear"),
            })
            .collect();
        // A product of `k` factors has degree `k` in `t`: sum it over the tails at
        // `t = 0..=k`, then interpolate once. All products share one pass over the tails.
        let products: Vec<&[usize]> = self.products.iter().map(|(_, ix)| ix.as_slice()).collect();
        let offsets: Vec<usize> = products
            .iter()
            .scan(0, |next, ix| {
                let offset = *next;
                *next += ix.len() + 1;
                Some(offset)
            })
            .collect();
        let sums_len = offsets
            .last()
            .map_or(0, |o| o + products[products.len() - 1].len() + 1);
        let points = products.iter().map(|ix| ix.len()).max().unwrap_or(0) + 1;
        let free_bit = 1usize << free_variable;
        let low_mask = free_bit - 1;
        let add_tail = |(mut acc, mut vals): (Vec<F>, Vec<F>), tail: usize| {
            let base = (tail & low_mask) | ((tail & !low_mask) << 1);
            add_products_at_tail(
                &mut acc,
                &mut vals,
                &tables,
                &products,
                &offsets,
                points,
                (base, base | free_bit),
            );
            (acc, vals)
        };
        let zeros = || {
            (
                vec![F::zero(); sums_len],
                vec![F::zero(); tables.len() * points],
            )
        };
        let sums = if tail_count < PARALLEL_TAIL_THRESHOLD {
            (0..tail_count).fold(zeros(), add_tail).0
        } else {
            (0..tail_count)
                .into_par_iter()
                .fold(zeros, add_tail)
                .map(|(acc, _)| acc)
                .reduce(
                    || vec![F::zero(); sums_len],
                    |mut a, b| {
                        add_coeffs_assign(&mut a, &b);
                        a
                    },
                )
        };
        let mut total = vec![F::zero(); degree + 1];
        for ((coefficient, indices), &offset) in self.products.iter().zip(&offsets) {
            let k = indices.len();
            let ts: Vec<F> = (0..=k).map(|t| F::from(t as u64)).collect();
            let mut coeffs = interpolate_univariate_from_points(&ts, &sums[offset..=offset + k])
                .expect("the points 0..=k are distinct");
            coeffs.iter_mut().for_each(|c| *c *= *coefficient);
            add_coeffs_assign(&mut total, &coeffs);
        }
        trim_trailing_zero_coeffs(&mut total);
        Some(total)
    }

    /// [`Self::sum_over_hypercube_except`] for any polynomial: evaluate the sum
    /// at `t = 0..=degree` and interpolate.
    pub(super) fn tail_sum_by_interpolation(
        &self,
        free_variable: usize,
        tail_num_vars: usize,
        tail_count: usize,
        degree: usize,
    ) -> Vec<F> {
        let points: Vec<F> = (0..=degree).map(|t| F::from(t as u64)).collect();
        let evals: Vec<F> = points
            .iter()
            .map(|&t| {
                (0..tail_count)
                    .into_par_iter()
                    .map(|tail| {
                        let mut point: Vec<F> = (0..tail_num_vars)
                            .map(|j| F::from(((tail >> j) & 1) as u64))
                            .collect();
                        point.insert(free_variable, t);
                        self.evaluate_mv(&point)
                            .expect("hypercube tail evaluation failed")
                    })
                    .sum()
            })
            .collect();
        interpolate_univariate_from_points(&points, &evals)
            .expect("the points 0..=degree are distinct")
    }

    /// Sum a batch of univariate virtual polynomials into one dense
    /// univariate polynomial without preserving the per-tail product-of-MLE
    /// representation. This is a private reduce(+) fast path for explicit
    /// sumcheck rounds after selected MLE factors have been restricted to the
    /// current unit variable.
    pub(crate) fn sum_univariate_products_dense(polys: &[&Self]) -> Option<Self> {
        if polys.is_empty() {
            return None;
        }

        // Small products (sumcheck rounds: a handful of degree-1 factors) are
        // multiplied out schoolbook, term by term. Large ones (e.g. products
        // of degree-n univariates) would make that O(n^2), so they are summed
        // in evaluation form instead (see `sum_products_eval_form`).
        let mut total = vec![F::zero()];
        let mut large: Vec<KeyedProduct<F>> = Vec::new();
        for poly in polys {
            if let Some(num_vars) = poly.num_variables
                && num_vars != 1
            {
                return None;
            }
            for (coefficient, indices) in &poly.products {
                let factors = indices
                    .iter()
                    .map(|&idx| {
                        let p = poly.flattened_polys[idx].as_ref();
                        univariate_factor_coeffs(p).map(|c| (std::ptr::from_ref(p), c))
                    })
                    .collect::<Option<Vec<_>>>()?;
                if factors.iter().any(|(_, coeffs)| coeffs.is_empty()) {
                    continue;
                }
                let product_len = factors.iter().map(|(_, c)| c.len() - 1).sum::<usize>() + 1;
                // A field without an FFT domain this large multiplies schoolbook.
                if factors.len() >= 2
                    && product_len > SCHOOLBOOK_PRODUCT_LEN
                    && product_len.next_power_of_two().trailing_zeros() <= F::TWO_ADICITY
                {
                    large.push((*coefficient, factors));
                } else {
                    let mut term = vec![*coefficient];
                    for (_, factor) in &factors {
                        term = mul_coeffs(&term, factor);
                    }
                    add_coeffs_assign(&mut total, &term);
                }
            }
        }
        if !large.is_empty() {
            add_coeffs_assign(&mut total, &sum_products_eval_form(&large));
        }
        trim_trailing_zero_coeffs(&mut total);

        Some(Self::univariate(total))
    }

    /// Evaluate or partially fix the leading variables, keeping the virtual
    /// form whenever possible.
    ///
    /// Typed zeroes and constants are answered directly from the declared
    /// arity, a product made purely of MLE factors (`DenseMle` or `SparseMle`)
    /// takes the factor-wise fast path, and anything else falls back to
    /// normalizing.
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if more points are supplied
    /// than the declared arity, and otherwise propagates
    /// [`Self::normalize`] and [`PolyVariant::evaluate_or_fix`].
    pub fn evaluate_or_fix(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        if let Some(num_vars) = self.num_variables {
            let constant = if self.is_zero() {
                Some(F::zero())
            } else {
                self.to_scalar()
            };
            if let Some(scalar) = constant {
                return match num_vars.checked_sub(points.len()) {
                    None => Err(PolyError::DimensionMismatch {
                        expected: num_vars,
                        actual: points.len(),
                    }),
                    Some(0) => Ok(VirtualPolynomial::from_scalar(scalar)),
                    Some(rest) => Ok(VirtualPolynomial::constant_with_num_vars(scalar, rest)),
                };
            }
        }

        if let Some(num_vars) = self.num_vars()
            && points.len() < num_vars
            && self.flattened_polys.iter().all(|poly| {
                matches!(
                    &**poly,
                    PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. }
                )
            })
        {
            return self.fix_first_mle_variables_factorwise(points);
        }

        let result = self.normalize()?.evaluate_or_fix(points)?;
        Ok(VirtualPolynomial::from_poly(result))
    }
}
