//! [`VirtualPolynomial`]: a polynomial kept as a sum of products of
//! [`PolyVariant`] factors, the form sumcheck rounds work on without expanding it.

use crate::Field;
use crate::{PolyError, PolyVariant};
use rayon::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Mul, Sub};
use std::sync::Arc;

/// Partial evaluation and sumcheck round sums.
mod rounds;

pub(crate) use rounds::interpolate_univariate_from_points;

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
    products: Vec<(F, Vec<usize>)>,
    /// Flattened list of all unique polynomials referenced by products
    flattened_polys: Vec<Arc<PolyVariant<F>>>,
    /// Lookup table mapping polynomial Arc to their indices.
    /// Hashed by Arc pointer (see `ArcPtr`) — content hashing on the
    /// DenseMle variant would walk the full 2^n-entry evaluation vector
    /// every insert/lookup, blowing up for matrix-sized MLEs.
    poly_pointers_lookup: HashMap<ArcPtr<F>, usize>,
    /// Number of variables (for multivariate polynomials)
    num_variables: Option<usize>,
}

impl<F: Field> VirtualPolynomial<F> {
    /// The constant `scalar` (no products when it is zero) with the given
    /// declared arity.
    fn constant(scalar: F, num_variables: Option<usize>) -> Self {
        VirtualPolynomial {
            products: if scalar.is_zero() {
                Vec::new()
            } else {
                vec![(scalar, vec![])]
            },
            flattened_polys: Vec::new(),
            poly_pointers_lookup: HashMap::new(),
            num_variables,
        }
    }

    /// Create a new empty virtual polynomial
    pub fn new() -> Self {
        Self::constant(F::zero(), None)
    }

    /// Create a virtual polynomial from a single polynomial with coefficient 1
    pub fn from_poly(poly: PolyVariant<F>) -> Self {
        let mut result = Self::new();
        result.add_poly_list([Arc::new(poly)], F::one());
        result
    }

    /// Create a virtual polynomial from a scalar constant
    pub fn from_scalar(scalar: F) -> Self {
        Self::constant(scalar, None)
    }

    /// Create a typed zero polynomial that preserves the declared arity.
    pub fn zero_with_num_vars(num_vars: usize) -> Self {
        Self::constant(F::zero(), Some(num_vars))
    }

    /// Create a typed constant polynomial that preserves the declared arity.
    pub fn constant_with_num_vars(scalar: F, num_vars: usize) -> Self {
        Self::constant(scalar, Some(num_vars))
    }

    /// Index of `poly` in `flattened_polys`, adding it if this exact `Arc` is
    /// not there yet.
    fn intern(&mut self, poly: Arc<PolyVariant<F>>) -> usize {
        let next = self.flattened_polys.len();
        let index = *self
            .poly_pointers_lookup
            .entry(ArcPtr(Arc::clone(&poly)))
            .or_insert(next);
        if index == next {
            self.flattened_polys.push(poly);
        }
        index
    }

    /// The factors referenced by some product, once per reference.
    fn factors(&self) -> impl Iterator<Item = &PolyVariant<F>> {
        self.products
            .iter()
            .flat_map(|(_, indices)| indices)
            .map(|&idx| self.flattened_polys[idx].as_ref())
    }

    /// The same products over factors replaced one-for-one by `f`.
    fn map_factors(
        &self,
        f: impl Fn(&PolyVariant<F>) -> Result<PolyVariant<F>, PolyError<F>> + Sync + Send,
        num_variables: Option<usize>,
    ) -> Result<Self, PolyError<F>> {
        let flattened_polys: Vec<Arc<PolyVariant<F>>> = self
            .flattened_polys
            .par_iter()
            .map(|poly| f(poly).map(Arc::new))
            .collect::<Result<_, _>>()?;
        let poly_pointers_lookup = flattened_polys
            .iter()
            .enumerate()
            .map(|(idx, poly)| (ArcPtr(Arc::clone(poly)), idx))
            .collect();
        Ok(VirtualPolynomial {
            products: self.products.clone(),
            flattened_polys,
            poly_pointers_lookup,
            num_variables,
        })
    }

    /// Add the product `coefficient · Π poly_list` (the constant
    /// `coefficient` when the list is empty).
    pub fn add_poly_list(
        &mut self,
        poly_list: impl IntoIterator<Item = Arc<PolyVariant<F>>>,
        coefficient: F,
    ) {
        let indices = poly_list
            .into_iter()
            .map(|poly| self.intern(poly))
            .collect();
        self.products.push((coefficient, indices));
    }

    /// Add `scale · other`, product by product.
    fn add_scaled(&mut self, other: &Self, scale: F) {
        for (coeff, indices) in &other.products {
            let factors = indices
                .iter()
                .map(|&idx| Arc::clone(&other.flattened_polys[idx]));
            self.add_poly_list(factors, *coeff * scale);
        }
    }

    /// Evaluate a univariate virtual polynomial at a point.
    ///
    /// # Panics
    /// Panics if any factor is a multivariate encoding, since a single-point
    /// univariate evaluation is then the wrong shape.
    pub fn evaluate_uv(&self, point: &F) -> F {
        let point = std::slice::from_ref(point);
        self.products
            .iter()
            .map(|(coeff, indices)| {
                indices.iter().fold(*coeff, |acc, &idx| {
                    acc * self.flattened_polys[idx].evaluate(point)
                })
            })
            .sum()
    }

    /// Whether a point of `len` coordinates evaluates this polynomial fully,
    /// that is, whether [`Self::evaluate_mv`] accepts it: the declared arity,
    /// if any, and every factor's arity are `len`.
    #[must_use]
    pub fn is_full_point(&self, len: usize) -> bool {
        self.num_variables.is_none_or(|n| n == len) && self.factors().all(|p| p.num_vars() == len)
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

    /// Check if the virtual polynomial is zero
    pub fn is_zero(&self) -> bool {
        self.products.iter().all(|(coeff, _)| coeff.is_zero())
    }

    /// Simplify by removing zero terms
    pub fn simplify(&mut self) {
        self.products.retain(|(coeff, _)| !coeff.is_zero());
    }

    /// The constant this is, when every stored polynomial is a constant.
    pub fn to_scalar(&self) -> Option<F> {
        let constants = self
            .flattened_polys
            .iter()
            .map(|poly| poly.to_scalar())
            .collect::<Option<Vec<F>>>()?;
        Some(
            self.products
                .iter()
                .map(|(coeff, indices)| {
                    indices
                        .iter()
                        .fold(*coeff, |acc, &idx| acc * constants[idx])
                })
                .sum(),
        )
    }

    /// Try to convert to vector (non-consuming)
    pub fn to_vec(&self) -> Option<Vec<F>> {
        match self.products.as_slice() {
            [(coeff, indices)] if indices.len() == 1 && coeff.is_one() => {
                self.flattened_polys[indices[0]].to_vec()
            }
            _ => None,
        }
    }

    /// Add a scalar to the polynomial
    pub fn poly_add_scalar(&self, scalar: F) -> Self {
        let mut result = self.clone();
        result.add_poly_list([], scalar);
        result
    }

    /// Add two polynomials, merging their sums of products.
    pub fn poly_add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.add_scaled(other, F::one());
        result
    }

    /// Subtract a scalar from the polynomial
    pub fn poly_sub_scalar(&self, scalar: F) -> Self {
        self.poly_add_scalar(-scalar)
    }

    /// Subtract two polynomials, merging their sums of products.
    pub fn poly_sub(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.add_scaled(other, -F::one());
        result
    }

    /// Multiply by a scalar
    pub fn poly_mul_scalar(&self, scalar: F) -> Self {
        let mut result = self.clone();
        if scalar.is_zero() {
            result.products.clear();
        } else {
            for (coeff, _) in &mut result.products {
                *coeff *= scalar;
            }
        }
        result
    }

    /// This polynomial with its terms `c·f` over multilinear `f` of one arity (the first
    /// such term's) combined into a single table, as `Σ c·f` is multilinear; `None` when
    /// there are fewer than two such terms.
    fn combine_linear_terms(&self) -> Option<Self> {
        let linear = |indices: &[usize]| match indices {
            [i] if matches!(
                *self.flattened_polys[*i],
                PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. }
            ) =>
            {
                Some(self.flattened_polys[*i].num_vars())
            }
            _ => None,
        };
        let num_vars = self.products.iter().find_map(|(_, ix)| linear(ix))?;
        let (terms, rest): (Vec<_>, Vec<_>) = self
            .products
            .iter()
            .partition(|(_, ix)| linear(ix) == Some(num_vars));
        if terms.len() < 2 {
            return None;
        }
        let terms: Vec<(F, &PolyVariant<F>)> = terms
            .iter()
            .map(|(c, ix)| (*c, self.flattened_polys[ix[0]].as_ref()))
            .collect();
        let combined = PolyVariant::linear_combination(num_vars, &terms)?;
        let mut result = Self::new();
        result.num_variables = self.num_variables;
        for (c, ix) in rest {
            result.add_poly_list(ix.iter().map(|&i| Arc::clone(&self.flattened_polys[i])), *c);
        }
        result.add_poly_list([Arc::new(combined)], F::one());
        Some(result)
    }

    /// Multiply two polynomials by distributing their sums of products. Each side's
    /// multilinear terms are first combined into one table when the other side has a
    /// factor to multiply them by, so it gains one product rather than one per term.
    pub fn poly_mul(&self, other: &Self) -> Self {
        let has_factors = |p: &Self| p.products.iter().any(|(_, ix)| !ix.is_empty());
        if has_factors(other)
            && let Some(combined) = self.combine_linear_terms()
        {
            return combined.poly_mul(other);
        }
        if has_factors(self)
            && let Some(combined) = other.combine_linear_terms()
        {
            return self.poly_mul(&combined);
        }
        let mut result = VirtualPolynomial::new();
        result.num_variables = self.num_variables.or(other.num_variables);
        for (coeff1, indices1) in &self.products {
            for (coeff2, indices2) in &other.products {
                let factors = indices1
                    .iter()
                    .map(|&idx| &self.flattened_polys[idx])
                    .chain(indices2.iter().map(|&idx| &other.flattened_polys[idx]))
                    .cloned();
                result.add_poly_list(factors, *coeff1 * *coeff2);
            }
        }
        result
    }

    /// Subtract polynomial from scalar (scalar - poly)
    pub fn scalar_sub_poly(scalar: F, poly: &Self) -> Self {
        VirtualPolynomial::from_scalar(scalar).poly_sub(poly)
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
        let mut result: Option<PolyVariant<F>> = None;
        for (coeff, indices) in &self.products {
            let mut factors = indices
                .iter()
                .map(|&idx| self.flattened_polys[idx].as_ref());
            let term = match factors.next() {
                None => PolyVariant::from_scalar(*coeff),
                Some(first) => {
                    let product = factors.try_fold(first.clone(), |acc, p| acc.poly_mul(p))?;
                    if coeff.is_one() {
                        product
                    } else {
                        product.poly_mul_scalar(*coeff)
                    }
                }
            };
            result = Some(match result {
                None => term,
                Some(acc) => acc.poly_add(&term)?,
            });
        }
        Ok(result.unwrap_or_else(|| PolyVariant::from_scalar(F::zero())))
    }

    /// Whether the normalized polynomial is univariate.
    ///
    /// Answers from the declared arity when one is recorded, then without
    /// normalizing when every factor is univariate (products and sums of
    /// univariates, and scalar-only terms, normalize to a univariate), and
    /// otherwise normalizes; a normalization failure degrades to the arity
    /// reported by [`Self::num_vars`].
    pub fn is_univariate(&self) -> bool {
        if let Some(num_vars) = self.num_variables {
            return num_vars == 1;
        }
        self.factors().all(PolyVariant::is_univariate)
            || self
                .normalize()
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
        self.normalize().is_ok_and(|p| p.is_multilinear())
    }

    /// Declared arity, falling back to the arity of the first factor when it
    /// is multivariate. `None` means the arity is unknown (for instance a
    /// purely scalar or univariate virtual polynomial).
    pub fn num_vars(&self) -> Option<usize> {
        self.num_variables.or_else(|| {
            self.flattened_polys
                .first()
                .filter(|poly| poly.is_multivariate())
                .map(|poly| poly.num_vars())
        })
    }

    /// Whether this is a polynomial of type `typ`, judged from its structure
    /// (so conservatively: a polynomial whose degree cancels down to the
    /// bound may be refused, one above it never accepted):
    /// - `Uni(d)`: univariate factors only, each product of degree at most `d`;
    /// - `Mle(n)`: `n`-variable multilinear factors, at most one per product;
    /// - `VPoly(n, d)`: `n`-variable multivariate factors, each product of
    ///   total degree at most `d` (an `n`-variable MLE counts as `n`).
    ///
    /// Every factor must be well formed ([`PolyVariant::is_well_formed`]).
    /// Any other type gives `false`.
    pub fn conforms_to(&self, typ: &crate::ATyp) -> bool {
        use crate::ATyp;
        let factors_ok = |ok: &dyn Fn(&PolyVariant<F>) -> bool| {
            self.flattened_polys
                .iter()
                .all(|p| p.is_well_formed() && ok(p))
        };
        let max_product_degree = || {
            self.products
                .iter()
                .map(|(_, indices)| {
                    indices
                        .iter()
                        .map(|&i| self.flattened_polys[i].total_degree_bound())
                        .sum::<usize>()
                })
                .max()
                .unwrap_or(0)
        };
        match *typ {
            ATyp::Uni(d) => {
                self.num_variables.is_none_or(|n| n == 1)
                    && factors_ok(&PolyVariant::is_univariate)
                    && max_product_degree() <= d
            }
            ATyp::Mle(n) => {
                self.num_vars() == Some(n)
                    && factors_ok(&|p| {
                        matches!(p, PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. })
                            && p.num_vars() == n
                    })
                    && self.products.iter().all(|(_, indices)| indices.len() <= 1)
            }
            ATyp::VPoly(n, d) => {
                self.num_vars() == Some(n)
                    && factors_ok(&|p| p.is_multivariate() && p.num_vars() == n)
                    && max_product_degree() <= d
            }
            _ => false,
        }
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

    /// Divide two virtual polynomials by normalizing both sides first.
    ///
    /// # Errors
    /// Propagates [`Self::normalize`] on either operand, and
    /// [`PolyVariant::poly_div`] failures such as
    /// [`PolyError::DivisionByZero`] or [`PolyError::DivisionNotApplicable`].
    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError<F>> {
        let result = self.normalize()?.poly_div(&other.normalize()?)?;
        Ok(VirtualPolynomial::from_poly(result))
    }

    /// Divide by a scalar by multiplying with its inverse, which keeps the
    /// sum-of-products form intact.
    ///
    /// # Errors
    /// Returns [`PolyError::DivisionByZero`] if `scalar` has no inverse.
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>> {
        let inv = scalar.inverse().ok_or_else(|| PolyError::DivisionByZero {
            v: PolyVariant::from_scalar(scalar),
        })?;
        Ok(self.poly_mul_scalar(inv))
    }
}

impl<F: Field> VirtualPolynomial<F> {
    /// Appends the transcript encoding: tag 0 and the normalized polynomial when it
    /// normalizes, else tag 1 and the explicit sum of products (products from `poly_mul`
    /// may not collapse to one `PolyVariant`, and hashing a public `Poly` value must not
    /// fail).
    pub fn write_bytes(&self, out: &mut Vec<u8>) {
        let u64_le = |out: &mut Vec<u8>, x: usize| out.extend((x as u64).to_le_bytes());
        if let Ok(normalized) = self.normalize() {
            out.push(0);
            normalized.write_bytes(out);
            return;
        }
        out.push(1);
        match self.num_variables {
            Some(n) => {
                out.push(1);
                u64_le(out, n);
            }
            None => out.push(0),
        }
        u64_le(out, self.products.len());
        for (coeff, indices) in &self.products {
            coeff.write_bytes(out);
            u64_le(out, indices.len());
            for &idx in indices {
                u64_le(out, idx);
            }
        }
        u64_le(out, self.flattened_polys.len());
        for poly in &self.flattened_polys {
            poly.write_bytes(out);
        }
    }
}

impl<F: Field> Default for VirtualPolynomial<F> {
    fn default() -> Self {
        VirtualPolynomial::new()
    }
}

impl<F: Field> Add for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn add(self, other: Self) -> Self::Output {
        self.poly_add(other)
    }
}

impl<F: Field> Sub for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn sub(self, other: Self) -> Self::Output {
        self.poly_sub(other)
    }
}

impl<F: Field> Mul for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn mul(self, other: Self) -> Self::Output {
        self.poly_mul(other)
    }
}

impl<F: Field> Add for VirtualPolynomial<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        &self + &other
    }
}

impl<F: Field> Sub for VirtualPolynomial<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        &self - &other
    }
}

impl<F: Field> Mul for VirtualPolynomial<F> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        &self * &other
    }
}

impl<F: Field> PartialEq for VirtualPolynomial<F> {
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

impl<F: Field> Eq for VirtualPolynomial<F> {}

impl<F: Field> fmt::Display for VirtualPolynomial<F> {
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
mod tests;
