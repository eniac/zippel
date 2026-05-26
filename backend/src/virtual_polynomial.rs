use crate::{PolyError, PolyVariant};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalSerialize, SerializationError};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::ops::{Add, Mul, Sub};
use std::sync::Arc;

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
    /// Lookup table mapping polynomial Arc to their indices
    poly_pointers_lookup: HashMap<Arc<PolyVariant<F>>, usize>,
    /// Number of variables (for multivariate polynomials)
    pub num_variables: Option<usize>,
}

impl<F: Field> VirtualPolynomial<F> {
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
        hm.insert(Arc::clone(&poly_arc), 0);

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

    pub fn fix_first_mle_variables_factorwise(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        if points.is_empty() {
            return Ok(self.clone());
        }

        let mut new_flattened = Vec::with_capacity(self.flattened_polys.len());

        for poly_arc in &self.flattened_polys {
            let fixed_variant = match &**poly_arc {
                PolyVariant::DenseMle(mle) => {
                    PolyVariant::DenseMle(mle.clone()).evaluate_or_fix_mle(points)?
                }
                other => other.clone(),
            };

            new_flattened.push(Arc::new(fixed_variant));
        }

        let mut new_lookup = HashMap::new();
        for (idx, poly) in new_flattened.iter().enumerate() {
            new_lookup.insert(Arc::clone(poly), idx);
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

    /// Add a product of polynomials to this virtual polynomial
    /// The polynomials will be multiplied together, then multiplied by the coefficient
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
            if let Some(&index) = self.poly_pointers_lookup.get(&poly) {
                indexed_product.push(index)
            } else {
                let curr_index = self.flattened_polys.len();
                self.flattened_polys.push(poly.clone());
                self.poly_pointers_lookup.insert(poly, curr_index);
                indexed_product.push(curr_index);
            }
        }

        self.products.push((coefficient, indexed_product));
        Ok(())
    }

    /// Multiply this virtual polynomial by another polynomial
    pub fn mul_by_poly(
        &mut self,
        poly: Arc<PolyVariant<F>>,
        coefficient: F,
    ) -> Result<(), PolyError<F>> {
        // Check if this polynomial already exists
        let poly_index = match self.poly_pointers_lookup.get(&poly) {
            Some(&p) => p,
            None => {
                self.poly_pointers_lookup
                    .insert(poly.clone(), self.flattened_polys.len());
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
    pub fn evaluate_mv(&self, point: &[F]) -> Result<F, PolyError<F>> {
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
    pub fn poly_mul(&self, other: &Self) -> Result<Self, PolyError<F>> {
        Ok(self.mul_virtual(other))
    }

    /// Subtract polynomial from scalar (scalar - poly)
    pub fn scalar_sub_poly(scalar: F, poly: &Self) -> Result<Self, PolyError<F>> {
        let scalar_vp = VirtualPolynomial::from_scalar(scalar);
        scalar_vp.poly_sub(poly)
    }

    /// Normalize the virtual polynomial to a single PolyVariant
    /// This expands the sum-of-products into a single polynomial
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

    pub fn is_univariate(&self) -> bool {
        self.normalize().map(|p| p.is_univariate()).unwrap_or(false)
    }

    pub fn is_multilinear(&self) -> bool {
        self.normalize()
            .map(|p| p.is_multilinear())
            .unwrap_or(false)
    }

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

    pub fn degree(&self) -> usize {
        self.normalize().map(|p| p.degree()).unwrap_or(0)
    }

    pub fn to_coeffs(&self) -> Option<Vec<F>> {
        self.normalize().ok().and_then(|p| p.to_coeffs())
    }

    pub fn evaluate_vec(&self, points: &[F]) -> Self {
        // Normalize and evaluate at all points, return as VirtualPolynomial
        if let Ok(normalized) = self.normalize() {
            VirtualPolynomial::from_poly(normalized.evaluate_vec(points))
        } else {
            VirtualPolynomial::new()
        }
    }

    pub fn evaluate_or_fix_mle(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        let normalized = self.normalize()?;
        let result = normalized.evaluate_or_fix_mle(points)?;
        Ok(VirtualPolynomial::from_poly(result))
    }

    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError<F>>
    where
        F: ark_ff::PrimeField,
    {
        let self_norm = self.normalize()?;
        let other_norm = other.normalize()?;
        let result = self_norm.poly_div(&other_norm)?;
        Ok(VirtualPolynomial::from_poly(result))
    }

    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>>
    where
        F: ark_ff::PrimeField,
    {
        let inv = scalar.inverse().ok_or_else(|| PolyError::DivisionByZero {
            v: PolyVariant::from_scalar(scalar),
        })?;
        Ok(self.poly_mul_scalar(inv))
    }

    pub fn scalar_div_poly(scalar: F, poly: &Self) -> Result<Self, PolyError<F>> {
        let poly_norm = poly.normalize()?;
        let result = PolyVariant::scalar_sub_poly(scalar, &poly_norm)?;
        Ok(VirtualPolynomial::from_poly(result))
    }
}

impl<F: Field> CanonicalSerialize for VirtualPolynomial<F> {
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

impl<F: Field> Default for VirtualPolynomial<F> {
    fn default() -> Self {
        VirtualPolynomial::new()
    }
}

impl<F: Field> Add for VirtualPolynomial<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.add_virtual(&other);
        result
    }
}

impl<F: Field> Sub for VirtualPolynomial<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        other_neg.add_virtual(&self);
        other_neg
    }
}

impl<F: Field> Add for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn add(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.add_virtual(other);
        result
    }
}

impl<F: Field> Sub for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        other_neg.add_virtual(self);
        other_neg
    }
}

impl<F: Field> Mul for VirtualPolynomial<F> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let result = self.clone();
        result.mul_virtual(&other);
        result
    }
}

impl<F: Field> Mul for &VirtualPolynomial<F> {
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

impl<F: Field> PartialOrd for VirtualPolynomial<F>
where
    F: ark_ff::PrimeField,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field> Ord for VirtualPolynomial<F>
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
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, univariate::DensePolynomial};
    use ark_std::test_rng;

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
