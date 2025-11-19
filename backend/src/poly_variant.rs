use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{
    DenseUVPolynomial, Polynomial,
    univariate::{DensePolynomial, SparsePolynomial, DenseOrSparsePolynomial},
    DenseMultilinearExtension, MultilinearExtension,
    evaluations::multivariate::multilinear::SparseMultilinearExtension,
};
use ark_serialize::{CanonicalSerialize, SerializationError};
use std::io::Write;
use std::fmt;
use thiserror::Error;

/// Virtual Polynomial - represents a polynomial as a sum of terms, where each term
/// is a coefficient multiplied by a product of base polynomials.
/// This is useful for sum-check protocols and allows flexible representation
/// of polynomial products without explicitly computing the full expansion.
#[derive(Debug, Clone)]
pub struct VirtualPolynomial<F: Field> {
    /// List of terms, where each term is (coefficient, vector of polynomials to multiply)
    /// The term evaluates to: coefficient * poly[0] * poly[1] * ... * poly[n-1]
    pub terms: Vec<(F, Vec<PolyVariant<F>>)>,
}

#[derive(Error, Debug, Clone)]
pub enum PolyError {
    #[error("Cannot multiply two multilinear polynomials - result would not be multilinear")]
    MleMultiplication,

    #[error("Cannot multiply univariate and multilinear polynomials - incompatible types")]
    IncompatibleMultiplication,

    #[error("Polynomial division not implemented for multilinear extension polynomials")]
    DivisionNotApplicable,

    #[error("Division by zero")]
    DivisionByZero,

    #[error("Can only divide scalar by constant polynomial")]
    ScalarDivByNonConstant,

    #[error("Polynomial modulo not applicable for multilinear extension polynomials")]
    ModuloNotApplicable,

    #[error("Cannot convert non-constant polynomial to scalar (degree: {degree})")]
    NotConstantPolynomial { degree: usize },

    #[error("Cannot perform operation on MLEs with different number of variables: {v1} vs {v2}")]
    MleVariableMismatch { v1: usize, v2: usize },

    #[error("Evaluation point dimension mismatch: expected {expected}, got {actual}")]
    DimensionMismatch { expected: usize, actual: usize },

    #[error("Can only evaluate MLE polynomials with evaluate_mle")]
    NotMlePolynomial,

    #[error("Operation only works for MLE polynomials")]
    RequiresMle,

    #[error("Index out of bounds: {index} >= {size}")]
    IndexOutOfBounds { index: usize, size: usize },
}

/// Polynomial types supported by the backend
#[derive(Debug, Clone)]
pub enum PolyVariant<F: Field> {
    /// Dense univariate polynomial
    DenseUni(DensePolynomial<F>),
    /// Sparse univariate polynomial
    SparseUni(SparsePolynomial<F>),
    /// Dense multilinear extension
    DenseMle(DenseMultilinearExtension<F>),
    /// Sparse multilinear extension
    SparseMle(SparseMultilinearExtension<F>),
    /// Virtual polynomial - sum of terms (coefficient * product of polynomials)
    Virtual(VirtualPolynomial<F>),
}

impl<F: Field> VirtualPolynomial<F> {
    /// Create a new empty virtual polynomial
    pub fn new() -> Self {
        VirtualPolynomial { terms: Vec::new() }
    }

    /// Create a virtual polynomial from a single polynomial (coefficient 1)
    pub fn from_poly(poly: PolyVariant<F>) -> Self {
        VirtualPolynomial {
            terms: vec![(F::one(), vec![poly])],
        }
    }

    /// Create a virtual polynomial from a scalar (constant term)
    pub fn from_scalar(scalar: F) -> Self {
        if scalar.is_zero() {
            VirtualPolynomial::new()
        } else {
            VirtualPolynomial {
                terms: vec![(scalar, vec![])],
            }
        }
    }

    /// Multiply two virtual polynomials
    pub fn mul_virtual(&self, other: &Self) -> Self {
        let mut result = VirtualPolynomial::new();
        for (coeff1, polys1) in &self.terms {
            for (coeff2, polys2) in &other.terms {
                let new_coeff = *coeff1 * *coeff2;
                let mut new_polys = polys1.clone();
                new_polys.extend(polys2.clone());
                result.terms.push((new_coeff, new_polys));
            }
        }
        result.simplify();
        result
    }

    /// Add two virtual polynomials
    pub fn add_virtual(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.terms.extend(other.terms.clone());
        result.simplify();
        result
    }

    /// Multiply by a scalar
    pub fn mul_scalar(&self, scalar: F) -> Self {
        if scalar.is_zero() {
            return VirtualPolynomial::new();
        }
        let mut result = self.clone();
        for (coeff, _) in &mut result.terms {
            *coeff *= scalar;
        }
        result
    }

    /// Evaluate the virtual polynomial at a point (for univariate)
    pub fn evaluate(&self, point: &F) -> F {
        self.terms.iter()
            .map(|(coeff, polys)| {
                let prod = polys.iter()
                    .map(|p| p.evaluate(point))
                    .fold(F::one(), |acc, val| acc * val);
                *coeff * prod
            })
            .sum()
    }

    /// Evaluate the virtual polynomial at an MLE point
    pub fn evaluate_mle(&self, point: &[F]) -> Result<F, PolyError> {
        let mut result = F::zero();
        for (coeff, polys) in &self.terms {
            let mut prod = *coeff;
            for p in polys {
                prod = prod * p.evaluate_mle(point)?;
            }
            result += prod;
        }
        Ok(result)
    }

    /// Check if the virtual polynomial is zero
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty() || self.terms.iter().all(|(coeff, _)| coeff.is_zero())
    }

    /// Simplify by removing zero terms
    pub fn simplify(&mut self) {
        self.terms.retain(|(coeff, _)| !coeff.is_zero());
    }
}

impl<F: Field> Default for VirtualPolynomial<F> {
    fn default() -> Self {
        VirtualPolynomial::new()
    }
}

impl<F: Field> PolyVariant<F> {
    // ========== Query Methods ==========

    /// Get the degree of a univariate polynomial (returns None for multilinear or virtual)
    pub fn degree(&self) -> Option<usize> {
        match self {
            PolyVariant::DenseUni(p) => Some(p.degree()),
            PolyVariant::SparseUni(p) => Some(p.degree()),
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle(_) | PolyVariant::Virtual(_) => None,
        }
    }

    /// Get the number of variables for a multilinear polynomial (returns None for univariate or virtual)
    pub fn num_vars(&self) -> Option<usize> {
        match self {
            PolyVariant::DenseMle(mle) => Some(mle.num_vars()),
            PolyVariant::SparseMle(mle) => Some(mle.num_vars),
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) | PolyVariant::Virtual(_) => None,
        }
    }

    /// Check if this is a univariate polynomial
    pub fn is_univariate(&self) -> bool {
        matches!(self, PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_))
    }

    /// Check if this is a multilinear polynomial
    pub fn is_multilinear(&self) -> bool {
        matches!(self, PolyVariant::DenseMle(_) | PolyVariant::SparseMle(_))
    }

    /// Check if this is a virtual polynomial
    pub fn is_virtual(&self) -> bool {
        matches!(self, PolyVariant::Virtual(_))
    }

    // ========== Conversion Methods ==========

    /// Convert to dense representation if sparse
    /// Virtual polynomials cannot be converted to dense without evaluation
    pub fn to_dense(&self) -> Self {
        match self {
            PolyVariant::SparseUni(p) => PolyVariant::DenseUni(p.clone().into()),
            PolyVariant::SparseMle(mle) => {
                // Convert sparse MLE to dense by creating evaluations vector
                let evals = (0..(1 << mle.num_vars))
                    .map(|i| {
                        mle.evaluations.iter()
                            .find(|(idx, _)| **idx == i)
                            .map(|(_, v)| *v)
                            .unwrap_or_else(F::zero)
                    })
                    .collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars, evals))
            }
            PolyVariant::Virtual(_) => {
                // Virtual polynomials stay virtual - cannot convert without evaluation
                self.clone()
            }
            dense => dense.clone(),
        }
    }

    /// Try to convert univariate degree-0 polynomial to scalar
    pub fn try_to_scalar(&self) -> Option<F> {
        match self {
            PolyVariant::DenseUni(p) if p.degree() == 0 => p.coeffs.first().cloned(),
            PolyVariant::SparseUni(p) if p.degree() == 0 => {
                // Convert to dense to access coefficients
                let dense: DensePolynomial<F> = p.clone().into();
                dense.coeffs.first().cloned()
            }
            PolyVariant::Virtual(vp) => {
                // If all terms have empty polynomial lists, it's a constant
                if vp.terms.iter().all(|(_, polys)| polys.is_empty()) {
                    Some(vp.terms.iter().map(|(coeff, _)| *coeff).sum())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Create a univariate degree-0 polynomial from a scalar
    pub fn from_scalar(scalar: F) -> Self {
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![scalar]))
    }

    /// Convert to scalar if this is a constant polynomial
    pub fn to_scalar(&self) -> Option<F> {
        match self {
            PolyVariant::DenseUni(p) => {
                if p.degree() == 0 {
                    Some(p.coeffs[0])
                } else {
                    None
                }
            }
            PolyVariant::SparseUni(p) => {
                if p.degree() == 0 {
                    // Evaluate at 0 to get constant coefficient
                    Some(p.evaluate(&F::zero()))
                } else {
                    None
                }
            }
            PolyVariant::DenseMle(mle) => {
                if mle.num_vars() == 0 {
                    Some(mle.evaluations[0])
                } else {
                    None
                }
            }
            PolyVariant::SparseMle(mle) => {
                if mle.num_vars == 0 {
                    Some(mle.evaluations.get(&0).copied().unwrap_or_else(F::zero))
                } else {
                    None
                }
            }
            PolyVariant::Virtual(vp) => {
                // If all terms have empty polynomial lists, it's a constant
                if vp.terms.iter().all(|(_, polys)| polys.is_empty()) {
                    Some(vp.terms.iter().map(|(coeff, _)| *coeff).sum())
                } else {
                    None
                }
            }
        }
    }

    /// Convert to vector if this is an MLE
    pub fn to_vec(&self) -> Option<Vec<F>> {
        match self {
            PolyVariant::DenseMle(mle) => Some(mle.evaluations.clone()),
            PolyVariant::SparseMle(mle) => {
                let mut v = vec![F::zero(); 1 << mle.num_vars];
                for (idx, val) in &mle.evaluations {
                    v[*idx] = *val;
                }
                Some(v)
            }
            _ => None
        }
    }

    /// Get coefficients if this is a univariate polynomial
    pub fn to_coeffs(&self) -> Option<Vec<F>> {
        match self {
            PolyVariant::DenseUni(p) => Some(p.coeffs.clone()),
            PolyVariant::SparseUni(p) => {
                // Convert to dense first
                let dense: DensePolynomial<F> = p.clone().into();
                Some(dense.coeffs)
            }
            _ => None
        }
    }

    /// Create univariate polynomial from coefficients
    pub fn from_coeffs(coeffs: Vec<F>) -> Self {
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs))
    }

    /// Check if polynomial is zero
    pub fn is_zero(&self) -> bool {
        match self {
            PolyVariant::DenseUni(p) => p.coeffs.iter().all(|c| c.is_zero()),
            PolyVariant::SparseUni(_) => {
                // Convert to dense to check
                let dense = self.to_dense();
                if let PolyVariant::DenseUni(p) = dense {
                    p.coeffs.iter().all(|c| c.is_zero())
                } else {
                    false
                }
            }
            PolyVariant::DenseMle(mle) => mle.evaluations.iter().all(|e| e.is_zero()),
            PolyVariant::SparseMle(_) => {
                // Convert to dense to check
                let dense = self.to_dense();
                if let PolyVariant::DenseMle(mle) = dense {
                    mle.evaluations.iter().all(|e| e.is_zero())
                } else {
                    false
                }
            }
            PolyVariant::Virtual(vp) => vp.is_zero(),
        }
    }

    // ========== Arithmetic Operations ==========

    /// Add two polynomials
    pub fn poly_add(&self, other: &Self) -> Result<Self, PolyError> {
        match (self, other) {
            // Univariate + Univariate
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                Ok(PolyVariant::DenseUni(p1 + p2))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::SparseUni(p2)) => {
                Ok(PolyVariant::SparseUni(p1 + p2))
            }

            // MLE + MLE
            (PolyVariant::DenseMle(m1), PolyVariant::DenseMle(m2)) => {
                if m1.num_vars() != m2.num_vars() {
                    return Err(PolyError::MleVariableMismatch {
                        v1: m1.num_vars(),
                        v2: m2.num_vars()
                    });
                }
                Ok(PolyVariant::DenseMle(m1 + m2))
            }
            (PolyVariant::SparseMle(m1), PolyVariant::SparseMle(m2)) => {
                if m1.num_vars != m2.num_vars {
                    return Err(PolyError::MleVariableMismatch {
                        v1: m1.num_vars,
                        v2: m2.num_vars
                    });
                }
                // Combine evaluations
                let mut combined = m1.evaluations.clone();
                for (idx, val) in &m2.evaluations {
                    combined.entry(*idx)
                        .and_modify(|v| *v += *val)
                        .or_insert(*val);
                }
                // Convert to dense for now - sparse MLE construction is complex
                let mut evals = vec![F::zero(); 1 << m1.num_vars];
                for (idx, val) in combined {
                    evals[idx] = val;
                }
                Ok(PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(m1.num_vars, evals)))
            }

            // Virtual + Virtual
            (PolyVariant::Virtual(v1), PolyVariant::Virtual(v2)) => {
                Ok(PolyVariant::Virtual(v1.add_virtual(&v2)))
            }

            // Virtual + Other or Other + Virtual
            (PolyVariant::Virtual(v1), other) => {
                let v2 = other.to_virtual();
                Ok(PolyVariant::Virtual(v1.add_virtual(&v2)))
            }
            (other, PolyVariant::Virtual(v2)) => {
                let v1 = other.to_virtual();
                Ok(PolyVariant::Virtual(v1.add_virtual(&v2)))
            }

            // Mixed types - convert to dense and retry
            _ => {
                self.to_dense().poly_add(&other.to_dense())
            }
        }
    }

    /// Add a scalar to a polynomial
    pub fn poly_add_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(p + &DensePolynomial::from_coefficients_vec(vec![scalar]))
            }
            PolyVariant::DenseMle(mle) => {
                let added_evals = mle.iter().map(|&eval| eval + scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), added_evals))
            }
            PolyVariant::Virtual(vp) => {
                // Add constant term
                let mut result = vp.clone();
                if !scalar.is_zero() {
                    result.terms.push((scalar, vec![]));
                }
                result.simplify();
                PolyVariant::Virtual(result)
            }
            _ => {
                // Convert to dense first
                self.to_dense().poly_add_scalar(scalar)
            }
        }
    }

    /// Subtract two polynomials
    pub fn poly_sub(&self, other: &Self) -> Result<Self, PolyError> {
        match (self, other) {
            // Univariate - Univariate
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                Ok(PolyVariant::DenseUni(p1 - p2))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::SparseUni(p2)) => {
                // Convert to dense for subtraction
                let dense1: DensePolynomial<F> = p1.clone().into();
                let dense2: DensePolynomial<F> = p2.clone().into();
                Ok(PolyVariant::DenseUni(&dense1 - &dense2))
            }

            // MLE - MLE
            (PolyVariant::DenseMle(m1), PolyVariant::DenseMle(m2)) => {
                if m1.num_vars() != m2.num_vars() {
                    return Err(PolyError::MleVariableMismatch {
                        v1: m1.num_vars(),
                        v2: m2.num_vars()
                    });
                }
                Ok(PolyVariant::DenseMle(m1 - m2))
            }

            // Virtual - Virtual
            (PolyVariant::Virtual(v1), PolyVariant::Virtual(v2)) => {
                let neg_v2 = v2.mul_scalar(-F::one());
                Ok(PolyVariant::Virtual(v1.add_virtual(&neg_v2)))
            }

            // Virtual - Other or Other - Virtual
            (PolyVariant::Virtual(v1), other) => {
                let v2 = other.to_virtual();
                let neg_v2 = v2.mul_scalar(-F::one());
                Ok(PolyVariant::Virtual(v1.add_virtual(&neg_v2)))
            }
            (other, PolyVariant::Virtual(v2)) => {
                let v1 = other.to_virtual();
                let neg_v2 = v2.mul_scalar(-F::one());
                Ok(PolyVariant::Virtual(v1.add_virtual(&neg_v2)))
            }

            // Mixed types - convert to dense and retry
            _ => {
                self.to_dense().poly_sub(&other.to_dense())
            }
        }
    }

    /// Subtract scalar from polynomial
    pub fn poly_sub_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(p - &DensePolynomial::from_coefficients_vec(vec![scalar]))
            }
            PolyVariant::DenseMle(mle) => {
                let sub_evals = mle.iter().map(|&eval| eval - scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), sub_evals))
            }
            _ => {
                self.to_dense().poly_sub_scalar(scalar)
            }
        }
    }

    /// Subtract polynomial from scalar
    pub fn scalar_sub_poly(scalar: F, poly: &Self) -> Self {
        match poly {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(&DensePolynomial::from_coefficients_vec(vec![scalar]) - p)
            }
            PolyVariant::DenseMle(mle) => {
                let sub_evals = mle.iter().map(|&eval| scalar - eval).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), sub_evals))
            }
            _ => {
                Self::scalar_sub_poly(scalar, &poly.to_dense())
            }
        }
    }

    /// Negate a polynomial
    pub fn poly_neg(&self) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                let neg_coeffs = p.coeffs.iter().map(|c| -*c).collect();
                PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(neg_coeffs))
            }
            PolyVariant::SparseUni(p) => {
                // Convert to dense, negate, keep as dense
                let dense: DensePolynomial<F> = p.clone().into();
                let neg_coeffs = dense.coeffs.iter().map(|c| -*c).collect();
                PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(neg_coeffs))
            }
            PolyVariant::DenseMle(mle) => {
                let neg_evals = mle.iter().map(|&eval| -eval).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), neg_evals))
            }
            PolyVariant::SparseMle(mle) => {
                // Convert to dense, negate
                let dense_evals: Vec<F> = mle.to_evaluations();
                let neg_evals = dense_evals.iter().map(|&eval| -eval).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars, neg_evals))
            }
            PolyVariant::Virtual(vp) => {
                PolyVariant::Virtual(vp.mul_scalar(-F::one()))
            }
        }
    }

    /// Multiply two polynomials - always returns a VirtualPolynomial for any multiplication
    pub fn poly_mul(&self, other: &Self) -> Result<Self, PolyError> {
        // Convert both polynomials to virtual representation and multiply
        let v1 = self.to_virtual();
        let v2 = other.to_virtual();
        Ok(PolyVariant::Virtual(v1.mul_virtual(&v2)))
    }

    /// Convert to virtual polynomial representation
    pub fn to_virtual(&self) -> VirtualPolynomial<F> {
        match self {
            PolyVariant::Virtual(vp) => vp.clone(),
            _ => VirtualPolynomial::from_poly(self.clone()),
        }
    }

    /// Multiply polynomial by scalar
    pub fn poly_mul_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(p * scalar)
            }
            PolyVariant::DenseMle(mle) => {
                let mul_evals = mle.iter().map(|&eval| eval * scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), mul_evals))
            }
            PolyVariant::Virtual(vp) => {
                PolyVariant::Virtual(vp.mul_scalar(scalar))
            }
            _ => {
                self.to_dense().poly_mul_scalar(scalar)
            }
        }
    }

    /// Divide two polynomials
    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError>
    where
        F: PrimeField,
    {
        match (self, other) {
            // Univariate / Univariate - use ark_poly's divide_with_q_and_r
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                if p2.is_zero() {
                    return Err(PolyError::DivisionByZero);
                }
                // Use ark_poly's polynomial division via DenseOrSparsePolynomial
                let dividend = DenseOrSparsePolynomial::from(p1.clone());
                let divisor = DenseOrSparsePolynomial::from(p2.clone());
                let (quotient, _remainder) = dividend.divide_with_q_and_r(&divisor)
                    .ok_or(PolyError::DivisionByZero)?;
                Ok(PolyVariant::DenseUni(quotient))
            }

            // MLE division not supported
            (PolyVariant::DenseMle(_), _) |
            (PolyVariant::SparseMle(_), _) |
            (_, PolyVariant::DenseMle(_)) |
            (_, PolyVariant::SparseMle(_)) => {
                Err(PolyError::DivisionNotApplicable)
            }

            // Sparse univariate - convert to dense first
            _ => {
                self.to_dense().poly_div(&other.to_dense())
            }
        }
    }

    /// Divide polynomial by scalar
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError> {
        if scalar.is_zero() {
            return Err(PolyError::DivisionByZero);
        }

        match self {
            PolyVariant::DenseUni(p) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero)?;
                Ok(PolyVariant::DenseUni(p * inv_scalar))
            }
            PolyVariant::DenseMle(mle) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero)?;
                let div_evals = mle.iter().map(|&eval| eval * inv_scalar).collect();
                Ok(PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), div_evals)))
            }
            PolyVariant::Virtual(vp) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero)?;
                Ok(PolyVariant::Virtual(vp.mul_scalar(inv_scalar)))
            }
            _ => {
                self.to_dense().poly_div_scalar(scalar)
            }
        }
    }

    /// Scalar divide by polynomial (for cases like Index / Poly)
    pub fn scalar_div_poly(scalar: F, poly: &Self) -> Result<Self, PolyError> {
        // This only makes sense if poly is a constant (degree 0)
        if let Some(poly_scalar) = poly.try_to_scalar() {
            if poly_scalar.is_zero() {
                return Err(PolyError::DivisionByZero);
            }
            let result = scalar * poly_scalar.inverse().ok_or(PolyError::DivisionByZero)?;
            Ok(PolyVariant::from_scalar(result))
        } else {
            Err(PolyError::ScalarDivByNonConstant)
        }
    }

    /// Polynomial remainder (modulo)
    pub fn poly_rem(&self, other: &Self) -> Result<Self, PolyError>
    where
        F: PrimeField,
    {
        match (self, other) {
            // Univariate % Univariate - use ark_poly's divide_with_q_and_r
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                if p2.is_zero() {
                    return Err(PolyError::DivisionByZero);
                }
                // Use ark_poly's polynomial division to get the remainder
                let dividend = DenseOrSparsePolynomial::from(p1.clone());
                let divisor = DenseOrSparsePolynomial::from(p2.clone());
                let (_quotient, remainder) = dividend.divide_with_q_and_r(&divisor)
                    .ok_or(PolyError::DivisionByZero)?;
                Ok(PolyVariant::DenseUni(remainder))
            }

            // MLE modulo not supported
            (PolyVariant::DenseMle(_), _) |
            (PolyVariant::SparseMle(_), _) |
            (_, PolyVariant::DenseMle(_)) |
            (_, PolyVariant::SparseMle(_)) => {
                Err(PolyError::ModuloNotApplicable)
            }

            // Sparse - convert to dense first
            _ => {
                self.to_dense().poly_rem(&other.to_dense())
            }
        }
    }

    /// Evaluate polynomial at a point
    pub fn evaluate(&self, point: &F) -> F {
        match self {
            PolyVariant::DenseUni(p) => p.evaluate(point),
            PolyVariant::SparseUni(p) => p.evaluate(point),
            PolyVariant::Virtual(vp) => vp.evaluate(point),
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle(_) => {
                panic!("Cannot evaluate MLE at single point - use evaluate_mle with boolean hypercube point")
            }
        }
    }

    /// Evaluate MLE at a boolean hypercube point
    pub fn evaluate_mle(&self, point: &[F]) -> Result<F, PolyError> {
        match self {
            PolyVariant::DenseMle(mle) => {
                if point.len() != mle.num_vars() {
                    return Err(PolyError::DimensionMismatch {
                        expected: mle.num_vars(),
                        actual: point.len()
                    });
                }
                Ok(mle.evaluate(&point.to_vec()))
            }
            PolyVariant::SparseMle(mle) => {
                if point.len() != mle.num_vars {
                    return Err(PolyError::DimensionMismatch {
                        expected: mle.num_vars,
                        actual: point.len()
                    });
                }
                // Manual evaluation for sparse MLE
                let idx = point.iter().enumerate()
                    .fold(0usize, |acc, (i, &val)| {
                        if !val.is_zero() && !val.is_one() {
                            panic!("MLE evaluation point must be boolean (0 or 1)");
                        }
                        acc | (if val.is_one() { 1 << i } else { 0 })
                    });
                Ok(mle.evaluations.get(&idx).cloned().unwrap_or_else(F::zero))
            }
            PolyVariant::Virtual(vp) => {
                vp.evaluate_mle(point)
            }
            _ => Err(PolyError::NotMlePolynomial)
        }
    }

    /// Evaluate univariate polynomial at multiple points
    /// Returns a univariate polynomial representing the vector of results
    pub fn evaluate_vec(&self, points: &[F]) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                let vals: Vec<F> = points.iter().map(|pt| p.evaluate(pt)).collect();
                // Return as MLE with log2(n) variables
                let num_vars = (vals.len() as f64).log2().ceil() as usize;
                let mut padded = vals.clone();
                padded.resize(1 << num_vars, F::zero());
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(num_vars, padded))
            }
            PolyVariant::SparseUni(p) => {
                let vals: Vec<F> = points.iter().map(|pt| p.evaluate(pt)).collect();
                // Return as MLE with log2(n) variables
                let num_vars = (vals.len() as f64).log2().ceil() as usize;
                let mut padded = vals.clone();
                padded.resize(1 << num_vars, F::zero());
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(num_vars, padded))
            }
            PolyVariant::Virtual(vp) => {
                let vals: Vec<F> = points.iter().map(|pt| vp.evaluate(pt)).collect();
                // Return as MLE with log2(n) variables
                let num_vars = (vals.len() as f64).log2().ceil() as usize;
                let mut padded = vals.clone();
                padded.resize(1 << num_vars, F::zero());
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(num_vars, padded))
            }
            _ => panic!("evaluate_vec only works for univariate polynomials")
        }
    }

    /// Evaluate or partially fix MLE variables
    /// Always returns a polynomial (possibly constant after full evaluation)
    pub fn evaluate_or_fix_mle(&self, points: &[F]) -> Result<Self, PolyError> {
        match self {
            PolyVariant::DenseMle(mle) => {
                if points.len() < mle.num_vars() {
                    // Partial evaluation - fix first k variables
                    let fixed = mle.fix_variables(points);
                    Ok(PolyVariant::DenseMle(fixed))
                } else if points.len() == mle.num_vars() {
                    // Full evaluation - return as constant polynomial
                    let val = mle.evaluate(&points.to_vec());
                    Ok(Self::from_scalar(val))
                } else {
                    Err(PolyError::DimensionMismatch {
                        expected: mle.num_vars(),
                        actual: points.len()
                    })
                }
            }
            PolyVariant::SparseMle(_) => {
                // Convert to dense for evaluation
                let dense = self.to_dense();
                dense.evaluate_or_fix_mle(points)
            }
            PolyVariant::Virtual(vp) => {
                // For virtual polynomials, evaluate fully
                let val = vp.evaluate_mle(points)?;
                Ok(Self::from_scalar(val))
            }
            _ => Err(PolyError::RequiresMle)
        }
    }

    // ========== Serialization ==========

    /// Serialize to writer
    pub fn serialize_compressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        match self {
            PolyVariant::DenseUni(p) => {
                0u8.serialize_compressed(&mut writer)?;
                p.serialize_compressed(&mut writer)
            }
            PolyVariant::SparseUni(p) => {
                1u8.serialize_compressed(&mut writer)?;
                p.serialize_compressed(&mut writer)
            }
            PolyVariant::DenseMle(mle) => {
                2u8.serialize_compressed(&mut writer)?;
                mle.serialize_compressed(&mut writer)
            }
            PolyVariant::SparseMle(mle) => {
                3u8.serialize_compressed(&mut writer)?;
                mle.serialize_compressed(&mut writer)
            }
            PolyVariant::Virtual(_vp) => {
                // Virtual polynomials cannot be serialized easily - would need full expansion
                // For now, return an error or convert to dense first
                Err(SerializationError::InvalidData)
            }
        }
    }
}

impl<F: Field> PartialEq for PolyVariant<F> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PolyVariant::DenseUni(a), PolyVariant::DenseUni(b)) => a == b,
            (PolyVariant::SparseUni(a), PolyVariant::SparseUni(b)) => a == b,
            (PolyVariant::DenseMle(a), PolyVariant::DenseMle(b)) => a == b,
            (PolyVariant::SparseMle(a), PolyVariant::SparseMle(b)) => {
                a.num_vars == b.num_vars && a.evaluations == b.evaluations
            },
            (PolyVariant::Virtual(a), PolyVariant::Virtual(b)) => {
                // Compare terms directly
                a.terms.len() == b.terms.len() &&
                a.terms.iter().zip(b.terms.iter()).all(|((c1, p1), (c2, p2))| {
                    c1 == c2 && p1.len() == p2.len() &&
                    p1.iter().zip(p2.iter()).all(|(a, b)| a == b)
                })
            },
            _ => false,
        }
    }
}

impl<F: Field> Eq for PolyVariant<F> {}

impl<F: PrimeField> PartialOrd for PolyVariant<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: PrimeField> Ord for PolyVariant<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        match (self, other) {
            // Both univariate
            (PolyVariant::DenseUni(_), PolyVariant::DenseUni(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::SparseUni(_)) |
            (PolyVariant::DenseUni(_), PolyVariant::SparseUni(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::DenseUni(_)) => {
                // Convert both to dense for comparison
                let self_dense = self.to_dense();
                let other_dense = other.to_dense();

                if let (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) = (self_dense, other_dense) {
                    p1.coeffs.len().cmp(&p2.coeffs.len()).then_with(|| {
                        for (c1, c2) in p1.coeffs.iter().zip(p2.coeffs.iter()) {
                            let ord = c1.into_bigint().cmp(&c2.into_bigint());
                            if ord != Ordering::Equal {
                                return ord;
                            }
                        }
                        Ordering::Equal
                    })
                } else {
                    unreachable!()
                }
            }

            // Both MLE
            (PolyVariant::DenseMle(_), PolyVariant::DenseMle(_)) |
            (PolyVariant::SparseMle(_), PolyVariant::SparseMle(_)) |
            (PolyVariant::DenseMle(_), PolyVariant::SparseMle(_)) |
            (PolyVariant::SparseMle(_), PolyVariant::DenseMle(_)) => {
                // Convert both to dense for comparison
                let self_dense = self.to_dense();
                let other_dense = other.to_dense();

                if let (PolyVariant::DenseMle(m1), PolyVariant::DenseMle(m2)) = (self_dense, other_dense) {
                    m1.num_vars().cmp(&m2.num_vars()).then_with(|| {
                        for (v1, v2) in m1.evaluations.iter().zip(m2.evaluations.iter()) {
                            let ord = v1.into_bigint().cmp(&v2.into_bigint());
                            if ord != Ordering::Equal {
                                return ord;
                            }
                        }
                        Ordering::Equal
                    })
                } else {
                    unreachable!()
                }
            }

            // Both Virtual
            (PolyVariant::Virtual(v1), PolyVariant::Virtual(v2)) => {
                v1.terms.len().cmp(&v2.terms.len()).then_with(|| {
                    // Compare term by term
                    for ((c1, p1), (c2, p2)) in v1.terms.iter().zip(v2.terms.iter()) {
                        let coeff_ord = c1.into_bigint().cmp(&c2.into_bigint());
                        if coeff_ord != Ordering::Equal {
                            return coeff_ord;
                        }
                        let poly_ord = p1.len().cmp(&p2.len());
                        if poly_ord != Ordering::Equal {
                            return poly_ord;
                        }
                    }
                    Ordering::Equal
                })
            }

            // Uni < Mle < Virtual
            (PolyVariant::DenseUni(_), PolyVariant::DenseMle(_)) |
            (PolyVariant::DenseUni(_), PolyVariant::SparseMle(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::DenseMle(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::SparseMle(_)) => Ordering::Less,

            // Uni < Virtual
            (PolyVariant::DenseUni(_), PolyVariant::Virtual(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::Virtual(_)) => Ordering::Less,

            // Mle < Virtual
            (PolyVariant::DenseMle(_), PolyVariant::Virtual(_)) |
            (PolyVariant::SparseMle(_), PolyVariant::Virtual(_)) => Ordering::Less,

            // Virtual > Uni, Mle
            (PolyVariant::Virtual(_), PolyVariant::DenseUni(_)) |
            (PolyVariant::Virtual(_), PolyVariant::SparseUni(_)) |
            (PolyVariant::Virtual(_), PolyVariant::DenseMle(_)) |
            (PolyVariant::Virtual(_), PolyVariant::SparseMle(_)) => Ordering::Greater,

            // Mle > Uni
            _ => Ordering::Greater
        }
    }
}

impl<F: Field> fmt::Display for PolyVariant<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PolyVariant::DenseUni(p) => write!(f, "Uni({:?})", p.coeffs),
            PolyVariant::SparseUni(p) => {
                // Convert to dense for display
                let dense: DensePolynomial<F> = p.clone().into();
                write!(f, "SparseUni({:?})", dense.coeffs)
            }
            PolyVariant::DenseMle(mle) => write!(f, "Mle({:?})", mle.evaluations),
            PolyVariant::SparseMle(mle) => write!(f, "SparseMle({:?})", mle.evaluations),
            PolyVariant::Virtual(vp) => write!(f, "Virtual({} terms)", vp.terms.len()),
        }
    }
}
