use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{
    DenseMultilinearExtension, DenseUVPolynomial, MultilinearExtension, Polynomial,
    multivariate::{
        SparsePolynomial as MultiSparsePolynomial, SparseTerm as MultiSparseTerm, Term,
    },
    univariate::{DenseOrSparsePolynomial, DensePolynomial, SparsePolynomial},
};
use ark_serialize::{CanonicalSerialize, SerializationError};
use lang::ast::BinOp;
use rayon::prelude::*;
use std::fmt;
use std::io::Write;
use thiserror::Error;

/// Type alias for sparse multivariate polynomial
type SparseMultivariatePolynomial<F> = MultiSparsePolynomial<F, MultiSparseTerm>;

#[derive(Error, Debug, Clone)]
pub enum PolyError<F: Field> {
    #[error("Unsupported polynomial operation:\n\t{left} {op} {right}")]
    UnsupportedOperation {
        op: BinOp,
        left: PolyVariant<F>,
        right: PolyVariant<F>,
    },

    #[error("Division by zero")]
    DivisionByZero { v: PolyVariant<F> },

    #[error("Can only divide scalar by constant polynomial:\n\t{scalar} / {polynomial}")]
    ScalarDivByNonConstant {
        scalar: F,
        polynomial: PolyVariant<F>,
    },

    #[error("Cannot convert non-constant polynomial {0} to scalar")]
    NotConstantPolynomial(PolyVariant<F>),

    #[error(
        "Cannot perform operation on multivariate polynomial with different number of variables:\n\t{v1} has {n1}, while {v2} has {n2}"
    )]
    VariableMismatch {
        v1: PolyVariant<F>,
        n1: usize,
        v2: PolyVariant<F>,
        n2: usize,
    },

    #[error(
        "Evaluation point dimension mismatch: expected {expected} variables, but received {actual}"
    )]
    DimensionMismatch {
        polynomial: PolyVariant<F>,
        expected: usize,
        actual: usize,
    },

    #[error("MLE variable count mismatch: {v1} vs {v2}")]
    MleVariableMismatch { v1: usize, v2: usize },

    #[error("MLE multiplication not directly supported: {v1} * {v2}")]
    MleMultiplication {
        v1: PolyVariant<F>,
        v2: PolyVariant<F>,
    },

    #[error("Division not applicable for: {v1} / {v2}")]
    DivisionNotApplicable {
        v1: PolyVariant<F>,
        v2: PolyVariant<F>,
    },

    #[error("Modulo operation not applicable for MLE")]
    ModuloNotApplicable,

    #[error("Operation requires MLE polynomial")]
    RequiresMle,

    #[error("Not an MLE polynomial")]
    NotMlePolynomial,
}

/// Polynomial types supported by the backend
#[derive(Debug, Clone, Hash)]
#[allow(clippy::derived_hash_with_manual_eq)]
pub enum PolyVariant<F: Field> {
    /// Dense univariate polynomial
    DenseUni(DensePolynomial<F>),
    /// Sparse univariate polynomial
    SparseUni(SparsePolynomial<F>),
    /// Dense multilinear extension
    DenseMle(DenseMultilinearExtension<F>),
    /// Sparse multivariate polynomial
    SparseMultivariate(SparseMultivariatePolynomial<F>),
}

/// Parallel replacement for `ark_poly::DenseMultilinearExtension::fix_variables`.
/// The arkworks implementation uses sequential `for` loops; this mirrors
/// hyperplonk's `fix_one_variable_helper` which fills each round's halved
/// buffer with `par_iter_mut`.
fn fix_first_variables_parallel<F: Field>(
    mle: &DenseMultilinearExtension<F>,
    partial_point: &[F],
) -> DenseMultilinearExtension<F> {
    assert!(
        partial_point.len() <= mle.num_vars(),
        "invalid size of partial point"
    );
    let nv = mle.num_vars();
    let dim = partial_point.len();
    let mut data: Vec<F> = mle.evaluations.clone();
    for (i, &r) in partial_point.iter().enumerate() {
        let half = 1usize << (nv - i - 1);
        let mut next = vec![F::zero(); half];
        next.par_iter_mut().enumerate().for_each(|(b, slot)| {
            let left = data[b << 1];
            let right = data[(b << 1) + 1];
            *slot = left + r * (right - left);
        });
        data = next;
    }
    DenseMultilinearExtension::from_evaluations_slice(nv - dim, &data[..(1 << (nv - dim))])
}

impl<F: Field> PolyVariant<F> {
    /// Get the degree of the polynomial
    pub fn degree(&self) -> usize {
        match self {
            PolyVariant::DenseUni(p) => p.degree(),
            PolyVariant::SparseUni(p) => p.degree(),
            PolyVariant::DenseMle(_) => 1,
            PolyVariant::SparseMultivariate(p) => p.degree(),
        }
    }

    /// Evaluate polynomial at a point (convenience method)
    pub fn evaluate(&self, point: &Vec<F>) -> F {
        match self {
            // A little hackish - univariate polynomials evaluate over a single Field element
            PolyVariant::DenseUni(p) => p.evaluate(&point[0]),
            PolyVariant::SparseUni(p) => p.evaluate(&point[0]),
            PolyVariant::DenseMle(p) => {
                if point.len() != p.num_vars() {
                    panic!(
                        "Evaluation point dimension mismatch:\n\t MLE expected {}, got {}",
                        p.num_vars(),
                        point.len()
                    );
                } else {
                    p.evaluate(point)
                }
            }
            PolyVariant::SparseMultivariate(p) => {
                if point.len() != p.num_vars {
                    panic!(
                        "Evaluation point dimension mismatch:\n\t Sparse multivariate expected {}, got {}",
                        p.num_vars,
                        point.len()
                    );
                } else {
                    p.evaluate(point)
                }
            }
        }
    }

    /// Get the number of variables for a multilinear polynomial (returns None for univariate or virtual)
    pub fn num_vars(&self) -> usize {
        match self {
            PolyVariant::DenseMle(mle) => mle.num_vars(),
            PolyVariant::SparseMultivariate(p) => p.num_vars,
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => 1,
        }
    }

    /// Check if this is a univariate polynomial
    pub fn is_univariate(&self) -> bool {
        matches!(self, PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_))
    }

    /// Check if this is a multilinear polynomial
    pub fn is_multilinear(&self) -> bool {
        match self {
            PolyVariant::DenseMle(_mle) => true,
            PolyVariant::SparseMultivariate(p) => p.degree() == 1,
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => false,
        }
    }

    /// Check if this is a multivariate polynomial
    pub fn is_multivariate(&self) -> bool {
        matches!(
            self,
            PolyVariant::DenseMle(_) | PolyVariant::SparseMultivariate(_)
        )
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
            PolyVariant::DenseMle(mle) if mle.num_vars() == 0 => mle.evaluations.first().cloned(),
            PolyVariant::SparseMultivariate(p) if p.degree() == 0 && p.num_vars == 0 => {
                // Constant sparse multivariate - should have a single constant term
                // Note: terms are stored as (coeff, term)
                if p.terms.is_empty() {
                    Some(F::zero())
                } else if p.terms.len() == 1 {
                    // Get coefficient from the single term
                    p.terms.first().map(|(c, _term)| *c)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Return MLE evaluation table if this is a DenseMle
    pub fn as_mle_evaluations(&self) -> Option<&[F]> {
        match self {
            PolyVariant::DenseMle(mle) => Some(mle.evaluations.as_slice()),
            _ => None,
        }
    }

    /// Convert to vector of evaluations or coefficients
    pub fn to_vec(&self) -> Option<Vec<F>> {
        match self {
            PolyVariant::DenseMle(mle) => Some(mle.evaluations.clone()),
            PolyVariant::DenseUni(p) => Some(p.coeffs.clone()),
            PolyVariant::SparseUni(p) => {
                let dense: DensePolynomial<F> = p.clone().into();
                Some(dense.coeffs)
            }
            PolyVariant::SparseMultivariate(_) => None,
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
            _ => None,
        }
    }

    /// Check if polynomial is zero
    pub fn is_zero(&self) -> bool {
        match self {
            PolyVariant::DenseUni(p) => p.is_zero(),
            PolyVariant::SparseUni(p) => p.is_zero(),
            PolyVariant::DenseMle(mle) => mle.is_zero(),
            PolyVariant::SparseMultivariate(p) => p.is_zero(),
        }
    }

    /// Create a polynomial from coefficients (univariate)
    pub fn from_coeffs(coeffs: Vec<F>) -> Self {
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs))
    }

    /// Create a polynomial from a scalar constant
    pub fn from_scalar(scalar: F) -> Self {
        // Return as degree-0 univariate polynomial
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![scalar]))
    }

    /// Try to convert to scalar (alias for try_to_scalar for compatibility)
    pub fn to_scalar(&self) -> Option<F> {
        self.try_to_scalar()
    }

    /// Convert polynomial into a scalar constant if it is constant, otherwise return None
    pub fn into_scalar(self) -> Option<F> {
        match self {
            PolyVariant::DenseUni(p) if p.degree() == 0 => p.coeffs.first().cloned(),
            PolyVariant::SparseUni(p) if p.degree() == 0 => {
                let dense: DensePolynomial<F> = p.into();
                dense.coeffs.first().cloned()
            }
            PolyVariant::DenseMle(mle) if mle.num_vars() == 0 => mle.evaluations.first().cloned(),
            PolyVariant::SparseMultivariate(p) if p.degree() == 0 && p.num_vars == 0 => {
                if p.terms.is_empty() {
                    Some(F::zero())
                } else if p.terms.len() == 1 {
                    p.terms.first().map(|(c, _term)| *c)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Convert to dense representation
    pub fn to_dense(&self) -> Self {
        match self {
            PolyVariant::DenseUni(_) | PolyVariant::DenseMle(_) => self.clone(),
            PolyVariant::SparseUni(p) => {
                let dense: DensePolynomial<F> = p.clone().into();
                PolyVariant::DenseUni(dense)
            }
            PolyVariant::SparseMultivariate(_) => self.clone(), // Already sparse, no dense equivalent
        }
    }

    /// Check if this is a virtual polynomial (always false for PolyVariant)
    pub fn is_virtual(&self) -> bool {
        false
    }

    /// Evaluate multivariate polynomial at a point
    pub fn evaluate_mv(&self, point: &[F]) -> Result<F, PolyError<F>> {
        match self {
            PolyVariant::DenseMle(mle) => {
                if point.len() != mle.num_vars() {
                    return Err(PolyError::DimensionMismatch {
                        polynomial: self.clone(),
                        expected: mle.num_vars(),
                        actual: point.len(),
                    });
                }
                Ok(mle.evaluate(&point.to_vec()))
            }
            PolyVariant::SparseMultivariate(p) => {
                if point.len() != p.num_vars {
                    return Err(PolyError::DimensionMismatch {
                        polynomial: self.clone(),
                        expected: p.num_vars,
                        actual: point.len(),
                    });
                }
                Ok(p.evaluate(&point.to_vec()))
            }
            PolyVariant::DenseUni(p) => {
                if point.len() != 1 {
                    return Err(PolyError::DimensionMismatch {
                        polynomial: self.clone(),
                        expected: 1,
                        actual: point.len(),
                    });
                }
                Ok(p.evaluate(&point[0]))
            }
            PolyVariant::SparseUni(p) => {
                if point.len() != 1 {
                    return Err(PolyError::DimensionMismatch {
                        polynomial: self.clone(),
                        expected: 1,
                        actual: point.len(),
                    });
                }
                Ok(p.evaluate(&point[0]))
            }
        }
    }

    // ========== Arithmetic Operations ==========

    /// Add two polynomials
    pub fn poly_add(&self, other: &Self) -> Result<Self, PolyError<F>> {
        match (self, other) {
            // Univariate + Univariate
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                Ok(PolyVariant::DenseUni(p1 + p2))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::SparseUni(p2)) => {
                Ok(PolyVariant::SparseUni(p1 + p2))
            }
            (PolyVariant::DenseUni(p1), PolyVariant::SparseUni(p2)) => {
                let dense2: DensePolynomial<F> = p2.clone().into();
                Ok(PolyVariant::DenseUni(p1 + &dense2))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::DenseUni(p2)) => {
                let dense1: DensePolynomial<F> = p1.clone().into();
                Ok(PolyVariant::DenseUni(&dense1 + p2))
            }

            // MLE + MLE
            (PolyVariant::DenseMle(m1), PolyVariant::DenseMle(m2)) => {
                if m1.num_vars() != m2.num_vars() {
                    return Err(PolyError::MleVariableMismatch {
                        v1: m1.num_vars(),
                        v2: m2.num_vars(),
                    });
                }
                Ok(PolyVariant::DenseMle(m1 + m2))
            }

            // MLE with 1 variable + Dense univariate
            (PolyVariant::DenseMle(mle), PolyVariant::DenseUni(p))
            | (PolyVariant::DenseUni(p), PolyVariant::DenseMle(mle)) => {
                if mle.num_vars() != 1 {
                    return Err(PolyError::VariableMismatch {
                        v1: self.clone(),
                        n1: mle.num_vars(),
                        v2: other.clone(),
                        n2: 1,
                    });
                }
                // Convert MLE to univariate polynomial as: y = mle(0) * (1 - x) + mle(1) * x
                let mle_as_uni = DensePolynomial::from_coefficients_vec(vec![
                    mle.evaluations[0],
                    mle.evaluations[1] - mle.evaluations[0],
                ]);
                Ok(PolyVariant::DenseUni(&mle_as_uni + p))
            }

            // MLE with 1 variable + Sparse Univariate
            (PolyVariant::DenseMle(mle), PolyVariant::SparseUni(p))
            | (PolyVariant::SparseUni(p), PolyVariant::DenseMle(mle)) => {
                if mle.num_vars() != 1 {
                    return Err(PolyError::VariableMismatch {
                        v1: self.clone(),
                        n1: mle.num_vars(),
                        v2: other.clone(),
                        n2: 1,
                    });
                }
                // Convert MLE to univariate polynomial as: y = mle(0) * (1 - x) + mle(1) * x
                let mle_as_uni = SparsePolynomial::from_coefficients_vec(vec![
                    (0, mle.evaluations[0]),
                    (1, mle.evaluations[1] - mle.evaluations[0]),
                ]);
                Ok(PolyVariant::SparseUni(&mle_as_uni + p))
            }

            // Sparse multivariate + Sparse multivariate
            (PolyVariant::SparseMultivariate(p1), PolyVariant::SparseMultivariate(p2)) => {
                if p1.num_vars != p2.num_vars {
                    return Err(PolyError::VariableMismatch {
                        v1: self.clone(),
                        n1: p1.num_vars,
                        v2: other.clone(),
                        n2: p2.num_vars,
                    });
                }
                Ok(PolyVariant::SparseMultivariate(p1 + p2))
            }

            _ => Err(PolyError::UnsupportedOperation {
                op: BinOp::Add,
                left: self.clone(),
                right: other.clone(),
            }),
        }
    }

    /// Add a scalar to a polynomial
    pub fn poly_add_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(p + &DensePolynomial::from_coefficients_vec(vec![scalar]))
            }
            PolyVariant::SparseMultivariate(p) => {
                // Add scalar as constant term - terms are (coeff, term)
                let const_term = MultiSparseTerm::new(vec![]);
                let p_scalar = SparseMultivariatePolynomial {
                    num_vars: p.num_vars,
                    terms: vec![(scalar, const_term)],
                };
                PolyVariant::SparseMultivariate(p + &p_scalar)
            }
            PolyVariant::SparseUni(p) => {
                let dense: DensePolynomial<F> = p.clone().into();
                PolyVariant::DenseUni(dense + &DensePolynomial::from_coefficients_vec(vec![scalar]))
            }
            PolyVariant::DenseMle(mle) => {
                let added_evals = mle.iter().map(|&eval| eval + scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                    mle.num_vars(),
                    added_evals,
                ))
            }
        }
    }

    /// Negate a polynomial
    pub fn poly_neg(&self) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                let neg_coeffs = p.coeffs.par_iter().map(|c| -*c).collect();
                PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(neg_coeffs))
            }
            PolyVariant::SparseUni(p) => {
                // Convert to dense, negate, keep as dense
                let dense: DensePolynomial<F> = p.clone().into();
                let neg_coeffs = dense.coeffs.iter().map(|c| -*c).collect();
                PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(neg_coeffs))
            }
            PolyVariant::DenseMle(mle) => {
                let neg_evals = mle.evaluations.par_iter().map(|&eval| -eval).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                    mle.num_vars(),
                    neg_evals,
                ))
            }
            PolyVariant::SparseMultivariate(p) => {
                let neg_terms: Vec<_> = p
                    .terms
                    .iter()
                    .map(|(coeff, term)| (-*coeff, term.clone()))
                    .collect();
                PolyVariant::SparseMultivariate(SparseMultivariatePolynomial {
                    num_vars: p.num_vars,
                    terms: neg_terms,
                })
            }
        }
    }
    /// Subtract two polynomials
    pub fn poly_sub(&self, other: &Self) -> Result<Self, PolyError<F>> {
        self.poly_add(&other.poly_neg())
    }

    /// Subtract scalar from polynomial
    pub fn poly_sub_scalar(&self, scalar: F) -> Self {
        self.poly_add_scalar(-scalar)
    }

    /// Subtract polynomial from scalar
    pub fn scalar_sub_poly(scalar: F, poly: &Self) -> Result<Self, PolyError<F>> {
        let scalar_poly = PolyVariant::from_scalar(scalar);
        scalar_poly.poly_sub(poly)
    }

    // TODO: Update the rest of this file
    /// Multiply two polynomials - always returns a VirtualPolynomial for any multiplication
    pub fn poly_mul(&self, other: &Self) -> Result<Self, PolyError<F>> {
        match (self, other) {
            // Univariate * Univariate
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                Ok(PolyVariant::DenseUni(p1.naive_mul(p2)))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::SparseUni(p2)) => {
                let dense1: DensePolynomial<F> = p1.clone().into();
                let dense2: DensePolynomial<F> = p2.clone().into();
                Ok(PolyVariant::DenseUni(dense1.naive_mul(&dense2)))
            }
            (PolyVariant::DenseUni(p1), PolyVariant::SparseUni(p2)) => {
                let dense2: DensePolynomial<F> = p2.clone().into();
                Ok(PolyVariant::DenseUni(p1.naive_mul(&dense2)))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::DenseUni(p2)) => {
                let dense1: DensePolynomial<F> = p1.clone().into();
                Ok(PolyVariant::DenseUni(dense1.naive_mul(p2)))
            }

            // MLE * _ - not directly supported, should use VirtualPolynomial
            (a @ PolyVariant::DenseMle(_), b) => Err(PolyError::MleMultiplication {
                v1: a.clone(),
                v2: b.clone(),
            }),
            (b, a @ PolyVariant::DenseMle(_)) => Err(PolyError::MleMultiplication {
                v1: a.clone(),
                v2: b.clone(),
            }),

            // Sparse multivariate * Sparse multivariate - not directly supported
            (PolyVariant::SparseMultivariate(_), PolyVariant::SparseMultivariate(_)) => {
                Err(PolyError::UnsupportedOperation {
                    op: BinOp::Mul,
                    left: self.clone(),
                    right: other.clone(),
                })
            }

            _ => Err(PolyError::UnsupportedOperation {
                op: BinOp::Mul,
                left: self.clone(),
                right: other.clone(),
            }),
        }
    }

    /// Multiply polynomial by scalar
    pub fn poly_mul_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) => PolyVariant::DenseUni(p * scalar),
            PolyVariant::SparseUni(p) => PolyVariant::SparseUni(p * scalar),
            PolyVariant::DenseMle(mle) => {
                let mul_evals = mle.iter().map(|&eval| eval * scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                    mle.num_vars(),
                    mul_evals,
                ))
            }
            PolyVariant::SparseMultivariate(p) => {
                let scaled_terms: Vec<_> = p
                    .terms
                    .iter()
                    .map(|(c, t)| ((*c) * scalar, t.clone()))
                    .collect();
                PolyVariant::SparseMultivariate(SparseMultivariatePolynomial {
                    num_vars: p.num_vars,
                    terms: scaled_terms,
                })
            }
        }
    }

    /// Divide two polynomials
    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError<F>>
    where
        F: PrimeField,
    {
        match (self, other) {
            // Univariate / Univariate - use ark_poly's divide_with_q_and_r
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                if p2.is_zero() {
                    return Err(PolyError::DivisionByZero { v: other.clone() });
                }
                // Use ark_poly's polynomial division via DenseOrSparsePolynomial
                let dividend = DenseOrSparsePolynomial::from(p1.clone());
                let divisor = DenseOrSparsePolynomial::from(p2.clone());
                let (quotient, _remainder) = dividend
                    .divide_with_q_and_r(&divisor)
                    .ok_or(PolyError::DivisionByZero { v: other.clone() })?;
                Ok(PolyVariant::DenseUni(quotient))
            }

            // MLE division not supported
            (a @ PolyVariant::DenseMle(_), b) | (a, b @ PolyVariant::DenseMle(_)) => {
                Err(PolyError::DivisionNotApplicable {
                    v1: a.clone(),
                    v2: b.clone(),
                })
            }

            // Sparse multivariate division not supported
            (a @ PolyVariant::SparseMultivariate(_), b)
            | (a, b @ PolyVariant::SparseMultivariate(_)) => {
                Err(PolyError::DivisionNotApplicable {
                    v1: a.clone(),
                    v2: b.clone(),
                })
            }

            // Sparse univariate - convert to dense first
            _ => self.to_dense().poly_div(&other.to_dense()),
        }
    }

    /// Divide polynomial by scalar
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>> {
        if scalar.is_zero() {
            return Err(PolyError::DivisionByZero { v: self.clone() });
        }

        match self {
            PolyVariant::DenseUni(p) => {
                let inv_scalar = scalar
                    .inverse()
                    .ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                Ok(PolyVariant::DenseUni(p * inv_scalar))
            }
            PolyVariant::SparseUni(p) => {
                let inv_scalar = scalar
                    .inverse()
                    .ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                Ok(PolyVariant::SparseUni(p * inv_scalar))
            }
            PolyVariant::DenseMle(mle) => {
                let inv_scalar = scalar
                    .inverse()
                    .ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                let div_evals = mle.iter().map(|&eval| eval * inv_scalar).collect();
                Ok(PolyVariant::DenseMle(
                    DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), div_evals),
                ))
            }
            PolyVariant::SparseMultivariate(p) => {
                let inv_scalar = scalar
                    .inverse()
                    .ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                let scaled_terms: Vec<_> = p
                    .terms
                    .iter()
                    .map(|(c, t)| ((*c) * inv_scalar, t.clone()))
                    .collect();
                Ok(PolyVariant::SparseMultivariate(
                    SparseMultivariatePolynomial {
                        num_vars: p.num_vars,
                        terms: scaled_terms,
                    },
                ))
            }
        }
    }

    /// Polynomial remainder (modulo)
    pub fn poly_rem(&self, other: &Self) -> Result<Self, PolyError<F>>
    where
        F: PrimeField,
    {
        match (self, other) {
            // Univariate % Univariate - use ark_poly's divide_with_q_and_r
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                if p2.is_zero() {
                    return Err(PolyError::DivisionByZero { v: other.clone() });
                }
                // Use ark_poly's polynomial division to get the remainder
                let dividend = DenseOrSparsePolynomial::from(p1.clone());
                let divisor = DenseOrSparsePolynomial::from(p2.clone());
                let (_quotient, remainder) = dividend
                    .divide_with_q_and_r(&divisor)
                    .ok_or(PolyError::DivisionByZero { v: other.clone() })?;
                Ok(PolyVariant::DenseUni(remainder))
            }

            // MLE modulo not supported
            (PolyVariant::DenseMle(_), _)
            | (_, PolyVariant::DenseMle(_))
            | (PolyVariant::SparseMultivariate(_), _)
            | (_, PolyVariant::SparseMultivariate(_)) => Err(PolyError::ModuloNotApplicable),

            // Sparse - convert to dense first
            _ => self.to_dense().poly_rem(&other.to_dense()),
        }
    }

    /// Evaluate MLE at a boolean hypercube point
    pub fn evaluate_mle(&self, point: &[F]) -> Result<F, PolyError<F>> {
        match self {
            PolyVariant::DenseMle(mle) => {
                if point.len() != mle.num_vars() {
                    return Err(PolyError::DimensionMismatch {
                        polynomial: self.clone(),
                        expected: mle.num_vars(),
                        actual: point.len(),
                    });
                }
                Ok(mle.evaluate(&point.to_vec()))
            }
            _ => Err(PolyError::NotMlePolynomial),
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
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                    num_vars, padded,
                ))
            }
            PolyVariant::SparseUni(p) => {
                let vals: Vec<F> = points.iter().map(|pt| p.evaluate(pt)).collect();
                // Return as MLE with log2(n) variables
                let num_vars = (vals.len() as f64).log2().ceil() as usize;
                let mut padded = vals.clone();
                padded.resize(1 << num_vars, F::zero());
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                    num_vars, padded,
                ))
            }
            _ => panic!("evaluate_vec only works for univariate polynomials"),
        }
    }

    /// Evaluate or partially fix MLE variables
    /// Always returns a polynomial (possibly constant after full evaluation)
    pub fn evaluate_or_fix_mle(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        match self {
            PolyVariant::DenseMle(mle) => {
                if points.len() < mle.num_vars() {
                    // Partial evaluation - fix first k variables.
                    // ark_poly::DenseMultilinearExtension::fix_variables is
                    // single-threaded; replicate hyperplonk's parallel form.
                    let fixed = fix_first_variables_parallel(mle, points);
                    Ok(PolyVariant::DenseMle(fixed))
                } else if points.len() == mle.num_vars() {
                    // Full evaluation - return as constant polynomial
                    let val = mle.evaluate(&points.to_vec());
                    Ok(Self::from_scalar(val))
                } else {
                    Err(PolyError::DimensionMismatch {
                        polynomial: self.clone(),
                        expected: mle.num_vars(),
                        actual: points.len(),
                    })
                }
            }
            _ => Err(PolyError::RequiresMle),
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
            PolyVariant::SparseMultivariate(p) => {
                3u8.serialize_compressed(&mut writer)?;
                p.serialize_compressed(&mut writer)
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
            (PolyVariant::SparseMultivariate(a), PolyVariant::SparseMultivariate(b)) => {
                a.num_vars == b.num_vars && a == b
            }
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
            (PolyVariant::DenseUni(_), PolyVariant::DenseUni(_))
            | (PolyVariant::SparseUni(_), PolyVariant::SparseUni(_))
            | (PolyVariant::DenseUni(_), PolyVariant::SparseUni(_))
            | (PolyVariant::SparseUni(_), PolyVariant::DenseUni(_)) => {
                // Convert both to dense for comparison
                let self_dense = self.to_dense();
                let other_dense = other.to_dense();

                if let (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) =
                    (self_dense, other_dense)
                {
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

            // Both MLE or Multivariate
            (PolyVariant::DenseMle(_), PolyVariant::DenseMle(_)) => {
                // Convert both to dense for comparison
                let self_dense = self.to_dense();
                let other_dense = other.to_dense();

                if let (PolyVariant::DenseMle(m1), PolyVariant::DenseMle(m2)) =
                    (self_dense, other_dense)
                {
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

            // Uni < Mle < Sparse Multivariate
            (PolyVariant::DenseUni(_), PolyVariant::DenseMle(_))
            | (PolyVariant::SparseUni(_), PolyVariant::DenseMle(_))
            | (PolyVariant::DenseUni(_), PolyVariant::SparseMultivariate(_))
            | (PolyVariant::SparseUni(_), PolyVariant::SparseMultivariate(_)) => Ordering::Less,

            (PolyVariant::DenseMle(_), PolyVariant::SparseMultivariate(_)) => Ordering::Less,

            // Mle > Uni, Sparse Multivariate > all
            _ => Ordering::Greater,
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
            PolyVariant::SparseMultivariate(p) => write!(
                f,
                "SparseMultivariate(nvars={}, nterms={})",
                p.num_vars,
                p.terms.len()
            ),
        }
    }
}
