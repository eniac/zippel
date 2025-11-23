use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{
    DenseUVPolynomial, Polynomial,
    univariate::{DensePolynomial, SparsePolynomial, DenseOrSparsePolynomial},
    DenseMultilinearExtension, MultilinearExtension,
    multivariate::{SparsePolynomial as MultiSparsePolynomial, SparseTerm as MultiSparseTerm},
    evaluations::multivariate::multilinear::SparseMultilinearExtension,
};
use ark_serialize::{CanonicalSerialize, SerializationError};
use std::io::Write;
use std::fmt;
use thiserror::Error;

/// Type alias for sparse multivariate polynomial
type SparseMultivariatePolynomial<F> = MultiSparsePolynomial<F, MultiSparseTerm>;

#[derive(Error, Debug, Clone)]
pub enum PolyError<F: Field> {
    #[error("Unsupported polynomial operation:\n\t{left} {op} {right}")]
    UnsupportedOperation { op: BinOp, left: PolyVariant<F>, right: PolyVariant<F> },

    #[error("Division by zero:\n\t{v1} / {v2}")]
    DivisionByZero { v1: PolyVariant<F>, v2: PolyVariant<F> },

    #[error("Can only divide scalar by constant polynomial:\n\t{scalar} / { polynomial }")]
    ScalarDivByNonConstant { scalar: F, polynomial: PolyVariant<F> },

    #[error("Cannot convert non-constant polynomial {0} to scalar")]
    NotConstantPolynomial(PolyVariant<F>),

    #[error("Cannot perform operation on multivariate polynomial with different number of variables:\n\t{v1} has {n1}, while {v2} has {n2}")]
    VariableMismatch { v1: PolyVariant<F>, n1: usize, v2: PolyVariant<F>, n2: usize },

    #[error("Evaluation point dimension mismatch:\n\t{polynomial} has {expected} variables, but received {actual}")]
    DimensionMismatch { polynomial: PolyVariant<F>, expected: usize, actual: usize },
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
    /// Sparse multivariate polynomial
    SparseMultivariate(SparseMultivariatePolynomial<F>),
}

impl Polynomial<F> for PolyVariant<F> {
    type Point = Vec<F>;
    fn degree(&self) -> usize {
        match self {
            PolyVariant::DenseUni(p) => p.degree(),
            PolyVariant::SparseUni(p) => p.degree(),
            PolyVariant::DenseMle(_) => 1,
            PolyVariant::SparseMultivariate(p) => p.degree(),
        }
    }

    /// Evaluate polynomial at a point
    fn evaluate(&self, point: &Vec<F>) -> F {
        match self {
            // A little hackish - univariate polynomials evaluate over a single Field element
            PolyVariant::DenseUni(p) => p.evaluate(point[0]),
            PolyVariant::SparseUni(p) => p.evaluate(point[0]),
            PolyVariant::DenseMle(p) =>
                if points.len() != p.num_vars() {
                    panic!("Evaluation point dimension mismatch:\n\t MLE {} expected {}, got {}", p, p.num_vars(), points.len());
                } else {
                    p.evaluate(points)
                },
            PolyVariant::SparseMultivariate(p) =>
                if points.len() != p.num_vars {
                    panic!("Evaluation point dimension mismatch:\n\t Sparse multivariate {} expected {}, got {}", p, p.num_vars, points.len());
                } else {
                    p.evaluate(points),
                }
        }
    }
}

impl<F: Field> PolyVariant<F> {
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
            PolyVariant::DenseMle(mle) => true,
            PolyVariant::SparseMultivariate(p) => p.degree() == 1,
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => false,
        }
    }

    /// Check if this is a multivariate polynomial
    pub fn is_multivariate(&self) -> bool {
        matches!(self, PolyVariant::DenseMle(_) | PolyVariant::SparseMultivariate(_))
    }

    /// Try to convert univariate degree-0 polynomial to scalar
    pub fn try_to_scalar(&self) -> Option<F> {
        match self {
            PolyVariant::DenseUni(p) if p.degree() == 0 => p.coeffs.first().cloned(),
            PolyVariant::SparseUni(p) if p.degree() == 0 => {
                // Convert to dense to access coefficients
                let dense: DensePolynomial<F> = p.clone().into();
                dense.coeffs.first().cloned()
            },
            PolyVariant::DenseMle(mle) if mle.num_vars() == 0 => mle.evaluations.first().cloned(),
            PolyVariant::SparseMle(mle) if mle.num_vars == 0 => {
                mle.evaluations.get(&0).cloned()
            },
            _ => None,
        }
    }

    /// Convert to vector of evaluations or coefficients
    pub fn to_vec(&self) -> Option<Vec<F>> {
        match self {
            PolyVariant::DenseMle(mle) => Some(mle.evaluations.clone()),
            PolyVariant::DenseUni(p) => Some(p.coeffs.clone()),
            PolyVariant::SparseUni(p) => Some(p.to_dense().coeffs),
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
            _ => None
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
                        v2: m2.num_vars()
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
                        n2: 1
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
                        n2: 1
                    });
                }
                // Convert MLE to univariate polynomial as: y = mle(0) * (1 - x) + mle(1) * x
                let mle_as_uni = SparsePolynomial::from_coefficients_vec(vec![
                    (0, mle.evaluations[0]),
                    (1, mle.evaluations[1] - mle.evaluations[0]),
                ]);
                Ok(PolyVariant::SparseUni(&mle_as_uni + &p))
            }

            // Sparse multivariate + Sparse multivariate
            (PolyVariant::SparseMultivariate(p1), PolyVariant::SparseMultivariate(p2)) => {
                if p1.num_vars != p2.num_vars {
                    return Err(PolyError::VariableMismatch {
                        v1: self.clone(),
                        n1: p1.num_vars,
                        v2: other.clone(),
                        n2: p2.num_vars
                    });
                }
                Ok(PolyVariant::SparseMultivariate(p1 + p2))
            }

            _ => Err(PolyError::UnsupportedOperation {
                op: BinOp::Add,
                left: self.clone(),
                right: other.clone()
            }),
        }
    }

    /// Add a scalar to a polynomial
    pub fn poly_add_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(p + &DensePolynomial::from_coefficients_vec(vec![scalar]))
            },
            PolyVariant::SparseMultivariate(p) => {
                let p_scalar = SparseMultivariate::from_coefficients_vec(vec![(0, scalar)]);
                PolyVariant::SparseMultivariate(p + &p_scalar)
            },
            PolyVariant::SparseUni(p) => {
                let dense: DensePolynomial<F> = p.clone().into();
                PolyVariant::DenseUni(dense + &DensePolynomial::from_coefficients_vec(vec![scalar]))
            },
            PolyVariant::DenseMle(mle) => {
                let added_evals = mle.iter().map(|&eval| eval + scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), added_evals))
            },
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
                let neg_evals = mle.par_iter().map(|&eval| -eval).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), neg_evals))
            }
            PolyVariant::SparseMle(mle) => {
                // Convert to dense, negate
                let dense_evals: Vec<F> = mle.to_evaluations();
                let neg_evals = dense_evals.par_iter().map(|&eval| -eval).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars, neg_evals))
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
        match poly {
            PolyVariant::DenseUni(p) => {
                let dense = DensePolynomial::from_coefficients_vec(vec![scalar]);
                Ok(PolyVariant::DenseUni(dense.poly_sub(p)?))
            },
            PolyVariant::DenseMle(mle) => {
                let sub_evals = mle.iter().map(|&eval| scalar - eval).collect();
                Ok(PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), sub_evals)))
            },
            PolyVariant::SparseUni(p) => {
                let sparse = SparsePolynomial::from_coefficients_vec(vec![(scalar)]);
                Ok(PolyVariant::SparseUni(sparse.poly_sub(p)?))
            },
            PolyVariant::SparseMultivariate(p) => {
                let sparse_scalar = SparseMultivariatePolynomial::from_coefficients_vec(vec![(0, scalar)]);
                Ok(PolyVariant::SparseMultivariate(sparse_scalar.poly_sub(p)?))
            }
        }
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

            // MLE * _
            (a@PolyVariant::DenseMle(_), b)
            | (a@PolyVariant::SparseMle(_), b) =>
                Err(PolyError::MleMultiplication { v1: a.clone(), v2: b.clone() }),
            (b, a@PolyVariant::DenseMle(_))
            | (b, a@PolyVariant::SparseMle(_))  =>
                Err(PolyError::MleMultiplication { v1: a.clone(), v2: b.clone() }),
        }
    }


    /// Multiply polynomial by scalar
    pub fn poly_mul_scalar(&self, scalar: F) -> Self {
        match self {
            PolyVariant::DenseUni(p) =>
                PolyVariant::DenseUni(p * scalar),
            PolyVariant::SparseUni(p) =>
                PolyVariant::SparseUni(p * scalar),
            PolyVariant::DenseMle(mle) => {
                let mul_evals = mle.iter().map(|&eval| eval * scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), mul_evals))
            },
            PolyVariant::SparseMle(mle) => {
                // Convert to dense, multiply
                let dense_evals: Vec<F> = mle.to_evaluations();
                let mul_evals = dense_evals.iter().map(|&eval| eval * scalar).collect();
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars, mul_evals))
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
                let (quotient, _remainder) = dividend.divide_with_q_and_r(&divisor)
                    .ok_or(PolyError::DivisionByZero { v: other.clone() })?;
                Ok(PolyVariant::DenseUni(quotient))
            }

            // MLE division not supported
            (a@PolyVariant::DenseMle(_), b) |
            (a@PolyVariant::SparseMle(_), b) |
            (a, b@PolyVariant::DenseMle(_)) |
            (a, b@PolyVariant::SparseMle(_)) => {
                Err(PolyError::DivisionNotApplicable { v1: a.clone(), v2: b.clone() })
            }

            // Sparse univariate - convert to dense first
            _ => {
                self.to_dense().poly_div(&other.to_dense())
            }
        }
    }

    /// Divide polynomial by scalar
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>> {
        if scalar.is_zero() {
            return Err(PolyError::DivisionByZero { v: self.clone() });
        }

        match self {
            PolyVariant::DenseUni(p) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                Ok(PolyVariant::DenseUni(p * inv_scalar))
            }
            PolyVariant::SparseUni(p) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                Ok(PolyVariant::SparseUni(p * inv_scalar))
            }
            PolyVariant::DenseMle(mle) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                let div_evals = mle.iter().map(|&eval| eval * inv_scalar).collect();
                Ok(PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars(), div_evals)))
            }
            PolyVariant::SparseMle(mle) => {
                let inv_scalar = scalar.inverse().ok_or(PolyError::DivisionByZero { v: self.clone() })?;
                let dense_evals: Vec<F> = mle.to_evaluations();
                let div_evals = dense_evals.iter().map(|&eval| eval * inv_scalar).collect();
                Ok(PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(mle.num_vars, div_evals)))
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
                let (_quotient, remainder) = dividend.divide_with_q_and_r(&divisor)
                    .ok_or(PolyError::DivisionByZero { v: other.clone() })?;
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


    /// Evaluate MLE at a boolean hypercube point
    pub fn evaluate_mle(&self, point: &[F]) -> Result<F, PolyError<F>> {
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
            _ => panic!("evaluate_vec only works for univariate polynomials")
        }
    }

    /// Evaluate or partially fix MLE variables
    /// Always returns a polynomial (possibly constant after full evaluation)
    pub fn evaluate_or_fix_mle(&self, points: &[F]) -> Result<Self, PolyError<F>> {
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

            // Uni < Mle
            (PolyVariant::DenseUni(_), PolyVariant::DenseMle(_)) |
            (PolyVariant::DenseUni(_), PolyVariant::SparseMle(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::DenseMle(_)) |
            (PolyVariant::SparseUni(_), PolyVariant::SparseMle(_)) => Ordering::Less,

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
        }
    }
}
