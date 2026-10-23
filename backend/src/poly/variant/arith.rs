//! Arithmetic on [`PolyVariant`], by what each operand is: univariate, multilinear (either
//! table encoding, see `mle`) or sparse multivariate. A univariate result is dense, except
//! that the sum of two sparse univariates stays sparse.

use crate::Field;
use lang::ast::BinOp;
use rayon::prelude::*;

use super::{DenseUni, Multivariate, PolyError, PolyVariant, SparseUni, Term, mle, mle::Table};

impl<F: Field> PolyVariant<F> {
    /// Add two polynomials. A one-variable MLE added to a univariate polynomial is the line
    /// through its two values.
    ///
    /// # Errors
    /// Returns [`PolyError::MleVariableMismatch`] or
    /// [`PolyError::VariableMismatch`] when the operands disagree on their
    /// variable count, and [`PolyError::UnsupportedOperation`] for kinds
    /// with no addition rule (for example an MLE plus a sparse multivariate).
    pub fn poly_add(&self, other: &Self) -> Result<Self, PolyError<F>> {
        use PolyVariant::{SparseMultivariate, SparseUni};
        if let (SparseUni(a), SparseUni(b)) = (self, other) {
            return Ok(SparseUni(a.add(b)));
        }
        if let (Some(a), Some(b)) = (self.dense_uni(), other.dense_uni()) {
            return Ok(PolyVariant::DenseUni(a.add(&b)));
        }
        match (self.mle_table(), other.mle_table()) {
            (Some((n1, a)), Some((n2, b))) => {
                if n1 != n2 {
                    return Err(PolyError::MleVariableMismatch { v1: n1, v2: n2 });
                }
                return Ok(mle::add(n1, a, b));
            }
            (Some((num_vars, table)), None) | (None, Some((num_vars, table)))
                if self.is_univariate() || other.is_univariate() =>
            {
                if num_vars != 1 {
                    return Err(PolyError::VariableMismatch {
                        v1: self.clone(),
                        n1: num_vars,
                        v2: other.clone(),
                        n2: 1,
                    });
                }
                let uni = if self.is_univariate() { self } else { other };
                return line(table, matches!(uni, SparseUni(_))).poly_add(uni);
            }
            _ => {}
        }
        match (self, other) {
            (SparseMultivariate(p1), SparseMultivariate(p2)) if p1.num_vars() != p2.num_vars() => {
                Err(PolyError::VariableMismatch {
                    v1: self.clone(),
                    n1: p1.num_vars(),
                    v2: other.clone(),
                    n2: p2.num_vars(),
                })
            }
            (SparseMultivariate(p1), SparseMultivariate(p2)) => Ok(SparseMultivariate(p1.add(p2))),
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
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => {
                PolyVariant::DenseUni(self.dense_uni().unwrap().add(&DenseUni::new(vec![scalar])))
            }
            PolyVariant::SparseMultivariate(p) => {
                let constant = Multivariate::new(p.num_vars(), vec![(scalar, Term::default())]);
                PolyVariant::SparseMultivariate(p.add(&constant))
            }
            PolyVariant::DenseMle(mle) => mle::dense_mle(
                mle.num_vars(),
                mle.evals().iter().map(|&eval| eval + scalar).collect(),
            ),
            // Adding zero keeps the entries; anything else makes every unlisted entry non-zero.
            PolyVariant::SparseMle { .. } if scalar.is_zero() => self.clone(),
            PolyVariant::SparseMle { .. } => self.to_dense().poly_add_scalar(scalar),
        }
    }

    /// The same polynomial with `f` applied to every stored coefficient or
    /// evaluation, in the same encoding. `f` must map zero to zero, so
    /// unstored (zero) entries stay correct.
    fn map_values(&self, f: impl Fn(F) -> F + Sync + Send) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::from_coeffs(p.coeffs().par_iter().map(|&c| f(c)).collect())
            }
            PolyVariant::SparseUni(p) => PolyVariant::SparseUni(SparseUni::new(
                p.terms().iter().map(|&(d, c)| (d, f(c))).collect(),
            )),
            PolyVariant::DenseMle(mle) => mle::dense_mle(
                mle.num_vars(),
                mle.evals().par_iter().map(|&e| f(e)).collect(),
            ),
            PolyVariant::SparseMultivariate(p) => PolyVariant::SparseMultivariate(p.map_coeffs(f)),
            PolyVariant::SparseMle { num_vars, evals } => PolyVariant::SparseMle {
                num_vars: *num_vars,
                evals: evals.iter().map(|&(i, v)| (i, f(v))).collect(),
            },
        }
    }

    /// Negate a polynomial
    pub fn poly_neg(&self) -> Self {
        self.map_values(|v| -v)
    }

    /// Subtract two polynomials
    ///
    /// # Errors
    /// Propagates the errors of [`Self::poly_add`] applied to the negated
    /// right-hand operand.
    pub fn poly_sub(&self, other: &Self) -> Result<Self, PolyError<F>> {
        self.poly_add(&other.poly_neg())
    }

    /// Subtract scalar from polynomial
    pub fn poly_sub_scalar(&self, scalar: F) -> Self {
        self.poly_add_scalar(-scalar)
    }

    /// Subtract polynomial from scalar
    ///
    /// # Errors
    /// Propagates the errors of [`Self::poly_sub`] with the scalar lifted to a
    /// degree-0 univariate polynomial.
    pub fn scalar_sub_poly(scalar: F, poly: &Self) -> Result<Self, PolyError<F>> {
        PolyVariant::from_scalar(scalar).poly_sub(poly)
    }

    /// Multiply two univariate polynomials (by FFT when both are long, see
    /// [`DenseUni::mul`]).
    ///
    /// # Errors
    /// Returns [`PolyError::MleMultiplication`] if either operand is a multilinear extension
    /// (the product is no longer multilinear; build a `VirtualPolynomial` instead), and
    /// [`PolyError::UnsupportedOperation`] for a sparse multivariate operand.
    pub fn poly_mul(&self, other: &Self) -> Result<Self, PolyError<F>> {
        if let (Some(a), Some(b)) = (self.dense_uni(), other.dense_uni()) {
            return Ok(PolyVariant::DenseUni(a.mul(&b)));
        }
        if self.mle_table().is_some() || other.mle_table().is_some() {
            let (v1, v2) = if self.mle_table().is_some() {
                (self, other)
            } else {
                (other, self)
            };
            return Err(PolyError::MleMultiplication {
                v1: v1.clone(),
                v2: v2.clone(),
            });
        }
        Err(PolyError::UnsupportedOperation {
            op: BinOp::Mul,
            left: self.clone(),
            right: other.clone(),
        })
    }

    /// Multiply polynomial by scalar
    pub fn poly_mul_scalar(&self, scalar: F) -> Self {
        self.map_values(|v| v * scalar)
    }

    /// The quotient of two univariate polynomials, the remainder dropped.
    ///
    /// # Errors
    /// Returns [`PolyError::DivisionByZero`] if the divisor is the zero
    /// polynomial, and [`PolyError::DivisionNotApplicable`] if either operand
    /// is multivariate.
    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError<F>> {
        let (Some(a), Some(b)) = (self.dense_uni(), other.dense_uni()) else {
            return Err(PolyError::DivisionNotApplicable {
                v1: self.clone(),
                v2: other.clone(),
            });
        };
        let (quotient, _) = a
            .div_rem(&b)
            .ok_or_else(|| PolyError::DivisionByZero { v: other.clone() })?;
        Ok(PolyVariant::DenseUni(quotient))
    }

    /// Divide polynomial by scalar
    ///
    /// # Errors
    /// Returns [`PolyError::DivisionByZero`] if `scalar` is zero.
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>> {
        let inv = scalar
            .inverse()
            .ok_or_else(|| PolyError::DivisionByZero { v: self.clone() })?;
        Ok(self.poly_mul_scalar(inv))
    }
}

/// The one-variable MLE `table` as the univariate line through its values at 0 and 1,
/// `f(0) + (f(1) - f(0))·x`, sparse if `sparse`.
fn line<F: Field>(table: Table<'_, F>, sparse: bool) -> PolyVariant<F> {
    let [f0, f1] = match table {
        Table::Dense(values) => [values[0], values[1]],
        Table::Sparse(entries) => entries.iter().fold([F::zero(); 2], |mut at, &(i, v)| {
            at[i] += v;
            at
        }),
    };
    if sparse {
        PolyVariant::SparseUni(SparseUni::new(vec![(0, f0), (1, f1 - f0)]))
    } else {
        PolyVariant::from_coeffs(vec![f0, f1 - f0])
    }
}
