//! Polynomials as runtime values: univariate (dense or sparse coefficients), multilinear
//! (dense or sparse evaluation tables) and general sparse multivariate.
//!
//! - `mle`: the evaluation-table algorithms behind both MLE encodings.
//! - `multivariate`: fixing variables of a sparse multivariate polynomial.
//! - `arith`: arithmetic, dispatched on what a polynomial is (univariate, multilinear,
//!   multivariate) rather than on how it is stored.
//! - `ord`: a total order, consistent with the derived equality.

mod arith;
mod error;
mod mle;
mod multivariate;
mod ord;

use ark_ff::Field;
use ark_poly::{
    DenseMultilinearExtension, DenseUVPolynomial, MultilinearExtension, Polynomial,
    univariate::{DensePolynomial, SparsePolynomial},
};
use ark_serialize::{CanonicalSerialize, SerializationError};
use lang::typ::CRange;
use std::borrow::Cow;
use std::fmt;
use std::io::Write;

pub use error::PolyError;
use mle::Table;
use multivariate::Multivariate;

/// Polynomial types supported by the backend. Equality is structural: the same encoding
/// with the same contents.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PolyVariant<F: Field> {
    /// Dense univariate polynomial
    DenseUni(DensePolynomial<F>),
    /// Sparse univariate polynomial
    SparseUni(SparsePolynomial<F>),
    /// Dense multilinear extension
    DenseMle(DenseMultilinearExtension<F>),
    /// Sparse multivariate polynomial
    SparseMultivariate(Multivariate<F>),
    /// Sparse multilinear extension in **evaluation form**: a list of
    /// `(boolean_index, value)` pairs interpreted as the MLE of a function
    /// `f: {0,1}^num_vars → F` with `f(i) = value` for each listed pair and
    /// `f(i) = 0` elsewhere (an index listed twice takes the sum). Indices are
    /// LSB-first (variable 0 is the low bit of the index). Designed for
    /// Spartan-style R1CS matrices, where `num_vars` is `2·log(N)` but only
    /// ~3·N entries are non-zero — full evaluation and partial evaluation
    /// run in `O(|evals| · num_vars)` rather than `O(2^num_vars)`. A result
    /// that may or may not stay sparse (partial or selected evaluation, the
    /// sum of two sparse MLEs) is encoded by its density; other arithmetic
    /// goes through the dense table.
    SparseMle {
        /// Number of boolean variables of the underlying function; the dense
        /// evaluation table this stands for would have `2^num_vars` entries.
        num_vars: usize,
        /// Non-zero entries as `(boolean_index, value)` pairs; all unlisted
        /// indices evaluate to zero.
        evals: Vec<(usize, F)>,
    },
}

/// Checks a selected evaluation's shape: `free_range` is a non-empty unit-step
/// range inside `input_num_vars`, and `fixed_len` covers every other variable.
pub(crate) fn check_free_range<F: Field>(
    input_num_vars: usize,
    free_range: &CRange,
    fixed_len: usize,
) -> Result<(), PolyError<F>> {
    let free_len = free_range.len();
    if free_range.step() != 1
        || free_range.start() >= free_range.end()
        || free_range.end() > input_num_vars
        || fixed_len != input_num_vars - free_len
    {
        return Err(PolyError::DimensionMismatch {
            expected: input_num_vars.saturating_sub(free_len),
            actual: fixed_len,
        });
    }
    Ok(())
}

/// The position of variable `var` among the fixed values of a selected evaluation, which list
/// the variables before `free_range` and then those after it; `None` for a free variable.
fn fixed_index_for_var(free_range: &CRange, var: usize) -> Option<usize> {
    if var < free_range.start() {
        Some(var)
    } else if var >= free_range.end() {
        Some(free_range.start() + (var - free_range.end()))
    } else {
        None
    }
}

impl<F: Field> PolyVariant<F> {
    /// Create a polynomial from coefficients (univariate)
    pub fn from_coeffs(coeffs: Vec<F>) -> Self {
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(coeffs))
    }

    /// Create a polynomial from a scalar constant
    pub fn from_scalar(scalar: F) -> Self {
        // Return as degree-0 univariate polynomial
        PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![scalar]))
    }

    /// A univariate polynomial's dense coefficients, borrowed when already dense.
    fn dense_uni(&self) -> Option<Cow<'_, DensePolynomial<F>>> {
        match self {
            PolyVariant::DenseUni(p) => Some(Cow::Borrowed(p)),
            PolyVariant::SparseUni(p) => Some(Cow::Owned(p.clone().into())),
            _ => None,
        }
    }

    /// A multilinear extension's variable count and evaluation table.
    fn mle_table(&self) -> Option<(usize, Table<'_, F>)> {
        match self {
            PolyVariant::DenseMle(mle) => Some((mle.num_vars, Table::Dense(&mle.evaluations))),
            PolyVariant::SparseMle { num_vars, evals } => Some((*num_vars, Table::Sparse(evals))),
            _ => None,
        }
    }

    /// Get the degree of the polynomial
    pub fn degree(&self) -> usize {
        match self {
            PolyVariant::DenseUni(p) => p.degree(),
            PolyVariant::SparseUni(p) => p.degree(),
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. } => 1,
            PolyVariant::SparseMultivariate(p) => p.degree(),
        }
    }

    /// An upper bound on the total degree, read from the representation
    /// rather than its bookkeeping (a dense univariate's coefficient count, a
    /// sparse one's largest index): unlike [`Self::degree`], an MLE counts
    /// as its variable count, and a malformed sparse univariate cannot
    /// understate it.
    pub fn total_degree_bound(&self) -> usize {
        use ark_poly::multivariate::Term;
        match self {
            PolyVariant::DenseUni(p) => p.coeffs.len().saturating_sub(1),
            PolyVariant::SparseUni(p) => p.iter().map(|(i, _)| *i).max().unwrap_or(0),
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. } => self.num_vars(),
            PolyVariant::SparseMultivariate(p) => {
                p.terms.iter().map(|(_, t)| t.degree()).max().unwrap_or(0)
            }
        }
    }

    /// Whether the representation is consistent: a dense MLE has
    /// `2^num_vars` evaluations, and a sparse MLE's indices and a sparse
    /// multivariate's variables are in range. Arithmetic assumes this, and
    /// the arkworks types' fields are public, so a value from outside (a
    /// proof) is checked.
    pub fn is_well_formed(&self) -> bool {
        let table_len = |num_vars: usize| 1usize.checked_shl(u32::try_from(num_vars).ok()?);
        match self {
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => true,
            PolyVariant::DenseMle(mle) => table_len(mle.num_vars) == Some(mle.evaluations.len()),
            PolyVariant::SparseMle { num_vars, evals } => {
                table_len(*num_vars).is_some_and(|len| evals.iter().all(|(i, _)| *i < len))
            }
            PolyVariant::SparseMultivariate(p) => p
                .terms
                .iter()
                .all(|(_, term)| term.iter().all(|(var, _)| *var < p.num_vars)),
        }
    }

    /// The number of variables: 1 for a univariate polynomial.
    pub fn num_vars(&self) -> usize {
        match self {
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => 1,
            PolyVariant::DenseMle(mle) => mle.num_vars,
            PolyVariant::SparseMle { num_vars, .. } => *num_vars,
            PolyVariant::SparseMultivariate(p) => p.num_vars,
        }
    }

    /// Check if this is a univariate polynomial
    pub fn is_univariate(&self) -> bool {
        matches!(self, PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_))
    }

    /// Check if this is a multilinear polynomial
    pub fn is_multilinear(&self) -> bool {
        match self {
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. } => true,
            PolyVariant::SparseMultivariate(p) => p.degree() == 1,
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => false,
        }
    }

    /// Check if this is a multivariate polynomial
    pub fn is_multivariate(&self) -> bool {
        !self.is_univariate()
    }

    /// Check if polynomial is zero
    pub fn is_zero(&self) -> bool {
        use ark_ff::Zero;
        match self {
            PolyVariant::DenseUni(p) => p.is_zero(),
            PolyVariant::SparseUni(p) => p.is_zero(),
            PolyVariant::DenseMle(mle) => mle.is_zero(),
            PolyVariant::SparseMultivariate(p) => p.is_zero(),
            PolyVariant::SparseMle { evals, .. } => evals.iter().all(|(_, v)| v.is_zero()),
        }
    }

    /// The constant this polynomial is, if it is a constant (degree-0
    /// univariate, zero-variable MLE, or constant zero-variable sparse
    /// multivariate). The zero univariate stores no coefficient and is `0`.
    pub fn to_scalar(&self) -> Option<F> {
        match self {
            // The zero polynomial has degree 0 and no coefficients.
            PolyVariant::DenseUni(p) if p.degree() == 0 => {
                Some(p.coeffs.first().copied().unwrap_or_else(F::zero))
            }
            PolyVariant::SparseUni(p) if p.degree() == 0 => {
                Some(p.first().map_or_else(F::zero, |&(_, c)| c))
            }
            PolyVariant::DenseMle(mle) if mle.num_vars() == 0 => mle.evaluations.first().copied(),
            PolyVariant::SparseMultivariate(p) if p.degree() == 0 && p.num_vars == 0 => {
                match p.terms.as_slice() {
                    [] => Some(F::zero()),
                    [(c, _)] => Some(*c),
                    _ => None,
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

    /// A univariate polynomial's coefficients or a multilinear extension's evaluation table;
    /// `None` for a sparse multivariate polynomial.
    pub fn to_vec(&self) -> Option<Vec<F>> {
        match self {
            PolyVariant::DenseMle(mle) => Some(mle.evaluations.clone()),
            PolyVariant::SparseMle { num_vars, evals } => Some(mle::to_dense(*num_vars, evals)),
            _ => self.to_coeffs(),
        }
    }

    /// Get coefficients if this is a univariate polynomial
    pub fn to_coeffs(&self) -> Option<Vec<F>> {
        self.dense_uni().map(|p| p.into_owned().coeffs)
    }

    /// The same polynomial in the dense encoding of its kind; a sparse multivariate polynomial,
    /// which has none, as itself.
    pub fn to_dense(&self) -> Self {
        match self {
            PolyVariant::SparseUni(_) => {
                PolyVariant::DenseUni(self.dense_uni().unwrap().into_owned())
            }
            PolyVariant::SparseMle { num_vars, evals } => {
                mle::dense_mle(*num_vars, mle::to_dense(*num_vars, evals))
            }
            _ => self.clone(),
        }
    }

    /// Evaluate at a point with one coordinate per variable (one for the
    /// univariate encodings).
    ///
    /// # Panics
    /// Panics if `point` has the wrong arity; [`Self::evaluate_mv`] is the
    /// fallible form.
    pub fn evaluate(&self, point: &[F]) -> F {
        self.evaluate_mv(point).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Evaluate at a point with one coordinate per variable (one for the
    /// univariate encodings).
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if `point` does not have
    /// exactly [`Self::num_vars`] coordinates.
    pub fn evaluate_mv(&self, point: &[F]) -> Result<F, PolyError<F>> {
        let expected = self.num_vars();
        if point.len() != expected {
            return Err(PolyError::DimensionMismatch {
                expected,
                actual: point.len(),
            });
        }
        Ok(match self {
            PolyVariant::DenseUni(p) => p.evaluate(&point[0]),
            PolyVariant::SparseUni(p) => p.evaluate(&point[0]),
            PolyVariant::SparseMultivariate(p) => p.evaluate(&point.to_vec()),
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. } => {
                mle::evaluate(self.mle_table().unwrap().1, point)
            }
        })
    }

    /// Fix the first `points.len()` variables of a multivariate polynomial, keeping its
    /// encoding: a `DenseMle`, `SparseMle` or sparse multivariate polynomial in the remaining
    /// variables, renumbered from 0. A constant once all are fixed.
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if more points are supplied
    /// than the polynomial has variables (one for a univariate encoding), and
    /// otherwise [`PolyError::RequiresMle`] for a univariate encoding.
    pub fn evaluate_or_fix(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        let num_vars = self.num_vars();
        let all = num_vars
            .checked_sub(points.len())
            .ok_or(PolyError::DimensionMismatch {
                expected: num_vars,
                actual: points.len(),
            })?
            == 0;
        match self {
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => Err(PolyError::RequiresMle),
            PolyVariant::SparseMultivariate(p) => {
                let rest = multivariate::fix_low(p, points);
                Ok(if all {
                    Self::from_scalar(rest.evaluate(&vec![]))
                } else {
                    PolyVariant::SparseMultivariate(rest)
                })
            }
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. } => {
                let (num_vars, table) = self.mle_table().unwrap();
                Ok(if all {
                    Self::from_scalar(mle::evaluate(table, points))
                } else {
                    mle::fix_low(num_vars, table, points)
                })
            }
        }
    }

    /// Fix all variables outside a contiguous free range, preserving the
    /// selected variables in their original order.
    ///
    /// `fixed` is ordered as variables `[0, range.start)` followed by
    /// variables `[range.end, input_num_vars)`. `input_num_vars` is the
    /// caller's static polynomial arity; selected eval must not guess arity
    /// from constant/zero payloads.
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if `free_range` is not a
    /// unit-step, non-empty range inside `input_num_vars`, if `fixed` does not
    /// supply exactly one value per non-free variable, or if the polynomial's
    /// own arity differs from `input_num_vars`. Univariate encodings are only
    /// accepted for the degenerate range `0..1` with no fixed values.
    pub fn fix_variables_except_range(
        &self,
        input_num_vars: usize,
        free_range: CRange,
        fixed: &[F],
    ) -> Result<Self, PolyError<F>> {
        check_free_range(input_num_vars, &free_range, fixed.len())?;
        if self.is_univariate() {
            // Only the degenerate range `0..1` of a one-variable input.
            return if input_num_vars == 1 {
                Ok(self.clone())
            } else {
                Err(PolyError::DimensionMismatch {
                    expected: input_num_vars - free_range.len(),
                    actual: fixed.len(),
                })
            };
        }
        if self.num_vars() != input_num_vars {
            return Err(PolyError::DimensionMismatch {
                expected: input_num_vars,
                actual: self.num_vars(),
            });
        }
        Ok(match self {
            PolyVariant::SparseMultivariate(p) => {
                PolyVariant::SparseMultivariate(multivariate::restrict(p, &free_range, fixed))
            }
            _ => {
                let (_, table) = self.mle_table().expect("a multivariate encoding");
                mle::restrict(input_num_vars, table, &free_range, fixed)
            }
        })
    }

    /// Serialize to writer
    ///
    /// # Errors
    /// Returns `SerializationError` if the underlying writer fails or an
    /// arkworks component rejects the value.
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
            PolyVariant::SparseMle { num_vars, evals } => {
                4u8.serialize_compressed(&mut writer)?;
                (*num_vars as u64).serialize_compressed(&mut writer)?;
                (evals.len() as u64).serialize_compressed(&mut writer)?;
                for (idx, val) in evals {
                    (*idx as u64).serialize_compressed(&mut writer)?;
                    val.serialize_compressed(&mut writer)?;
                }
                Ok(())
            }
        }
    }
}

impl<F: Field> fmt::Display for PolyVariant<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PolyVariant::DenseUni(p) => write!(f, "Uni({:?})", p.coeffs),
            PolyVariant::SparseUni(_) => write!(f, "SparseUni({:?})", self.to_coeffs().unwrap()),
            PolyVariant::DenseMle(mle) => write!(f, "Mle({:?})", mle.evaluations),
            PolyVariant::SparseMultivariate(p) => write!(
                f,
                "SparseMultivariate(nvars={}, nterms={})",
                p.num_vars,
                p.terms.len()
            ),
            PolyVariant::SparseMle { num_vars, evals } => {
                write!(f, "SparseMle(nvars={}, nnz={})", num_vars, evals.len())
            }
        }
    }
}
