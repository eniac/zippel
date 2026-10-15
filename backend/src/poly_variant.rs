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
use lang::typ::CRange;
use rayon::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use thiserror::Error;

/// Type alias for sparse multivariate polynomial
type SparseMultivariatePolynomial<F> = MultiSparsePolynomial<F, MultiSparseTerm>;

/// Failures raised by `PolyVariant` arithmetic, evaluation and conversion.
///
/// These are value-level runtime failures hit while a scheduled DAG node
/// executes (shape violations between polynomial encodings, zero divisors,
/// unsupported operand combinations), as distinct from the source-level
/// `TypeError` produced by `lang` during inference. Every variant carries the
/// offending operands so `Display` can print the whole attempted operation.
#[derive(Error, Debug, Clone)]
pub enum PolyError<F: Field> {
    /// A binary operation has no implementation for this pair of encodings,
    /// e.g. multiplying two `SparseMultivariate` polynomials.
    #[error("Unsupported polynomial operation:\n\t{left} {op} {right}")]
    UnsupportedOperation {
        /// The binary operator that was attempted.
        op: BinOp,
        /// Left-hand operand.
        left: PolyVariant<F>,
        /// Right-hand operand.
        right: PolyVariant<F>,
    },

    /// A divisor was the zero polynomial, or a scalar divisor was zero.
    #[error("Division by zero")]
    DivisionByZero {
        /// The polynomial involved in the failed division: the divisor when a
        /// polynomial divisor is zero, otherwise the dividend of a division by
        /// a zero scalar.
        v: PolyVariant<F>,
    },

    /// `scalar / polynomial` is only defined when the polynomial is a
    /// constant (degree-0) polynomial that can be inverted.
    #[error("Can only divide scalar by constant polynomial:\n\t{scalar} / {polynomial}")]
    ScalarDivByNonConstant {
        /// The scalar numerator.
        scalar: F,
        /// The non-constant denominator that cannot be inverted.
        polynomial: PolyVariant<F>,
    },

    /// A polynomial was required to collapse to a field element but is not
    /// degree-0 (see `PolyVariant::try_to_scalar`).
    #[error("Cannot convert non-constant polynomial {0} to scalar")]
    NotConstantPolynomial(PolyVariant<F>),

    /// Two multivariate operands disagree on their variable count, so their
    /// evaluation domains cannot be aligned.
    #[error(
        "Cannot perform operation on multivariate polynomial with different number of variables:\n\t{v1} has {n1}, while {v2} has {n2}"
    )]
    VariableMismatch {
        /// First operand.
        v1: PolyVariant<F>,
        /// Variable count of the first operand.
        n1: usize,
        /// Second operand.
        v2: PolyVariant<F>,
        /// Variable count of the second operand.
        n2: usize,
    },

    /// An evaluation point has the wrong arity for the polynomial being
    /// evaluated or partially fixed.
    #[error(
        "Evaluation point dimension mismatch: expected {expected} variables, but received {actual}"
    )]
    DimensionMismatch {
        /// Number of coordinates the polynomial requires.
        expected: usize,
        /// Number of coordinates actually supplied.
        actual: usize,
    },

    /// Two multilinear extensions disagree on their number of variables.
    #[error("MLE variable count mismatch: {v1} vs {v2}")]
    MleVariableMismatch {
        /// Variable count of the first extension.
        v1: usize,
        /// Variable count of the second extension.
        v2: usize,
    },

    /// Multilinear extensions cannot be multiplied in place: the product of
    /// two multilinear polynomials is no longer multilinear, so callers must
    /// build a `VirtualPolynomial` (a sum of products) instead.
    #[error("MLE multiplication not directly supported: {v1} * {v2}")]
    MleMultiplication {
        /// First factor.
        v1: PolyVariant<F>,
        /// Second factor.
        v2: PolyVariant<F>,
    },

    /// Division is undefined for this pair of encodings (any operand that is
    /// multilinear or sparse multivariate).
    #[error("Division not applicable for: {v1} / {v2}")]
    DivisionNotApplicable {
        /// Dividend.
        v1: PolyVariant<F>,
        /// Divisor.
        v2: PolyVariant<F>,
    },

    /// The operation is only implemented for multilinear extensions and was
    /// handed some other encoding.
    #[error("Operation requires MLE polynomial")]
    RequiresMle,

    /// The polynomial is not a `DenseMle`, so MLE-specific evaluation cannot
    /// be performed.
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
    /// Sparse multilinear extension in **evaluation form**: a list of
    /// `(boolean_index, value)` pairs interpreted as the MLE of a function
    /// `f: {0,1}^num_vars → F` with `f(i) = value` for each listed pair and
    /// `f(i) = 0` elsewhere. Indices are LSB-first (variable 0 is the low
    /// bit of the index). Designed for Spartan-style R1CS matrices, where
    /// `num_vars` is `2·log(N)` but only ~3·N entries are non-zero — full
    /// evaluation and partial-evaluation both run in `O(|evals| · num_vars)`
    /// rather than `O(2^num_vars)`. Arithmetic ops on this variant fall
    /// back to `to_dense` first (correct but expensive); the only fast
    /// paths are `evaluate` and `evaluate_or_fix_mle`.
    SparseMle {
        /// Number of boolean variables of the underlying function; the dense
        /// evaluation table this stands for would have `2^num_vars` entries.
        num_vars: usize,
        /// Non-zero entries as `(boolean_index, value)` pairs; all unlisted
        /// indices evaluate to zero.
        evals: Vec<(usize, F)>,
    },
}

/// Fixes the low `point.len()` variables of the multilinear extension whose
/// evaluation table is `evals` (variable 0 is the low bit of an index).
///
/// Entry `j` of the result is the block `evals[j·2^k..(j+1)·2^k]` evaluated at
/// the `k`-coordinate `point`, so fixing every variable evaluates the
/// extension. Only the `2^(n-k)`-entry result is allocated: arkworks'
/// `fix_variables` and `evaluate` first copy the whole table, and fold it
/// single-threaded.
///
/// # Panics
/// Panics if `evals.len()` is not a multiple of `2^point.len()`.
fn fix_low_variables<F: Field>(evals: &[F], point: &[F]) -> Vec<F> {
    let block = 1usize << point.len();
    assert_eq!(
        evals.len() % block,
        0,
        "fixing more variables than the table has"
    );
    evals
        .par_chunks(block)
        .map(|b| evaluate_block(b, point))
        .collect()
}

/// Blocks above this many entries evaluate their halves in parallel.
const PARALLEL_BLOCK: usize = 1 << 10;

/// The multilinear extension of `block` (`2^point.len()` entries) at `point`:
/// the halves on the last variable, combined.
fn evaluate_block<F: Field>(block: &[F], point: &[F]) -> F {
    let Some((&r, rest)) = point.split_last() else {
        return block[0];
    };
    let (lo, hi) = block.split_at(block.len() / 2);
    let (a, b) = if block.len() > PARALLEL_BLOCK {
        rayon::join(|| evaluate_block(lo, rest), || evaluate_block(hi, rest))
    } else {
        (evaluate_block(lo, rest), evaluate_block(hi, rest))
    };
    a + r * (b - a)
}

/// [`fix_low_variables`] for a sparse table of `(index, value)` entries over
/// `num_vars` variables: each entry is weighted by `eq(point, low bits)` and
/// added to the slot of its high bits. `O(|evals| · k + 2^(n-k))`.
fn fix_low_variables_sparse<F: Field>(
    num_vars: usize,
    evals: &[(usize, F)],
    point: &[F],
) -> Vec<F> {
    let k = point.len();
    debug_assert!(k <= num_vars);
    let one_minus: Vec<F> = point.iter().map(|r| F::one() - r).collect();
    let weight = |idx: usize, value: F| {
        (0..k).fold(value, |acc, j| {
            acc * if (idx >> j) & 1 == 1 {
                point[j]
            } else {
                one_minus[j]
            }
        })
    };
    if k == num_vars {
        return vec![evals.par_iter().map(|&(i, v)| weight(i, v)).sum()];
    }
    let mut out = vec![F::zero(); 1 << (num_vars - k)];
    for &(i, v) in evals {
        out[i >> k] += weight(i, v);
    }
    out
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

fn fixed_index_for_var(free_range: &CRange, var_idx: usize) -> Option<usize> {
    if var_idx < free_range.start() {
        Some(var_idx)
    } else if var_idx >= free_range.end() {
        Some(free_range.start() + (var_idx - free_range.end()))
    } else {
        None
    }
}

/// Fixes the variables outside `free_range` of the multilinear extension
/// whose non-zero table entries are `entries`, keeping the free variables in
/// order: each entry is weighted by `eq(fixed, its fixed bits)` and added to
/// the slot of its free bits.
fn restrict_mle_except_range<F: Field>(
    input_num_vars: usize,
    entries: impl Iterator<Item = (usize, F)>,
    free_range: &CRange,
    fixed: &[F],
) -> DenseMultilinearExtension<F> {
    let free_len = free_range.len();
    let mut out = vec![F::zero(); 1usize << free_len];
    for (idx, value) in entries {
        let mut free_idx = 0usize;
        let mut factor = value;
        for var_idx in 0..input_num_vars {
            let bit = (idx >> var_idx) & 1 == 1;
            match fixed_index_for_var(free_range, var_idx) {
                None => {
                    if bit {
                        free_idx |= 1usize << (var_idx - free_range.start());
                    }
                }
                Some(i) => factor *= if bit { fixed[i] } else { F::one() - fixed[i] },
            }
        }
        out[free_idx] += factor;
    }
    DenseMultilinearExtension::from_evaluations_vec(free_len, out)
}

fn field_bits<F: Field>(values: &[F]) -> Option<Vec<bool>> {
    values
        .iter()
        .map(|value| {
            if value.is_zero() {
                Some(false)
            } else if *value == F::one() {
                Some(true)
            } else {
                None
            }
        })
        .collect()
}

fn restrict_dense_mle_except_range_boolean<F: Field>(
    input_num_vars: usize,
    evals: &[F],
    free_range: CRange,
    fixed_bits: &[bool],
) -> DenseMultilinearExtension<F> {
    let free_len = free_range.len();
    let mut out = vec![F::zero(); 1usize << free_len];
    let fill_value = |free_idx: usize| {
        let mut source_idx = 0usize;
        for var_idx in 0..input_num_vars {
            let bit = match fixed_index_for_var(&free_range, var_idx) {
                None => ((free_idx >> (var_idx - free_range.start())) & 1) == 1,
                Some(i) => fixed_bits[i],
            };
            if bit {
                source_idx |= 1usize << var_idx;
            }
        }
        evals[source_idx]
    };

    if out.len() <= 1024 {
        for (free_idx, out_value) in out.iter_mut().enumerate() {
            *out_value = fill_value(free_idx);
        }
    } else {
        out.par_iter_mut()
            .enumerate()
            .for_each(|(free_idx, out_value)| *out_value = fill_value(free_idx));
    }
    DenseMultilinearExtension::from_evaluations_vec(free_len, out)
}

impl<F: Field> PolyVariant<F> {
    /// Get the degree of the polynomial
    pub fn degree(&self) -> usize {
        match self {
            PolyVariant::DenseUni(p) => p.degree(),
            PolyVariant::SparseUni(p) => p.degree(),
            PolyVariant::DenseMle(_) => 1,
            PolyVariant::SparseMultivariate(p) => p.degree(),
            PolyVariant::SparseMle { .. } => 1,
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

    /// An upper bound on the total degree, read from the representation
    /// rather than its bookkeeping (a dense univariate's coefficient count, a
    /// sparse one's largest index): unlike [`Self::degree`], an MLE counts
    /// as its variable count, and a malformed sparse univariate cannot
    /// understate it.
    pub fn total_degree_bound(&self) -> usize {
        match self {
            PolyVariant::DenseUni(p) => p.coeffs.len().saturating_sub(1),
            PolyVariant::SparseUni(p) => p.iter().map(|(i, _)| *i).max().unwrap_or(0),
            PolyVariant::DenseMle(mle) => mle.num_vars,
            PolyVariant::SparseMle { num_vars, .. } => *num_vars,
            PolyVariant::SparseMultivariate(p) => p
                .terms
                .iter()
                .map(|(_, term)| term.degree())
                .max()
                .unwrap_or(0),
        }
    }

    /// Densify a `SparseMle`: instantiate the `2^num_vars` evaluation vector
    /// by scattering the listed `(index, value)` pairs. O(`2^num_vars + |evals|`).
    fn sparse_mle_to_dense_mle(
        num_vars: usize,
        evals: &[(usize, F)],
    ) -> DenseMultilinearExtension<F> {
        let len = 1usize << num_vars;
        let mut dense = vec![F::zero(); len];
        for (idx, val) in evals {
            debug_assert!(*idx < len, "SparseMle index out of range");
            dense[*idx] += *val;
        }
        DenseMultilinearExtension::from_evaluations_vec(num_vars, dense)
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

    /// Get the number of variables for a multilinear polynomial (returns None for univariate or virtual)
    pub fn num_vars(&self) -> usize {
        match self {
            PolyVariant::DenseMle(mle) => mle.num_vars(),
            PolyVariant::SparseMultivariate(p) => p.num_vars,
            PolyVariant::SparseMle { num_vars, .. } => *num_vars,
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
            PolyVariant::SparseMle { .. } => true,
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => false,
        }
    }

    /// Check if this is a multivariate polynomial
    pub fn is_multivariate(&self) -> bool {
        matches!(
            self,
            PolyVariant::DenseMle(_)
                | PolyVariant::SparseMultivariate(_)
                | PolyVariant::SparseMle { .. }
        )
    }

    /// The constant this polynomial is, if it is a non-zero constant
    /// (degree-0 univariate, zero-variable MLE, or constant zero-variable
    /// sparse multivariate). Zero-coefficient univariates have no stored
    /// coefficient and answer `None`.
    pub fn to_scalar(&self) -> Option<F> {
        match self {
            PolyVariant::DenseUni(p) if p.degree() == 0 => p.coeffs.first().copied(),
            PolyVariant::SparseUni(p) if p.degree() == 0 => p.first().map(|&(_, c)| c),
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
            PolyVariant::SparseMle { num_vars, evals } => {
                Some(Self::sparse_mle_to_dense_mle(*num_vars, evals).evaluations)
            }
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
            PolyVariant::SparseMle { evals, .. } => evals.iter().all(|(_, v)| v.is_zero()),
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

    /// Convert to dense representation
    pub fn to_dense(&self) -> Self {
        match self {
            PolyVariant::DenseUni(_) | PolyVariant::DenseMle(_) => self.clone(),
            PolyVariant::SparseUni(p) => {
                let dense: DensePolynomial<F> = p.clone().into();
                PolyVariant::DenseUni(dense)
            }
            PolyVariant::SparseMultivariate(_) => self.clone(), // Already sparse, no dense equivalent
            PolyVariant::SparseMle { num_vars, evals } => {
                PolyVariant::DenseMle(Self::sparse_mle_to_dense_mle(*num_vars, evals))
            }
        }
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
            PolyVariant::DenseMle(mle) => evaluate_block(&mle.evaluations, point),
            PolyVariant::SparseMultivariate(p) => p.evaluate(&point.to_vec()),
            PolyVariant::SparseMle { num_vars, evals } => {
                fix_low_variables_sparse(*num_vars, evals, point)[0]
            }
        })
    }

    // ========== Arithmetic Operations ==========

    /// Add two polynomials
    ///
    /// # Errors
    /// Returns [`PolyError::MleVariableMismatch`] or
    /// [`PolyError::VariableMismatch`] when the operands disagree on their
    /// variable count, and [`PolyError::UnsupportedOperation`] for encoding
    /// pairs with no addition rule (for example `DenseMle` plus
    /// `SparseMultivariate`).
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
            PolyVariant::SparseMle { .. } => self.to_dense().poly_add_scalar(scalar),
        }
    }

    /// The same polynomial with `f` applied to every stored coefficient or
    /// evaluation, in the same encoding. `f` must map zero to zero, so
    /// unstored (zero) entries stay correct.
    fn map_values(&self, f: impl Fn(F) -> F + Sync + Send) -> Self {
        match self {
            PolyVariant::DenseUni(p) => {
                PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(
                    p.coeffs.par_iter().map(|&c| f(c)).collect(),
                ))
            }
            PolyVariant::SparseUni(p) => {
                PolyVariant::SparseUni(SparsePolynomial::from_coefficients_vec(
                    p.iter().map(|&(d, c)| (d, f(c))).collect(),
                ))
            }
            PolyVariant::DenseMle(mle) => {
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                    mle.num_vars(),
                    mle.evaluations.par_iter().map(|&e| f(e)).collect(),
                ))
            }
            PolyVariant::SparseMultivariate(p) => {
                PolyVariant::SparseMultivariate(SparseMultivariatePolynomial {
                    num_vars: p.num_vars,
                    terms: p.terms.iter().map(|(c, t)| (f(*c), t.clone())).collect(),
                })
            }
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
        let scalar_poly = PolyVariant::from_scalar(scalar);
        scalar_poly.poly_sub(poly)
    }

    /// Multiply two polynomials - always returns a VirtualPolynomial for any multiplication
    ///
    /// Uses arkworks' `Mul` impl on `&DensePolynomial`, which dispatches
    /// to FFT-based multiplication (evaluate over a smooth domain → pointwise
    /// → interpolate). That's O(n log n); the previous `naive_mul` path was
    /// O(n²) and dominated zippel-side prover time at large K. The
    /// `F: FftField` bound is already satisfied wherever this is called
    /// from (`Value<C>` uses C::F: PrimeField, and PrimeField: FftField).
    ///
    /// # Errors
    /// Returns [`PolyError::MleMultiplication`] if either operand is a
    /// `DenseMle` (the product would no longer be multilinear — build a
    /// `VirtualPolynomial` instead), and
    /// [`PolyError::UnsupportedOperation`] for sparse-multivariate operands
    /// and any other unhandled encoding pair.
    pub fn poly_mul(&self, other: &Self) -> Result<Self, PolyError<F>>
    where
        F: ark_ff::FftField,
    {
        match (self, other) {
            // Univariate * Univariate. Use arkworks dense multiplication here;
            // for FFT-capable fields this routes through an evaluation domain
            // instead of the quadratic `naive_mul` path.
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                Ok(PolyVariant::DenseUni(p1 * p2))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::SparseUni(p2)) => {
                let dense1: DensePolynomial<F> = p1.clone().into();
                let dense2: DensePolynomial<F> = p2.clone().into();
                Ok(PolyVariant::DenseUni(&dense1 * &dense2))
            }
            (PolyVariant::DenseUni(p1), PolyVariant::SparseUni(p2)) => {
                let dense2: DensePolynomial<F> = p2.clone().into();
                Ok(PolyVariant::DenseUni(p1 * &dense2))
            }
            (PolyVariant::SparseUni(p1), PolyVariant::DenseUni(p2)) => {
                let dense1: DensePolynomial<F> = p1.clone().into();
                Ok(PolyVariant::DenseUni(&dense1 * p2))
            }

            // MLE * _ - not directly supported, should use VirtualPolynomial
            (a @ PolyVariant::DenseMle(_), b) | (b, a @ PolyVariant::DenseMle(_)) => {
                Err(PolyError::MleMultiplication {
                    v1: a.clone(),
                    v2: b.clone(),
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
        self.map_values(|v| v * scalar)
    }

    /// Quotient and remainder of dense univariates; `divisor` is the operand
    /// reported when `p2` is zero.
    fn div_rem(
        p1: &DensePolynomial<F>,
        p2: &DensePolynomial<F>,
        divisor: &Self,
    ) -> Result<(DensePolynomial<F>, DensePolynomial<F>), PolyError<F>>
    where
        F: PrimeField,
    {
        // ark-poly returns `(0, 0)` for a zero dividend before checking the divisor.
        if p2.is_zero() {
            return Err(PolyError::DivisionByZero { v: divisor.clone() });
        }
        DenseOrSparsePolynomial::from(p1)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(p2))
            .ok_or_else(|| PolyError::DivisionByZero { v: divisor.clone() })
    }

    /// Divide two polynomials
    ///
    /// # Errors
    /// Returns [`PolyError::DivisionByZero`] if the divisor is the zero
    /// polynomial, and [`PolyError::DivisionNotApplicable`] if either operand
    /// is multilinear or sparse multivariate.
    pub fn poly_div(&self, other: &Self) -> Result<Self, PolyError<F>>
    where
        F: PrimeField,
    {
        match (self, other) {
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                Ok(PolyVariant::DenseUni(Self::div_rem(p1, p2, other)?.0))
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
    ///
    /// # Errors
    /// Returns [`PolyError::DivisionByZero`] if `scalar` is zero.
    pub fn poly_div_scalar(&self, scalar: F) -> Result<Self, PolyError<F>> {
        let inv = scalar
            .inverse()
            .ok_or_else(|| PolyError::DivisionByZero { v: self.clone() })?;
        Ok(self.poly_mul_scalar(inv))
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
            PolyVariant::DenseMle(mle) => PolyVariant::DenseMle(match field_bits(fixed) {
                Some(bits) => restrict_dense_mle_except_range_boolean(
                    input_num_vars,
                    &mle.evaluations,
                    free_range,
                    &bits,
                ),
                None => restrict_mle_except_range(
                    input_num_vars,
                    mle.evaluations.iter().copied().enumerate(),
                    &free_range,
                    fixed,
                ),
            }),
            PolyVariant::SparseMle { evals, .. } => {
                PolyVariant::DenseMle(restrict_mle_except_range(
                    input_num_vars,
                    evals.iter().copied(),
                    &free_range,
                    fixed,
                ))
            }
            PolyVariant::SparseMultivariate(p) => {
                let mut terms_by_monomial: HashMap<MultiSparseTerm, F> = HashMap::new();
                for (coeff, term) in &p.terms {
                    let mut new_coeff = *coeff;
                    let mut new_term = Vec::with_capacity(term.len());
                    for &(var_idx, pow) in term.iter() {
                        match fixed_index_for_var(&free_range, var_idx) {
                            Some(i) => new_coeff *= fixed[i].pow([pow as u64]),
                            None => new_term.push((var_idx - free_range.start(), pow)),
                        }
                    }
                    if !new_coeff.is_zero() {
                        *terms_by_monomial
                            .entry(MultiSparseTerm::new(new_term))
                            .or_insert_with(F::zero) += new_coeff;
                    }
                }
                let terms = terms_by_monomial
                    .into_iter()
                    .filter_map(|(term, coeff)| (!coeff.is_zero()).then_some((coeff, term)))
                    .collect();
                PolyVariant::SparseMultivariate(SparseMultivariatePolynomial {
                    num_vars: free_range.len(),
                    terms,
                })
            }
            PolyVariant::DenseUni(_) | PolyVariant::SparseUni(_) => unreachable!("handled above"),
        })
    }

    /// Fix the first `points.len()` variables of a multilinear extension: a
    /// `DenseMle` in the remaining variables, or a constant once all are fixed.
    ///
    /// # Errors
    /// Returns [`PolyError::DimensionMismatch`] if more points are supplied
    /// than the extension has variables, and [`PolyError::RequiresMle`] for
    /// any encoding that is not `DenseMle` or `SparseMle`.
    pub fn evaluate_or_fix_mle(&self, points: &[F]) -> Result<Self, PolyError<F>> {
        let num_vars = match self {
            PolyVariant::DenseMle(_) | PolyVariant::SparseMle { .. } => self.num_vars(),
            _ => return Err(PolyError::RequiresMle),
        };
        if points.len() > num_vars {
            return Err(PolyError::DimensionMismatch {
                expected: num_vars,
                actual: points.len(),
            });
        }
        let rest = match self {
            PolyVariant::DenseMle(mle) => fix_low_variables(&mle.evaluations, points),
            PolyVariant::SparseMle { evals, .. } => {
                fix_low_variables_sparse(num_vars, evals, points)
            }
            _ => unreachable!("checked above"),
        };
        Ok(if points.len() == num_vars {
            Self::from_scalar(rest[0])
        } else {
            PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(
                num_vars - points.len(),
                rest,
            ))
        })
    }

    // ========== Serialization ==========

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

impl<F: Field> PartialEq for PolyVariant<F> {
    /// Structural equality: the same encoding with the same contents.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PolyVariant::DenseUni(a), PolyVariant::DenseUni(b)) => a == b,
            (PolyVariant::SparseUni(a), PolyVariant::SparseUni(b)) => a == b,
            (PolyVariant::DenseMle(a), PolyVariant::DenseMle(b)) => a == b,
            (PolyVariant::SparseMultivariate(a), PolyVariant::SparseMultivariate(b)) => a == b,
            (
                PolyVariant::SparseMle {
                    num_vars: n1,
                    evals: e1,
                },
                PolyVariant::SparseMle {
                    num_vars: n2,
                    evals: e2,
                },
            ) => n1 == n2 && e1 == e2,
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

/// Lexicographic order of field-element sequences, by canonical integer.
fn cmp_field_seq<'a, F: PrimeField + 'a>(
    a: impl Iterator<Item = &'a F>,
    b: impl Iterator<Item = &'a F>,
) -> std::cmp::Ordering {
    a.map(|x| x.into_bigint()).cmp(b.map(|x| x.into_bigint()))
}

impl<F: PrimeField> Ord for PolyVariant<F> {
    /// Univariates < dense MLEs < sparse multivariates < sparse MLEs; within
    /// an encoding, by size and then contents. Consistent with `Eq`: a dense
    /// and a sparse univariate with the same coefficients order dense first.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use PolyVariant::{DenseMle, DenseUni, SparseMle, SparseMultivariate, SparseUni};
        let rank = |p: &Self| match p {
            DenseUni(_) | SparseUni(_) => 0,
            DenseMle(_) => 1,
            SparseMultivariate(_) => 2,
            SparseMle { .. } => 3,
        };
        rank(self)
            .cmp(&rank(other))
            .then_with(|| match (self, other) {
                (DenseUni(_) | SparseUni(_), DenseUni(_) | SparseUni(_)) => {
                    let (a, b) = (self.to_coeffs().unwrap(), other.to_coeffs().unwrap());
                    a.len()
                        .cmp(&b.len())
                        .then_with(|| cmp_field_seq(a.iter(), b.iter()))
                        .then_with(|| {
                            matches!(self, SparseUni(_)).cmp(&matches!(other, SparseUni(_)))
                        })
                }
                (DenseMle(a), DenseMle(b)) => a
                    .num_vars()
                    .cmp(&b.num_vars())
                    .then_with(|| cmp_field_seq(a.evaluations.iter(), b.evaluations.iter())),
                (SparseMultivariate(a), SparseMultivariate(b)) => a
                    .num_vars
                    .cmp(&b.num_vars)
                    .then_with(|| a.terms.len().cmp(&b.terms.len()))
                    .then_with(|| {
                        a.terms
                            .iter()
                            .map(|(c, t)| (c.into_bigint(), t))
                            .cmp(b.terms.iter().map(|(c, t)| (c.into_bigint(), t)))
                    }),
                (
                    SparseMle {
                        num_vars: n1,
                        evals: e1,
                    },
                    SparseMle {
                        num_vars: n2,
                        evals: e2,
                    },
                ) => n1.cmp(n2).then_with(|| {
                    e1.iter()
                        .map(|(i, v)| (*i, v.into_bigint()))
                        .cmp(e2.iter().map(|(i, v)| (*i, v.into_bigint())))
                }),
                _ => unreachable!("equal ranks are the same encoding"),
            })
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
            PolyVariant::SparseMle { num_vars, evals } => {
                write!(f, "SparseMle(nvars={}, nnz={})", num_vars, evals.len())
            }
        }
    }
}
