//! Failures of [`PolyVariant`] arithmetic, evaluation and conversion.

use ark_ff::Field;
use lang::ast::BinOp;
use thiserror::Error;

use super::PolyVariant;

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
        /// The multilinear factor (the left one if both are).
        v1: PolyVariant<F>,
        /// The other factor.
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

    /// The operation needs a polynomial in several variables (fixing some of
    /// them) and was handed a univariate encoding.
    #[error("Operation requires MLE polynomial")]
    RequiresMle,
}
