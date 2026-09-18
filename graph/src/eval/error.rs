use crate::Ref;
use thiserror::Error;

/// Failure raised while constant-folding / interpreting a DAG node outside the
/// full `runtime` engine (see `graph::eval`).
///
/// These are invariant violations in the IR or unsupported value shapes, not
/// user-facing type errors — those are reported by `lang`'s `infer()`.
#[derive(Error, Debug)]
pub enum EvalError {
    /// A `Ref` node pointed at a node that has no value in the evaluation
    /// environment, i.e. it was consumed before its definition was evaluated.
    #[error("Undefined reference: {0:?}")]
    UndefinedRef(Ref),

    /// An operand had a runtime `Value` shape incompatible with the operation,
    /// e.g. a group element where a scalar was required.
    #[error("Type mismatch in operation: expected {expected}, got {got}")]
    TypeMismatch {
        /// Description of the shape the operation required.
        expected: String,
        /// Description of the shape actually supplied.
        got: String,
    },

    /// A `backend` value-level operation rejected its arguments; the payload is
    /// the backend's message.
    #[error("Value operation error: {0}")]
    ValueError(String),

    /// A loop index was requested for a nesting level that the current
    /// evaluation context does not bind.
    #[error("Loop parameter out of range: level {0}")]
    LoopParam(usize),
}
