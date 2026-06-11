use crate::Ref;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum EvalError {
    #[error("Undefined reference: {0:?}")]
    UndefinedRef(Ref),

    #[error("Type mismatch in operation: expected {expected}, got {got}")]
    TypeMismatch { expected: String, got: String },

    #[error("Value operation error: {0}")]
    ValueError(String),

    #[error("Loop parameter out of range: level {0}")]
    LoopParam(usize),
}
