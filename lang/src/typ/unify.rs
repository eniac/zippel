use crate::id::Tid;
use crate::typ::lub::LubError;
use crate::typ::{CKind, CTyp};
use thiserror::Error;

/// Failure raised while matching a parameter type against an argument type.
#[derive(Error, PartialEq, Debug)]
pub enum UnifyError {
    /// Wraps the failure that occurred while matching the two given types; displays that
    /// failure.
    #[error("{2}")]
    Typ(CTyp, CTyp, Box<UnifyError>),
    /// A least-upper-bound computation on a nested size range failed.
    #[error(transparent)]
    Lub(LubError),
    /// A type variable has no entry in the kind context `kctx`.
    #[error("Unknown type variable `{0}`")]
    KindNotFound(Tid),
    /// A parameter was matched with a caller type variable of an incompatible kind.
    #[error("Type {0} ({1}) does not match {2} ({3})")]
    KindMismatch(Tid, CKind, Tid, CKind),
    /// The two type shapes do not match.
    #[error("Type {0} does not match {1}")]
    TypMismatch(CTyp, CTyp),
}

impl UnifyError {
    /// Builds a [`UnifyError::KindNotFound`] for a type variable missing from `kctx`.
    pub fn kind_not_found(a: &Tid) -> Self {
        UnifyError::KindNotFound(a.clone())
    }
    /// Wraps `e` with the pair of types whose matching produced it.
    pub fn typ(a: &CTyp, b: &CTyp, e: UnifyError) -> Self {
        UnifyError::Typ(a.clone(), b.clone(), Box::new(e))
    }
    /// Builds a [`UnifyError::KindMismatch`] recording both variables and their kinds.
    pub fn kind_mismatch(a: &Tid, ka: &CKind, b: &Tid, kb: &CKind) -> Self {
        UnifyError::KindMismatch(a.clone(), ka.clone(), b.clone(), kb.clone())
    }
    /// Builds a [`UnifyError::TypMismatch`] for two type shapes that do not match.
    pub fn typ_mismatch(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::TypMismatch(a.clone(), b.clone())
    }
}
