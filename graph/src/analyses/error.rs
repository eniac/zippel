use crate::analyses::groebner::{ElimTerm, GrevLexTerm, SparsePolynomial};
use backend::ArkConfig;
use thiserror::Error;

/// Errors from static protocol analyses.
#[derive(Error, Debug, Clone)]
pub enum AnalysisError<C: ArkConfig> {
    /// A verifier equation that cannot be derived from the prover's Gröbner basis.
    #[error("Incomplete protocol: {0}")]
    Incomplete(SparsePolynomial<C::F, GrevLexTerm>),

    /// A polynomial relating public and private variables, leaking knowledge.
    #[error("Knowledge leak: {0}")]
    KnowledgeLeak(SparsePolynomial<C::F, ElimTerm>),
}
