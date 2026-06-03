use crate::analyses::groebner::{GrevLexTerm, SparsePolynomial};
use crate::analyses::knowledge::ElimTerm;
use crate::analyses::soundness::SoundnessElimTerm;
use crate::{GraphError, PRef};
use backend::ArkConfig;
use thiserror::Error;

/// Errors from static protocol analyses.
#[derive(Error, Debug)]
pub enum AnalysisError<C: ArkConfig> {
    /// A verifier equation that cannot be derived from the prover's Gröbner basis.
    #[error("Incomplete protocol: {0}")]
    Incomplete(SparsePolynomial<C::F, GrevLexTerm>),

    /// A polynomial relating public and private variables, leaking knowledge.
    #[error("Knowledge leak: {0}")]
    KnowledgeLeak(SparsePolynomial<C::F, ElimTerm>),

    /// The verifier subgraph is invalid or cannot be projected from the graph.
    #[error("Verifier invalid: {0}")]
    VerifierInvalid(GraphError),

    /// Special soundness requires l_vec non-empty and each li >= 2.
    #[error("Special soundness requires l_vec non-empty and each li >= 2")]
    InvalidSoundnessParameter,

    /// Special soundness requires at least one challenge.
    #[error("Special soundness requires at least one challenge")]
    NoChallenge,

    /// The number of challenge rounds does not match l_vec length.
    #[error(
        "Not a 2n+1-move protocol: l_vec has {expected} round(s) but verifier has {found} challenge(s)"
    )]
    Not2nPlus1MoveProtocol { expected: usize, found: usize },

    /// No extractor polynomial found for witness variable.
    #[error("No extractor for witness: {0}")]
    NoExtractor(PRef),

    /// Extractor polynomial depends on non-transcript-visible variables.
    #[error("Extractor for witness {witness} is not transcript-computable: {poly}")]
    ExtractorNotVisible {
        witness: PRef,
        poly: SparsePolynomial<C::F, SoundnessElimTerm>,
    },

    /// Extractor invalid; relation remainder is non-zero.
    #[error("Extractor invalid; relation remainder: {0}")]
    ExtractorInvalid(SparsePolynomial<C::F, SoundnessElimTerm>),
}
