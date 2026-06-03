use crate::analyses::groebner::{ElimTerm, GrevLexTerm, SparsePolynomial};
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

    /// Special soundness requires l >= 2.
    #[error("Special soundness requires l >= 2")]
    InvalidSoundnessParameter,

    /// Special soundness requires at least one challenge.
    #[error("Special soundness requires at least one challenge")]
    NoChallenge,

    /// Protocol is not a sigma (3-move) protocol: challenges and
    /// prover responses are interleaved rather than all challenges
    /// preceding all responses.
    #[error("Not a sigma protocol: challenges and responses interleaved (challenge {challenge_name} follows response {response_name})")]
    NotSigmaProtocol {
        challenge_name: String,
        response_name: String,
    },

    /// No extractor polynomial found for witness variable.
    #[error("No extractor for witness: {0}")]
    NoExtractor(PRef),

    /// Extractor polynomial depends on non-transcript-visible variables.
    #[error("Extractor for witness {witness} is not transcript-computable: {poly}")]
    ExtractorNotVisible {
        witness: PRef,
        poly: SparsePolynomial<C::F, GrevLexTerm>,
    },

    /// Extractor invalid; relation remainder is non-zero.
    #[error("Extractor invalid; relation remainder: {0}")]
    ExtractorInvalid(SparsePolynomial<C::F, GrevLexTerm>),
}
