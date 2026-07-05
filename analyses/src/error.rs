use crate::Var;
use crate::frontend::Polynomial;
use backend::ArkConfig;
use graph::GraphError;
use thiserror::Error;

/// Reason why no valid extractor was found for a witness slot.
pub enum ExtractorRejection<C: ArkConfig> {
    /// No basis polynomial has this witness as leading term.
    NoExtractor,
    /// Extractor depends on variables not visible to the verifier.
    NotVisible(Polynomial<C::F>),
    /// Field witness extractor depends on group variables.
    FieldDependsOnGroup(Polynomial<C::F>),
    /// Group witness extractor has a monomial with >1 group variable.
    MultiGroupTerm(Polynomial<C::F>),
}

impl<C: ArkConfig> std::fmt::Debug for ExtractorRejection<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtractorRejection::NoExtractor => write!(f, "NoExtractor"),
            ExtractorRejection::NotVisible(p) => write!(f, "NotVisible({})", p),
            ExtractorRejection::FieldDependsOnGroup(p) => {
                write!(f, "FieldDependsOnGroup({})", p)
            }
            ExtractorRejection::MultiGroupTerm(p) => {
                write!(f, "MultiGroupTerm({})", p)
            }
        }
    }
}

impl<C: ArkConfig> Clone for ExtractorRejection<C> {
    fn clone(&self) -> Self {
        match self {
            ExtractorRejection::NoExtractor => ExtractorRejection::NoExtractor,
            ExtractorRejection::NotVisible(p) => ExtractorRejection::NotVisible(p.clone()),
            ExtractorRejection::FieldDependsOnGroup(p) => {
                ExtractorRejection::FieldDependsOnGroup(p.clone())
            }
            ExtractorRejection::MultiGroupTerm(p) => ExtractorRejection::MultiGroupTerm(p.clone()),
        }
    }
}

/// Errors from static protocol analyses.
#[derive(Error, Debug)]
pub enum AnalysisError<C: ArkConfig> {
    /// A verifier equation that cannot be derived from the prover's Gröbner basis.
    #[error("Incomplete protocol: {0}")]
    Incomplete(Polynomial<C::F>),

    /// A polynomial relating public and private variables, leaking knowledge.
    #[error("Knowledge leak: {0}")]
    KnowledgeLeak(Polynomial<C::F>),

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

    /// No valid extractor found for a witness slot.
    #[error("No valid extractor for witness {witness}: {reason:?}")]
    NoValidExtractor {
        witness: Var,
        reason: Box<ExtractorRejection<C>>,
    },

    /// Extractor invalid; relation remainder is non-zero.
    #[error("Extractor invalid; relation remainder: {0}")]
    ExtractorInvalid(Polynomial<C::F>),

    /// A Gröbner basis reduced to the unit ideal (contains 1).
    /// This indicates the protocol is self-contradictory or the backend
    /// produced an inconsistent basis.
    #[error("Unit ideal: {context}")]
    UnitIdeal { context: &'static str },
}
