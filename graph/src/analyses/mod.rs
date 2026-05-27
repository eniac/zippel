pub mod completeness;
pub mod error;
pub mod groebner;
pub mod qualifier;
pub mod trans_clos;
pub mod uniform;

pub mod knowledge;

pub use completeness::CompletenessAnalysis;
pub use error::AnalysisError;
pub use groebner::{GroebnerBasis, GroebnerBuilder, GroebnerNamespace, GroebnerResult};
pub use knowledge::KnowledgeAnalysis;
pub use qualifier::QualifierPropagation;
pub use trans_clos::TransClos;
pub use uniform::UniformityPropagation;
use crate::Dag;
use backend::ArkConfig;

/// Default packed monomial width for public static-analysis entry points.
///
/// W=128 supports up to 1023 symbolic variables in ark-gb's packed layout,
/// which covers larger IPA and multilinear-sumcheck analyses.
pub const DEFAULT_GB_W: usize = 128;

/// A trait for static analyses on a DAG
pub trait StaticAnalysis<C: ArkConfig, A> {
    type Args;
    type Output;
    fn new(g: &Dag<C, A>) -> Self;
    fn run(&mut self, args: Self::Args) -> Self::Output;
}
