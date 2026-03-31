pub mod trans_clos;
pub mod groebner;
pub mod uniform;
pub mod qualifier;
pub mod completeness;
pub mod error;

pub mod knowledge;

pub use trans_clos::TransClos;
pub use groebner::{GroebnerBuilder, GroebnerBasis};
pub use qualifier::QualifierPropagation;
pub use uniform::UniformityPropagation;
pub use completeness::CompletenessAnalysis;
pub use knowledge::KnowledgeAnalysis;
pub use error::AnalysisError;

use backend::ArkConfig;
use crate::Dag;

/// A trait for static analyses on a DAG
pub trait StaticAnalysis<C: ArkConfig, A> {
    type Args;
    type Output;
    fn new(g: &Dag<C, A>) -> Self;
    fn run(&mut self, args: Self::Args) -> Self::Output;
}