#![feature(deref_patterns)]
#![allow(clippy::result_large_err)]

#[cfg(test)]
extern crate self as analyses;

pub mod backend;
pub mod completeness;
pub mod error;
pub mod extractor;
pub mod frontend;
pub mod ideal;
pub mod knowledge;
pub mod qualifier;
pub mod soundness;
pub mod uniform;
pub mod var;

pub use completeness::{CompletenessAnalysis, CompletenessInputs};
pub use error::AnalysisError;
pub use frontend::TransClos;
pub use ideal::{Ideal, IdealBuilder, IdealNamespace};
pub use knowledge::KnowledgeAnalysis;
pub use qualifier::QualifierPropagation;
pub use soundness::{SoundnessInputs, SpecialSoundnessAnalysis};
pub use uniform::UniformityPropagation;
pub use var::Var;

pub use backend::GbBackendKind;

#[cfg(test)]
mod tests;
