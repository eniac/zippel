#![feature(box_patterns)]
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

pub use completeness::CompletenessAnalysis;
pub use error::AnalysisError;
pub use frontend::TransClos;
pub use ideal::{IdealBuilder, GroebnerNamespace, Ideal};
pub use knowledge::KnowledgeAnalysis;
pub use qualifier::QualifierPropagation;
pub use soundness::SpecialSoundnessAnalysis;
pub use uniform::UniformityPropagation;

/// Default packed monomial width for public static-analysis entry points.
///
/// W=128 supports up to 1023 symbolic variables in ark-gb's packed layout,
/// which covers larger IPA and multilinear-sumcheck analyses.
pub const DEFAULT_GB_W: usize = 128;

#[cfg(test)]
mod tests;
