#![feature(box_patterns)]
#![allow(clippy::result_large_err)]

// In #[cfg(test)] builds, alias the crate as `analyses` so that test-only
// modules can reference `analyses::TransClos`, `analyses::groebner::...`,
// etc. with the same paths they use when compiled as external bench /
// integration test code.
#[cfg(test)]
extern crate self as analyses;

pub mod completeness;
pub mod error;
pub mod extractor;
pub mod groebner;
pub mod knowledge;
pub mod qualifier;
pub mod soundness;
pub mod trans_clos;
pub mod uniform;

pub use completeness::CompletenessAnalysis;
pub use error::AnalysisError;
pub use groebner::{GroebnerBasis, GroebnerBuilder, GroebnerNamespace, GroebnerResult};
pub use knowledge::KnowledgeAnalysis;
pub use qualifier::QualifierPropagation;
pub use soundness::SpecialSoundnessAnalysis;
pub use trans_clos::TransClos;
pub use uniform::UniformityPropagation;

/// Default packed monomial width for public static-analysis entry points.
///
/// W=128 supports up to 1023 symbolic variables in ark-gb's packed layout,
/// which covers larger IPA and multilinear-sumcheck analyses.
pub const DEFAULT_GB_W: usize = 128;

#[cfg(test)]
mod tests;
