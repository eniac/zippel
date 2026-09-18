//! Static protocol analyses over the Zippel graph IR.
//!
//! Every analysis in this crate consumes a [`graph::Dag`] that has already
//! been through qualifier propagation and turns it into a system of
//! polynomial equations over the protocol's variables. Gröbner-basis
//! reasoning on that system then answers the security questions: is the
//! verifier's equation implied by the prover's computation
//! ([`CompletenessAnalysis`]), does any basis element relate instance and
//! witness variables ([`KnowledgeAnalysis`]), and can a witness be extracted
//! from transcripts ([`SpecialSoundnessAnalysis`]).
//!
//! The [`frontend`] module holds ordering-free polynomial machinery, the
//! [`backend`] module owns leading-term and Gröbner-basis computation, and
//! [`Var`] is the shared notion of a scalar slot that both sides speak in.

#![feature(deref_patterns)]
#![allow(clippy::result_large_err)]

#[cfg(test)]
extern crate self as analyses;

pub mod backend;
/// Completeness analysis: verifier equations reduce to zero modulo the prover.
pub mod completeness;
/// Error type shared by every analysis in this crate.
pub mod error;
/// Witness extraction from a Gröbner basis, and its rejection reasons.
pub mod extractor;
pub mod frontend;
/// Construction of polynomial ideals from a DAG's transitive closure.
pub mod ideal;
/// Knowledge analysis: detects polynomials leaking witness data.
pub mod knowledge;
/// Qualifier propagation: labels nodes `Witness`/`Instance`/`Local`/`Extra`.
pub mod qualifier;
/// Special-soundness analysis over `2n+1`-move protocols.
pub mod soundness;
/// Uniformity propagation: distributions and ancestor sets per node.
pub mod uniform;
/// [`Var`], the scalar-slot variable every analysis polynomial ranges over.
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
