//! Explicit static-analysis preparation and pass execution.

use crate::{CompileError, CompiledProtocol};
use analyses::{
    AnalysisBackend, AnalysisError, CompletenessAnalysis, GbBackendKind, KnowledgeAnalysis,
    QualifierPropagation, SpecialSoundnessAnalysis,
};
use backend::Backend;
use graph::{Dag, Relations, UDags};
use lang::typ::Qualifier;
use std::sync::Arc;

/// A static-analysis pass with its protocol-specific parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Analysis<'a> {
    /// Check completeness.
    Completeness,
    /// Check zero-knowledge through qualifier and algebraic knowledge analysis.
    Zk,
    /// Check special soundness using the transcript counts for each round.
    Soundness(&'a [usize]),
}

impl Analysis<'_> {
    /// Human-readable pass name.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Completeness => "Completeness",
            Self::Zk => "ZK",
            Self::Soundness(_) => "Soundness",
        }
    }
}

/// A relation-lowered, qualifier-propagated graph ready for analysis passes.
///
/// Constructed by [`CompiledProtocol::prepare_analysis`]. Reuse this object to measure
/// multiple passes independently of graph preparation.
pub struct PreparedAnalysis<C: Backend> {
    graph: Dag<C, Qualifier>,
}

impl<C: AnalysisBackend> CompiledProtocol<C> {
    /// Lower the full protocol graph, including its relation, and propagate qualifiers.
    ///
    /// Call once before timing passes. This does no polynomial encoding or Gröbner-basis work.
    ///
    /// # Errors
    /// Returns source diagnostics if full graph construction fails.
    ///
    /// # Panics
    /// If an internal compiler invariant fails.
    pub fn prepare_analysis(&self) -> Result<PreparedAnalysis<C>, CompileError> {
        let graphs = UDags::<C>::lower(&self.typed, Relations::Lower).map_err(|e| {
            CompileError::Diagnostics {
                name: self.source_name.clone(),
                source: Arc::clone(&self.source),
                diagnostics: vec![e.into()],
            }
        })?;
        let graph = graphs
            .protocol(&self.protocol_name)
            .expect("compiled protocol exists");
        Ok(PreparedAnalysis {
            graph: QualifierPropagation::from_dag(graph),
        })
    }
}

impl<C: AnalysisBackend> PreparedAnalysis<C> {
    /// Prepared graph for lower-level `build_inputs` / `try_from_inputs` / `run` control.
    #[must_use]
    pub const fn graph(&self) -> &Dag<C, Qualifier> {
        &self.graph
    }

    /// Encode and run one pass with an explicitly selected Gröbner-basis backend.
    ///
    /// Graph construction and qualifier propagation have already completed. This call
    /// includes polynomial input construction, basis computation and the pass's checks.
    ///
    /// # Errors
    /// Returns an analysis finding, invalid soundness parameters or a backend error.
    #[allow(clippy::result_large_err)]
    pub fn run(
        &self,
        analysis: Analysis<'_>,
        backend: GbBackendKind,
    ) -> Result<(), AnalysisError<C>> {
        match analysis {
            Analysis::Completeness => CompletenessAnalysis::try_from_inputs(
                CompletenessAnalysis::build_inputs(&self.graph),
                backend,
            )?
            .run(),
            Analysis::Zk => KnowledgeAnalysis::try_from_inputs(
                KnowledgeAnalysis::build_inputs(&self.graph),
                backend,
            )?
            .run(),
            Analysis::Soundness(rounds) => SpecialSoundnessAnalysis::try_from_inputs(
                SpecialSoundnessAnalysis::build_inputs(&self.graph, rounds.to_vec())?,
                backend,
            )?
            .run(),
        }
    }
}
