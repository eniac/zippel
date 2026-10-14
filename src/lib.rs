//! Compile, execute and analyze cryptographic protocols written in Zippel.
//!
//! [`ParsedModule`] owns parsed source and exposes its size parameters.
//! [`ParsedModule::compile`] returns a [`CompiledProtocol`] ready to prove and verify.
//! [`CompiledProtocol::prepare_analysis`] lowers relations and propagates qualifiers,
//! returning a [`PreparedAnalysis`] that can run several passes without further graph work.
//! All source and execution errors are returned to the caller; the library does not exit.

mod analysis;
mod compiler;
mod execution;

pub use analysis::{Analysis, PreparedAnalysis};
pub use compiler::{CompileError, CompileOptions, CompiledProtocol, ParsedModule};

// Re-export workspace crates so library users only need a dependency on zippel.
pub use analyses;
pub use backend;
pub use graph;
pub use lang;
pub use runtime;
pub use share;

use backend::{ArkConfig, Value, value_to_bytes};

/// Interpret verifier output as pass/fail.
/// Passes if every Check in the output returned `true`.
#[must_use]
pub fn check_verification(outputs: &[bool]) -> bool {
    outputs.iter().all(|b| *b)
}

/// Compute the total serialized size (in bytes) of a proof certificate.
pub fn proof_size_bytes<C: ArkConfig>(proof: &[Value<C>]) -> usize {
    proof
        .iter()
        .filter_map(|v| value_to_bytes(v).ok())
        .map(|b| b.len())
        .sum()
}

#[cfg(test)]
mod tests;
