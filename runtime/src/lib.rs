//! Execution engine for compiled Zippel protocols.
//!
//! This is the last stage of the pipeline: a scheduled `TDag` is wrapped in a
//! [`MutexGraph`], whose nodes carry atomic readiness counters and inboxes of
//! the operands they read. `MutexGraph::run_graph` then drives the DAG in one
//! `rayon::scope`, running every node as soon as its dependencies finish, while
//! Fiat-Shamir sponge operations (instance inputs, transcript messages,
//! challenges) stay in transcript order so prover and verifier transcripts
//! stay in lockstep.

/// Typed failures raised while validating inputs or executing a graph.
pub mod error;
/// Runtime graph representation and the parallel execution loop.
pub mod graph;

mod inbox;
/// A protocol's named inputs, shared rather than copied by each run.
pub mod inputs;
pub use error::RuntimeError;
pub use graph::{MutexGraph, RunResult};
pub use inputs::Inputs;

#[cfg(test)]
mod tests;
