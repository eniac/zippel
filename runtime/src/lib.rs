//! Execution engine for compiled Zippel protocols.
//!
//! This is the last stage of the pipeline: a scheduled `TDag` is wrapped in a
//! [`MutexGraph`], whose nodes carry atomic readiness counters and write-once
//! value slots. `MutexGraph::run_graph` then drives the DAG, running pure
//! compute nodes on `rayon` workers while keeping Fiat-Shamir sponge
//! operations (instance inputs, transcript messages, challenges) sequential on
//! the main thread so prover and verifier transcripts stay in lockstep.

/// Typed failures raised while validating inputs or executing a graph.
pub mod error;
/// Runtime graph representation and the parallel execution loop.
pub mod graph;

mod queue;
pub use error::RuntimeError;
pub use graph::{MutexGraph, RunResult};

#[cfg(test)]
mod tests;
