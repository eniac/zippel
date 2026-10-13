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
/// The executable graph: per-node run state and precomputed scheduling
/// tables.
pub mod graph;

mod inbox;
mod run;
mod transcript;
pub use error::RuntimeError;
pub use graph::MutexGraph;
pub use run::{ResultKind, RunResult};

#[cfg(test)]
mod tests;
