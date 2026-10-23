//! The IR: the typed operations a `graph` DAG is made of, and their types.

/// The typed IR operation enum `Op<C, R>` and its hash-consing factory.
pub mod op;
/// The IR type level: `ATyp`/`ABase` and conversion from source-level `CTyp`.
pub mod types;
