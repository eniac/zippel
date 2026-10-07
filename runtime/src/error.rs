use lang::id::Vid;
use thiserror::Error;

/// Errors raised by the Zippel runtime during graph execution.
#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    /// One or more inputs declared by the protocol signature were not
    /// supplied in the `inputs` map passed to `run_prover` / `run_verifier`.
    ///
    /// Surfaced by the upfront validation in
    /// [`ZippelHandler::run_prover`](../../src/lib.rs.html) before any graph
    /// execution begins; this is the user-facing error for a typo or schema
    /// mismatch between the `.zippel` `proto`/`fn` signature and the caller.
    #[error(
        "missing input value(s) for protocol argument(s): [{missing_str}].\n  \
         expected (from the protocol declaration): [{expected_str}]\n  \
         provided (in the `inputs` map):          [{provided_str}]\n  \
         hint: the names in `inputs` must match the parameter \
         names in the .zippel `proto`/`fn` signature exactly.",
        missing_str = missing.join(", "),
        expected_str = expected.join(", "),
        provided_str = provided.join(", "),
    )]
    MissingInputs {
        /// Declared parameter names with no entry in the `inputs` map.
        missing: Vec<String>,
        /// Every parameter name the protocol/function signature declares.
        expected: Vec<String>,
        /// Every key the caller actually supplied, for diffing against
        /// `expected`.
        provided: Vec<String>,
    },

    /// During graph execution an `Arg` node referenced a `Vid` that was
    /// absent from the `inputs` map.
    ///
    /// Upstream validation should normally catch this before execution
    /// starts; raising it here as a typed error rather than a panic means
    /// a programming mistake (e.g. invoking `run_graph` directly without
    /// validation, or a future scheduling bug) surfaces cleanly.
    #[error(
        "missing input value for protocol argument `{vid}` during graph \
         execution. provided: [{provided_str}]. The keys must match the \
         parameter names in the .zippel signature exactly.",
        provided_str = provided.join(", "),
    )]
    MissingArg {
        /// Rendered `Vid` of the `Arg` node whose value could not be found.
        vid: String,
        /// Keys present in the `inputs` map at the time of the lookup.
        provided: Vec<String>,
    },

    /// The proof passed to `run_verifier` does not have one element per
    /// prover message of the protocol.
    #[error("the proof has {found} element(s); the protocol's prover sends {expected} message(s)")]
    ProofLength {
        /// The protocol's number of prover messages.
        expected: usize,
        /// The proof's number of elements.
        found: usize,
    },

    /// A proof element is not a value of the type the protocol declares for
    /// that prover message.
    #[error("proof element {index} (message `{message}`) is not a value of type {expected}")]
    MalformedProof {
        /// The element's position in the proof.
        index: usize,
        /// The prover message it stands for.
        message: String,
        /// The message's declared type.
        expected: String,
    },
}

impl RuntimeError {
    /// Build a [`RuntimeError::MissingInputs`] from `Vid` iterators.
    pub fn missing_inputs<'a, M, E, P>(missing: M, expected: E, provided: P) -> Self
    where
        M: IntoIterator<Item = &'a Vid>,
        E: IntoIterator<Item = &'a Vid>,
        P: IntoIterator<Item = &'a Vid>,
    {
        RuntimeError::MissingInputs {
            missing: missing.into_iter().map(ToString::to_string).collect(),
            expected: expected.into_iter().map(ToString::to_string).collect(),
            provided: provided.into_iter().map(ToString::to_string).collect(),
        }
    }

    /// Build a [`RuntimeError::MissingArg`] for a single `Vid` lookup
    /// against a `Ctx`-like iterator of provided keys.
    pub fn missing_arg<'a, P>(vid: &Vid, provided: P) -> Self
    where
        P: IntoIterator<Item = &'a Vid>,
    {
        RuntimeError::MissingArg {
            vid: vid.to_string(),
            provided: provided.into_iter().map(ToString::to_string).collect(),
        }
    }
}
