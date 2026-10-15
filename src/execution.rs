//! Prover and verifier execution with input and transcript validation.
use crate::CompiledProtocol;
use backend::{ATyp, ArkConfig, HasOpFactory, Value};
use graph::{ArgKind, Node, domain_seperator::ZippelDomainSeparator};
use lang::id::Vid;
use runtime::{MutexGraph, ResultKind, RunResult, RuntimeError};
use std::{collections::HashMap, sync::Arc};

impl<C: ArkConfig + HasOpFactory> CompiledProtocol<C> {
    /// Run prover, takes inputs by name and returns proof.
    ///
    /// The run owns the values it is passed and frees each after its last
    /// reader. A `Value` is a handle: cloning one shares its buffers and
    /// copies no data, so an input the caller reuses across runs (an SRS, a
    /// proving key) is lent by passing a clone, and the run never frees the
    /// caller's buffers; an input passed without keeping a clone (a fresh
    /// witness) is given.
    ///
    /// # Errors
    /// Returns [`RuntimeError::MissingInputs`] if expected inputs are missing,
    /// and [`RuntimeError::MalformedInput`] if an input is not a value of its
    /// argument's declared type.
    ///
    pub fn prove<K: Into<Vid>>(
        &self,
        inputs: impl IntoIterator<Item = (K, Value<C>)>,
    ) -> Result<Vec<Value<C>>, RuntimeError> {
        let inputs: HashMap<Vid, Value<C>> =
            inputs.into_iter().map(|(k, v)| (k.into(), v)).collect();
        let prover = &self.prover_graph;

        // The arguments the caller supplies, with their types.
        // Transcript-sourced args are produced internally.
        let caller_args: Vec<(&Vid, &ATyp)> = prover
            .input_args()
            .into_iter()
            .filter_map(|n| match &prover[n] {
                Node::Arg(name, typ, _, _, ArgKind::Input) => Some((name, typ)),
                _ => None,
            })
            .collect();

        // Validate that every prover argument expected from the caller is
        // present in `inputs`, and of its declared type. Without this check,
        // a typo or mismatch between the protocol declaration and the
        // call-site `inputs` map surfaces deep inside the runtime as an
        // opaque panic, or a wrong-length vector is silently computed on.
        let expected_args: Vec<Vid> = caller_args
            .iter()
            .map(|(name, _)| (*name).clone())
            .collect();
        let missing: Vec<&Vid> = expected_args
            .iter()
            .filter(|v| !inputs.contains_key(v))
            .collect();
        if !missing.is_empty() {
            return Err(RuntimeError::missing_inputs(
                missing.iter().copied(),
                expected_args.iter(),
                inputs.keys(),
            ));
        }
        check_input_types(caller_args, &inputs)?;

        let domain_separator_session = self.domain_separator_session();
        let prover_seperator = ZippelDomainSeparator::new_zippel_domain_seperator(
            domain_separator_session,
            &prover.clone(),
        );

        let mut prover_state = prover_seperator.prover_state();
        let result = MutexGraph::run_graph(
            Arc::new(MutexGraph::new(prover.clone())),
            inputs,
            &mut prover_state,
            ResultKind::Prover,
        )?;
        match result {
            RunResult::Prover(transcript) => Ok(transcript),
            RunResult::Verifier { .. } => {
                unreachable!("prove with ResultKind::Prover")
            }
        }
    }

    /// Run verifier, returning `true` if every verification check passes.
    /// Proof values and inputs are owned as in [`Self::prove`];
    /// inputs that are not instance arguments are dropped unread.
    ///
    /// # Errors
    /// Returns [`RuntimeError::ProofLength`] unless the proof has exactly one
    /// element per prover message, [`RuntimeError::MalformedProof`] if an
    /// element is not a value of its message's declared type,
    /// [`RuntimeError::MalformedInput`] if an instance input is not a value of
    /// its argument's declared type, and other `RuntimeError`s if the run
    /// fails (e.g. a missing instance input). A
    /// proof that runs but fails a check returns `Ok(false)`.
    ///
    pub fn verify<K: Into<Vid>>(
        &self,
        proof: impl IntoIterator<Item = Value<C>>,
        inputs: impl IntoIterator<Item = (K, Value<C>)>,
    ) -> Result<bool, RuntimeError> {
        let verifier = &self.verifier_graph;

        // Instance inputs: filter by qual.is_instance() from verifier graph,
        // each checked against its declared type.
        let instance_args: Vec<(&Vid, &ATyp)> = verifier
            .input_args()
            .into_iter()
            .filter_map(|n| match &verifier[n] {
                Node::Arg(name, typ, qual, _, ArgKind::Input) if qual.is_instance() => {
                    Some((name, typ))
                }
                _ => None,
            })
            .collect();
        let instance_inputs: HashMap<Vid, Value<C>> = inputs
            .into_iter()
            .map(|(k, v)| (k.into(), v))
            .filter(|(vid, _)| instance_args.iter().any(|(name, _)| *name == vid))
            .collect();
        check_input_types(instance_args, &instance_inputs)?;

        // Transcript inputs: the prover messages, one proof element each, in
        // order. The proof comes from outside, so its shape is checked here:
        // the graph assumes every value has its declared type.
        let transcript_args: Vec<(&Vid, &ATyp)> = verifier
            .input_args()
            .into_iter()
            .filter_map(|n| match &verifier[n] {
                Node::Arg(name, typ, _, _, ArgKind::TranscriptInput) => Some((name, typ)),
                _ => None,
            })
            .collect();
        let proof: Vec<Value<C>> = proof.into_iter().collect();
        if proof.len() != transcript_args.len() {
            return Err(RuntimeError::ProofLength {
                expected: transcript_args.len(),
                found: proof.len(),
            });
        }
        for (index, ((name, typ), value)) in transcript_args.iter().zip(&proof).enumerate() {
            if !value.conforms_to(typ) {
                return Err(RuntimeError::MalformedProof {
                    index,
                    message: name.to_string(),
                    expected: typ.to_string(),
                });
            }
        }
        let transcript_inputs = transcript_args
            .into_iter()
            .map(|(name, _)| name.clone())
            .zip(proof);

        let mut all_inputs = instance_inputs;
        all_inputs.extend(transcript_inputs);

        let domain_separator_session = self.domain_separator_session();
        let verifier_seperator = ZippelDomainSeparator::new_zippel_domain_seperator(
            domain_separator_session,
            &verifier.clone(),
        );
        // For now, use prover state since we don't have narg_string yet
        // TODO: Fix this to use proper verifier state when narg_string is available
        let mut verifier_state = verifier_seperator.prover_state();
        let result = MutexGraph::run_graph(
            Arc::new(MutexGraph::new(verifier.clone())),
            all_inputs,
            &mut verifier_state,
            ResultKind::Verifier,
        )?;
        match result {
            RunResult::Verifier { verify_results } => Ok(verify_results.iter().all(|b| *b)),
            RunResult::Prover { .. } => {
                unreachable!("verify with ResultKind::Verifier")
            }
        }
    }
}

/// Checks each supplied input against the type its argument declares, in
/// argument order; an argument with no input is left to the caller.
///
/// # Errors
/// [`RuntimeError::MalformedInput`] for the first input that is not a value
/// of its argument's type.
fn check_input_types<'a, C: ArkConfig>(
    args: impl IntoIterator<Item = (&'a Vid, &'a ATyp)>,
    inputs: &HashMap<Vid, Value<C>>,
) -> Result<(), RuntimeError> {
    for (name, typ) in args {
        if let Some(value) = inputs.get(name)
            && !value.conforms_to(typ)
        {
            return Err(RuntimeError::MalformedInput {
                name: name.to_string(),
                expected: typ.to_string(),
            });
        }
    }
    Ok(())
}
