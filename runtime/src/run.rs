//! One execution of a [`MutexGraph`]: every node runs as a job of one
//! `rayon::scope` as soon as its dependencies have finished.

use backend::{Backend, Value};
use graph::{ArgKind, Node, Op};
use lang::id::Vid;
use log::debug;
use petgraph::graph::NodeIndex;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::collections::HashMap;
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};

use crate::error::RuntimeError;
use crate::graph::MutexGraph;
use crate::transcript::Transcript;

/// Specifies what kind of result to collect from graph execution.
///
/// Prover graphs collect proof transcript values (non-challenge),
/// while verifier graphs collect Check node values.
#[derive(Clone, Copy)]
pub enum ResultKind {
    /// Collect proof transcript values in transcript order for the prover.
    Prover,
    /// Collect Check node values for the verifier.
    Verifier,
}

/// Result of `run_graph`, parameterized by the role.
///
/// - `Prover`: proof transcript values in transcript order.
/// - `Verifier`: per-Verify pass/fail booleans.
#[derive(Debug)]
pub enum RunResult<C: Backend> {
    /// Proof transcript values emitted by the prover, in transcript order.
    Prover(Vec<Value<C>>),
    /// Outcome of the verifier graph's checks.
    Verifier {
        /// One boolean per `Op::Verify` op node, in node-index order; the
        /// protocol verifies iff every entry is `true`.
        verify_results: Vec<bool>,
    },
}

/// The first error of a run. The first task to fail records it; tasks that
/// start afterwards do nothing, so the run drains and `run_graph` returns
/// the error.
#[derive(Default)]
struct FirstError(Mutex<Option<RuntimeError>>);

impl FirstError {
    /// Records `err` unless an earlier task already recorded one.
    fn record(&self, err: RuntimeError) {
        self.0.lock().unwrap().get_or_insert(err);
    }

    fn is_set(&self) -> bool {
        self.0.lock().unwrap().is_some()
    }

    fn into_inner(self) -> Option<RuntimeError> {
        self.0.into_inner().unwrap()
    }
}

/// One execution of a graph.
///
/// The scope returns when the last job does: no thread waits or polls for
/// work, and the run computes on exactly the pool's threads.
struct Run<'a, C: Backend, H: DuplexSpongeInterface<U = u8>> {
    graph: &'a MutexGraph<C>,
    /// The run's inputs, each taken out when its `Arg` node delivers it, so
    /// an input the caller gave up is freed after its last reader.
    inputs: Mutex<HashMap<Vid, Value<C>>>,
    /// Every supplied input name, for error messages.
    names: Vec<Vid>,
    error: FirstError,
    transcript: Mutex<Transcript<'a, C, H>>,
    /// Whether each `Verify` node's checks passed, as they run.
    checks: Mutex<HashMap<NodeIndex, bool>>,
}

impl<C: Backend, H: DuplexSpongeInterface<U = u8> + Send> Run<'_, C, H> {
    /// Runs the ready `node`, then releases its successors.
    ///
    /// # Panics
    /// Panics if `node` has already run (a scheduling bug), or as
    /// [`MutexGraph::evaluate`] does.
    fn run_node<'s>(&'s self, scope: &rayon::Scope<'s>, node: NodeIndex) {
        // Once a task has failed the run is abandoned.
        if self.error.is_set() {
            return;
        }
        // Every node, challenges included: a challenge run twice would
        // squeeze the sponge twice.
        let state = self
            .graph
            .state(node)
            .unwrap_or_else(|| unreachable!("marker {node:?} scheduled as a job"));
        assert!(
            !state.executed.swap(true, Ordering::SeqCst),
            "runtime invariant violation: node {node:?} executed twice"
        );
        let value = match &self.graph.dag[node] {
            Node::Transcr(op, _) if matches!(**op, Op::Challenge(_, _)) => {
                debug!("[run_graph] node {node:?} is Challenge");
                let exclusion = self.graph.evaluate_exclusion(node);
                self.transcript
                    .lock()
                    .unwrap()
                    .challenge(exclusion.as_ref())
            }
            Node::Op(op, _) if matches!(**op, Op::Challenge(_, _)) => {
                unreachable!("challenge {node:?} outside the transcript")
            }
            Node::Op(_, _) => {
                let Some(value) = self.evaluate(node) else {
                    return;
                };
                value
            }
            Node::Transcr(op, _) => {
                debug!("[run_graph] node {node:?} is Transcript");
                // Computed outside the lock; only the sponge bookkeeping is
                // in it.
                let Some(value) = self.evaluate(node) else {
                    return;
                };
                // The type checker guarantees it; a verifier's message is a
                // proof element `run_verifier` has already checked.
                debug_assert!(
                    value.conforms_to(&op.typ()),
                    "message {node:?} is not a value of its type {}: {value}",
                    op.typ()
                );
                self.transcript.lock().unwrap().message(node, &value);
                value
            }
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => {
                unreachable!("marker {node:?} scheduled as a job")
            }
        };
        self.release_successors(scope, node, Some(&value));
    }

    /// Evaluates `node`, recording the outcome of any checks it evaluated, or
    /// records the run's error and returns `None` if it fails.
    fn evaluate(&self, node: NodeIndex) -> Option<Value<C>> {
        match self.graph.evaluate(node) {
            Ok((value, passed)) => {
                if let Some(passed) = passed {
                    self.checks.lock().unwrap().insert(node, passed);
                }
                Some(value)
            }
            Err(err) => {
                self.error.record(err);
                None
            }
        }
    }

    /// Queues the instance inputs of the `Inp` marker `node` for the sponge,
    /// in argument order, then releases its successors.
    ///
    /// # Errors
    /// [`RuntimeError::MissingArg`] if an instance input was not supplied.
    fn absorb_inputs<'s>(
        &'s self,
        scope: &rayon::Scope<'s>,
        node: NodeIndex,
    ) -> Result<(), RuntimeError> {
        let mut transcript = self.transcript.lock().unwrap();
        // Successors are sorted, so arguments are in node-index order.
        for &arg in self.graph.successors(node) {
            if let Node::Arg(name, _, qual, _, kind) = &self.graph.dag[arg]
                && qual.is_instance()
                && !matches!(kind, ArgKind::TranscriptInput)
            {
                let Some(value) = self.inputs.lock().unwrap().get(name).cloned() else {
                    let err = RuntimeError::missing_arg(name, &self.names);
                    self.error.record(err.clone());
                    return Err(err);
                };
                transcript.instance(value);
            }
        }
        drop(transcript);
        self.release_successors(scope, node, None);
        Ok(())
    }

    /// Hands the finished `node`'s `value` (if it has one) to each successor
    /// and runs the successors that are now ready. An `Arg` successor is
    /// passed through: it finishes at once with its input value.
    fn release_successors<'s>(
        &'s self,
        scope: &rayon::Scope<'s>,
        node: NodeIndex,
        value: Option<&Value<C>>,
    ) {
        for &successor in self.graph.successors(node) {
            match &self.graph.dag[successor] {
                Node::Op(_, state) | Node::Transcr(_, state) => {
                    if state.receive(node, value) {
                        scope.spawn(move |scope| self.run_node(scope, successor));
                    }
                }
                // Each input feeds one `Arg` node (checked in
                // `MutexGraph::new`).
                Node::Arg(vid, _, _, _, _) => {
                    let input = {
                        let mut inputs = self.inputs.lock().unwrap();
                        let input = inputs.remove(vid);
                        // Once every input is handed out, free the map's
                        // storage rather than keep it for the whole run.
                        if inputs.is_empty() {
                            *inputs = HashMap::new();
                        }
                        input
                    };
                    match input {
                        Some(input) => self.release_successors(scope, successor, Some(&input)),
                        None => self
                            .error
                            .record(RuntimeError::missing_arg(vid, &self.names)),
                    }
                }
                Node::Inp(_) | Node::Rel(_) => {
                    unreachable!("Inp/Rel marker {successor:?} follows node {node:?}")
                }
            }
        }
    }
}

impl<C: Backend> MutexGraph<C> {
    /// Execute all nodes in the DAG, each as soon as its dependencies have
    /// finished, in parallel on the rayon pool.
    ///
    /// # Readiness tracking
    ///
    /// Each compute node carries an atomic counter of its unfinished
    /// distinct predecessors. When a node finishes, it delivers its value
    /// into the inbox of each distinct successor that reads it and
    /// decrements that successor's counter; a successor whose counter
    /// reaches zero is spawned as a job of the run's `rayon::scope`. A value
    /// is freed once every node reading it has run.
    ///
    /// # Inputs
    ///
    /// The run owns `inputs`. Each is handed to its `Arg` node's readers and
    /// dropped from the run, so an input whose buffers the caller does not
    /// share (a witness passed without keeping a clone) is freed after its
    /// last reader. A caller that keeps a clone (an SRS reused across runs)
    /// shares the buffers, which are then never freed or written in place.
    ///
    /// # Execution
    ///
    /// The whole run is one `rayon::scope`, so it computes on exactly the
    /// pool's threads; the calling thread only waits, and the scope returns
    /// when the last node has run. No thread waits or polls for ready work.
    ///
    /// # Sponge synchronization
    ///
    /// The input marker runs first: the instance inputs it queues begin the
    /// transcript. Transcript nodes (messages and challenges) then share the
    /// sponge through a mutex; the graph chains them in transcript order, so
    /// only one is ever ready, and a message is computed outside the lock.
    ///
    /// # Returns
    ///
    /// - For `ResultKind::Prover`: `RunResult::Prover(Vec<Value<C>>)` — proof
    ///   transcript values in transcript order.
    /// - For `ResultKind::Verifier`: `RunResult::Verifier { verify_results }` —
    ///   per-Verify pass/fail booleans.
    ///
    /// # Errors
    ///
    /// Returns [`RuntimeError::MissingArg`] if an `Arg` node references an
    /// input the caller did not supply.
    ///
    /// # Panics
    ///
    /// Panics if a node is executed twice, runs without an operand (see
    /// [`MutexGraph::evaluate`]) or, with debug assertions and no error,
    /// never runs; if a transcript value cannot be serialized for the
    /// sponge, or if a mutex is poisoned.
    pub fn run_graph<H: DuplexSpongeInterface<U = u8> + Send>(
        g: Arc<Self>,
        inputs: HashMap<Vid, Value<C>>,
        prover_state: &mut ProverState<H>,
        result_kind: ResultKind,
    ) -> Result<RunResult<C>, RuntimeError> {
        debug!(
            "[run_graph] total nodes={}, roots={}",
            g.dag.node_count(),
            g.roots().len()
        );
        let run = Run {
            graph: &g,
            names: inputs.keys().cloned().collect(),
            inputs: Mutex::new(inputs),
            error: FirstError::default(),
            transcript: Mutex::new(Transcript::new(
                prover_state,
                matches!(result_kind, ResultKind::Prover),
            )),
            checks: Mutex::new(HashMap::new()),
        };
        rayon::scope(|scope| {
            // See "Sponge synchronization" above.
            if let Some(input) = g.input() {
                run.absorb_inputs(scope, input)?;
            }
            for &root in g.roots() {
                let run = &run;
                scope.spawn(move |scope| run.run_node(scope, root));
            }
            Ok(())
        })?;
        let Run {
            error,
            transcript,
            checks,
            ..
        } = run;

        // A task may have recorded an error; surface it before collecting.
        if let Some(err) = error.into_inner() {
            return Err(err);
        }
        // Without an error every node ran. Debug builds only (tests run with
        // debug assertions): soundness does not rest on it, since a check with
        // no result fails below and a missing message shortens the proof.
        debug_assert!(
            g.states().all(|s| s.executed.load(Ordering::SeqCst)),
            "runtime invariant violation: a node never ran"
        );
        debug_assert!(
            g.states().all(|s| s.inbox.is_empty()),
            "a delivered value was never taken"
        );

        Ok(match result_kind {
            ResultKind::Prover => {
                let mut messages = transcript.into_inner().unwrap().into_messages();
                // Every reader of a message has run, so each is usually
                // held only here and moves into the proof without a copy. A
                // message that views part of a vector is copied out of it:
                // the proof outlives the run and would keep the whole vector.
                RunResult::Prover(
                    g.dag
                        .transcript_nodes()
                        .into_iter()
                        .filter_map(|n| messages.remove(&n))
                        .map(Value::compact)
                        .collect(),
                )
            }
            ResultKind::Verifier => {
                let checks = checks.into_inner().unwrap();
                RunResult::Verifier {
                    verify_results: g
                        .checks()
                        .iter()
                        // A check with no result failed (none should be
                        // missing once every node has run).
                        .map(|n| checks.get(n).copied().unwrap_or(false))
                        .collect(),
                }
            }
        })
    }
}
