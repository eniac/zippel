use backend::{ArkConfig, Value, value_to_bytes};
use graph::{ArgKind, Dag, GOp, Node, Op, UDag};
use log::debug;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use rand::rngs::ThreadRng;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::error::RuntimeError;
use crate::inbox::Inbox;
use crate::inputs::Inputs;

/// Size threshold (in bytes of serialized form) above which an instance
/// input is absorbed into the Fiat-Shamir sponge via a Blake3 digest
/// instead of its raw byte representation.
///
/// At M=12 each Spartan R1CS matrix is 16M field elements × 32 B = 512 MB.
/// Sponge-absorbing 1.5 GB of matrix bytes was costing ~3 s per prove. The
/// digest path streams through a Blake3 hasher (single 32 B sponge absorb)
/// and never holds the full serialized buffer in the sponge.
///
/// Both prover and verifier graphs flow through `run_graph`, so they
/// apply this threshold symmetrically — sponge state stays in sync.
const FS_DIGEST_THRESHOLD_BYTES: usize = 64 * 1024;

/// Domain separator for the Blake3 digest path. Hashing context-prefix
/// + value bytes prevents a digest from being confused with raw value
///   bytes if both schemes were ever fed into the same sponge.
const FS_DIGEST_DOMAIN: &[u8] = b"zippel-fs-pubinp-digest-v1";

/// Absorb an instance input value into the Fiat-Shamir sponge.
///
/// For values below `FS_DIGEST_THRESHOLD_BYTES`, serialize as before
/// (preserves transcript bytes for existing small-input protocols). For
/// large values, stream the serialized bytes through a Blake3 hasher and
/// absorb the 32-byte digest — symmetric on prover and verifier sides.
fn absorb_instance_input<C: ArkConfig, H>(prover_state: &mut ProverState<H>, value: &Value<C>)
where
    H: DuplexSpongeInterface<U = u8>,
{
    let bytes = value_to_bytes(value).expect("value serialization should not fail");
    if bytes.len() > FS_DIGEST_THRESHOLD_BYTES {
        let mut hasher = blake3::Hasher::new();
        hasher.update(FS_DIGEST_DOMAIN);
        hasher.update(&bytes);
        let digest = hasher.finalize();
        prover_state.public_message(digest.as_bytes());
    } else {
        prover_state.public_message(bytes.as_slice());
    }
}

/// A value queued for the Fiat-Shamir sponge, absorbed before the next
/// challenge (see [`Transcript`]).
enum PendingAbsorb<C: ArkConfig> {
    /// An instance input, absorbed with [`absorb_instance_input`].
    Instance(Arc<Value<C>>),
    /// A prover message, absorbed as its serialized bytes.
    Message(Arc<Value<C>>),
}

/// The first error of a run. The first task to fail records it here; tasks
/// that start afterwards do nothing, so the run drains and `run_graph`
/// returns the error.
type ErrorSlot = Mutex<Option<RuntimeError>>;

/// Record `err` into `slot` if no earlier task has already done so.
fn record_error(slot: &ErrorSlot, err: RuntimeError) {
    let mut guard = slot.lock().unwrap();
    if guard.is_none() {
        *guard = Some(err);
    }
}

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
pub enum RunResult<C: ArkConfig> {
    /// Proof transcript values emitted by the prover, in transcript order.
    Prover(Vec<Value<C>>),
    /// Outcome of the verifier graph's checks.
    Verifier {
        /// One boolean per `Op::Verify` op node, in node-index order; the
        /// protocol verifies iff every entry is `true`.
        verify_results: Vec<bool>,
    },
}

/// Runtime information attached to each Op/Transcr node in the DAG.
///
/// A node never stores its own value: when it finishes, it delivers the
/// value into the [`Inbox`] of each successor that reads it, and the value
/// is freed once the last of them has run.
///
/// `remaining_deps` uses atomic operations for lock-free counter-based
/// readiness tracking: when a node's dependencies finish, they decrement
/// its counter; when the counter reaches zero, the node is ready to execute.
pub struct RuntimeInformation<C: ArkConfig> {
    /// Operands delivered by the nodes this one reads; taken when it runs.
    inbox: Inbox<Value<C>>,
    /// Set when the node runs, to catch a scheduler running it twice.
    executed: AtomicBool,
    /// Number of unfinished dependencies. Atomically decremented;
    /// when it reaches zero, this node is ready to execute.
    pub remaining_deps: AtomicUsize,
}

impl<C: ArkConfig> RuntimeInformation<C> {
    /// Runtime state for a not-yet-executed node computing `op`: an empty
    /// inbox for the nodes `op` reads, and a zero dependency counter that
    /// `run_graph` sets to the node's unique-predecessor count.
    pub fn new(op: &GOp<C>) -> Self {
        RuntimeInformation {
            inbox: Inbox::new(op.references()),
            executed: AtomicBool::new(false),
            remaining_deps: AtomicUsize::new(0),
        }
    }

    /// Records that the predecessor `from` has finished, taking its value if
    /// it produced one, and returns whether this node is now ready to run.
    fn receive(&self, from: NodeIndex, value: Option<&Arc<Value<C>>>) -> bool {
        if let Some(value) = value {
            self.inbox.deliver(graph::Ref(from), value);
        }
        self.remaining_deps.fetch_sub(1, Ordering::SeqCst) == 1
    }
}

/// A [`UDag`] whose per-node annotation is the shared [`RuntimeInformation`]
/// used to execute it.
///
/// This is the final stage of the pipeline: a scheduled DAG wrapped with
/// enough interior mutability (operand inboxes, atomic dependency counters,
/// a mutex-guarded check map) that the jobs of one `rayon::scope` can drive
/// it concurrently.
pub struct MutexGraph<C: ArkConfig> {
    mutex_graph: Dag<C, Arc<RuntimeInformation<C>>>,
    /// Auxiliary map storing pass/fail results for `Op::Verify` nodes.
    /// Populated by `handle_node` when a Verify node is evaluated;
    /// `run_graph` collects from it for `ResultKind::Verifier`.
    check_results: Mutex<HashMap<NodeIndex, bool>>,
}

/// The Fiat-Shamir side of one run: the sponge, the values queued for it,
/// and, for the prover, the messages that form the proof.
///
/// Transcript nodes use it one at a time: the graph chains them in
/// transcript order, so only one is ever ready.
struct Transcript<'a, C: ArkConfig, H: DuplexSpongeInterface<U = u8>> {
    sponge: &'a mut ProverState<H>,
    /// Absorbed, in order, only when a challenge is squeezed: the sponge's
    /// only output is challenges, so values after the last challenge (every
    /// value, in a protocol with no challenges) never need serializing.
    pending: Vec<PendingAbsorb<C>>,
    /// Prover messages by node, for the proof; `None` for the verifier.
    messages: Option<HashMap<NodeIndex, Arc<Value<C>>>>,
}

impl<C: ArkConfig, H: DuplexSpongeInterface<U = u8>> Transcript<'_, C, H> {
    /// Queues a prover message for the sponge, and keeps it for the proof.
    fn message(&mut self, node: NodeIndex, value: &Arc<Value<C>>) {
        self.pending.push(PendingAbsorb::Message(Arc::clone(value)));
        if let Some(messages) = &mut self.messages {
            messages.insert(node, Arc::clone(value));
        }
    }

    /// Absorbs everything queued, then squeezes a challenge.
    fn challenge(&mut self) -> Value<C> {
        for p in self.pending.drain(..) {
            match p {
                PendingAbsorb::Instance(v) => absorb_instance_input::<C, H>(self.sponge, &v),
                PendingAbsorb::Message(v) => {
                    let serialized = value_to_bytes(&*v).unwrap();
                    self.sponge.public_message(serialized.as_slice());
                }
            }
        }
        Value::<C>::challenge(self.sponge)
    }
}

/// One execution of a graph.
///
/// Every node runs as a job of one `rayon::scope` as soon as its
/// dependencies have finished, and the scope returns when the last job does:
/// no thread waits or polls for work, and the run computes on exactly the
/// pool's threads.
struct Run<'a, C: ArkConfig, H: DuplexSpongeInterface<U = u8>> {
    graph: &'a MutexGraph<C>,
    inputs: &'a Inputs<C>,
    errors: ErrorSlot,
    transcript: Mutex<Transcript<'a, C, H>>,
}

impl<C: ArkConfig, H: DuplexSpongeInterface<U = u8> + Send> Run<'_, C, H> {
    /// Runs the ready `node`, then releases its successors.
    ///
    /// # Panics
    /// Panics if `node` has already run (a scheduling bug), or as
    /// [`MutexGraph::handle_node`] does.
    fn run_node<'s>(&'s self, scope: &rayon::Scope<'s>, node: NodeIndex) {
        // Once a task has failed the run is abandoned.
        if self.errors.lock().unwrap().is_some() {
            return;
        }
        // Every node, challenges included: a challenge run twice would
        // squeeze the sponge twice.
        let info = self
            .graph
            .info(node)
            .unwrap_or_else(|| unreachable!("marker {node:?} scheduled as a job"));
        assert!(
            !info.executed.swap(true, Ordering::SeqCst),
            "runtime invariant violation: node {node:?} executed twice"
        );
        let value = match &self.graph.mutex_graph[node] {
            Node::Op(op, _) if matches!(**op, Op::Challenge(_, _)) => {
                unreachable!("challenge {node:?} outside the transcript")
            }
            Node::Op(_, _) => self.graph.handle_node(node),
            Node::Transcr(op, _) if matches!(**op, Op::Challenge(_, _)) => {
                debug!("[run_graph] node {:?} is Challenge", node);
                Arc::new(self.transcript.lock().unwrap().challenge())
            }
            Node::Transcr(_, _) => {
                debug!("[run_graph] node {:?} is Transcript", node);
                // Computed outside the lock; only the sponge bookkeeping is
                // in it.
                let value = self.graph.handle_node(node);
                self.transcript.lock().unwrap().message(node, &value);
                value
            }
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => {
                unreachable!("marker {node:?} scheduled as a job")
            }
        };
        self.release_successors(scope, node, Some(&value));
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
        let mut args: Vec<NodeIndex> = self
            .graph
            .mutex_graph
            .nodes_from(node)
            .filter(|n| self.graph.mutex_graph[*n].is_arg())
            .collect();
        args.sort();
        let mut transcript = self.transcript.lock().unwrap();
        for arg in args {
            if let Node::Arg(name, _, qual, _, kind) = &self.graph.mutex_graph[arg]
                && qual.is_instance()
                && !matches!(kind, ArgKind::TranscriptInput)
            {
                let Some(value) = self.inputs.get(name) else {
                    let err = RuntimeError::missing_arg(name, self.inputs.names());
                    record_error(&self.errors, err.clone());
                    return Err(err);
                };
                transcript
                    .pending
                    .push(PendingAbsorb::Instance(Arc::clone(value)));
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
        value: Option<&Arc<Value<C>>>,
    ) {
        // A successor joined by parallel edges still counts `node` once.
        let successors: HashSet<NodeIndex> = self
            .graph
            .mutex_graph
            .neighbors_directed(node, Direction::Outgoing)
            .collect();
        for successor in successors {
            match &self.graph.mutex_graph[successor] {
                Node::Op(_, info) | Node::Transcr(_, info) => {
                    if info.receive(node, value) {
                        scope.spawn(move |scope| self.run_node(scope, successor));
                    }
                }
                Node::Arg(vid, _, _, _, _) => match self.inputs.get(vid) {
                    Some(input) => self.release_successors(scope, successor, Some(input)),
                    None => record_error(
                        &self.errors,
                        RuntimeError::missing_arg(vid, self.inputs.names()),
                    ),
                },
                Node::Inp(_) | Node::Rel(_) => {
                    unreachable!("Inp/Rel marker {:?} follows node {:?}", successor, node)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// MutexGraph implementation
// ---------------------------------------------------------------------------

impl<C: ArkConfig> MutexGraph<C> {
    /// Wrap a scheduled DAG for execution, replacing every node annotation
    /// with fresh [`RuntimeInformation`] and starting with an empty
    /// assert/verify result map.
    ///
    /// # Panics
    ///
    /// Panics if a node reads a node it has no dependency edge from: its
    /// operand would never be delivered.
    pub fn new(dag: UDag<C>) -> Self {
        let g = MutexGraph {
            mutex_graph: dag.map_annotations(&|op, _| Arc::new(RuntimeInformation::new(op))),
            check_results: Mutex::new(HashMap::new()),
        };
        for node in g.mutex_graph.node_indices() {
            if let Some(info) = g.info(node) {
                // Collected once per node: scanning the incoming edges for
                // each operand is quadratic in a node's operand count.
                let predecessors: HashSet<NodeIndex> = g
                    .mutex_graph
                    .neighbors_directed(node, Direction::Incoming)
                    .collect();
                for source in info.inbox.sources() {
                    assert!(
                        predecessors.contains(&source.0),
                        "node {node:?} reads {source:?} without a dependency edge from it"
                    );
                }
            }
        }
        g
    }

    /// The runtime state of a compute (`Op`/`Transcr`) node.
    fn info(&self, node: NodeIndex) -> Option<&RuntimeInformation<C>> {
        match &self.mutex_graph[node] {
            Node::Op(_, info) | Node::Transcr(_, info) => Some(info),
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => None,
        }
    }

    /// Log every edge of the graph at `debug` level, for diagnosing
    /// scheduling and readiness-counter problems.
    pub fn print_edges(&self) {
        for node in self.mutex_graph.node_indices() {
            for neighbor in self
                .mutex_graph
                .neighbors_directed(node, petgraph::Direction::Outgoing)
            {
                debug!("Edge from {:?} to {:?}", node, neighbor);
            }
        }
    }

    /// Execute one compute node: evaluate its op on the operands in its
    /// inbox, record any `Verify` outcome into the check map, and return the
    /// value for the caller to deliver to its successors.
    ///
    /// Evaluation goes through [`graph::eval::eval_op_owned`], which shares
    /// its semantics with the borrowing [`graph::eval::eval_op`] the test
    /// executors use, but moves each operand out on its last use so the op
    /// can reuse it.
    ///
    /// # Panics
    ///
    /// Panics if `node` is not an `Op`/`Transcr` node, if an operand was not
    /// delivered (a scheduling bug), if the
    /// check-results mutex is poisoned, or if `eval_op_owned` fails: every shape
    /// and type precondition is established by the `lang` type checker and
    /// the scheduler, so a failure is a compiler invariant violation.
    pub fn handle_node(&self, node: NodeIndex) -> Arc<Value<C>> {
        let (Node::Op(op, info) | Node::Transcr(op, info)) = &self.mutex_graph[node] else {
            unreachable!("marker node {node:?} has nothing to compute")
        };
        let env = info.inbox.take_all();
        let mut check_sink = Vec::new();
        let value = graph::eval::eval_op_owned(op, env, &mut ThreadRng::default(), &mut check_sink)
            .expect("runtime invariant violation: eval_op failed on a scheduled node");
        // A node passes only if every check it evaluated did (today there is
        // at most one): a later result must not overwrite a failure.
        if !check_sink.is_empty() {
            let passed = check_sink.iter().all(|&p| p);
            self.check_results.lock().unwrap().insert(node, passed);
        }
        value
    }

    /// Execute all nodes in the DAG, each as soon as its dependencies have
    /// finished, in parallel on the rayon pool.
    ///
    /// # Readiness tracking
    ///
    /// Each Op/Transcr node carries an atomic `remaining_deps` counter
    /// initialized to its number of unique predecessors. When a node
    /// finishes, it delivers its value into the inbox of each unique
    /// successor that reads it and decrements that successor's counter; a
    /// successor whose counter reaches zero is spawned as a job of the run's
    /// `rayon::scope`. A value is freed once every node reading it has run.
    ///
    /// # Execution
    ///
    /// The whole run is one `rayon::scope`, so it computes on exactly the
    /// pool's threads; the calling thread only waits, and the scope returns
    /// when the last node has run. No thread waits or polls for ready work.
    ///
    /// # Sponge synchronization
    ///
    /// The `Inp` marker runs first: the instance inputs it queues begin the
    /// transcript. (A graph has at most one; with two, the first's
    /// successors could squeeze a challenge before the second's inputs were
    /// queued.) Transcript nodes (messages and
    /// challenges) then share the sponge through a mutex; the graph chains
    /// them in transcript order, so only one is ever ready, and a message is
    /// computed outside the lock.
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
    /// [`MutexGraph::handle_node`]) or, in a run without errors, never runs;
    /// if the graph has more than one input marker; if a transcript value cannot be
    /// serialized for the sponge, or if the error/check mutexes are
    /// poisoned.
    pub fn run_graph<H: DuplexSpongeInterface<U = u8> + Send>(
        g: Arc<MutexGraph<C>>,
        inputs: &Inputs<C>,
        prover_state: &mut ProverState<H>,
        result_kind: ResultKind,
    ) -> Result<RunResult<C>, RuntimeError> {
        // Set remaining_deps counters, collect result indices, and identify
        // the initially ready nodes, in one pass.
        //
        // `result_indices` holds the primary output nodes:
        //   - Prover: transcript nodes (proof values in transcript order)
        //   - Verifier: `Op::Verify` op nodes (pass/fail booleans)
        let mut result_indices: Vec<NodeIndex> = Vec::new();
        // Roots are decided from the graph here, never from `remaining_deps`
        // once jobs run: by then a job may have brought a non-root counter to
        // zero, and spawning it again would run it twice.
        let mut initial_roots: Vec<NodeIndex> = Vec::new();
        let mut input_markers: Vec<NodeIndex> = Vec::new();
        for node_idx in g.mutex_graph.node_indices() {
            match &g.mutex_graph[node_idx] {
                Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                    let unique_preds: HashSet<NodeIndex> = g
                        .mutex_graph
                        .neighbors_directed(node_idx, Direction::Incoming)
                        .collect();
                    let n_preds = unique_preds.len();
                    annotation.remaining_deps.store(n_preds, Ordering::SeqCst);
                    if n_preds == 0 {
                        initial_roots.push(node_idx);
                    }

                    // Collect the verifier's checks (the prover graph has
                    // none).
                    if let Node::Op(op, _) = &g.mutex_graph[node_idx]
                        && matches!(**op, Op::Verify(_))
                        && matches!(result_kind, ResultKind::Verifier)
                    {
                        result_indices.push(node_idx);
                    }
                }
                Node::Inp(_) => input_markers.push(node_idx),
                Node::Rel(_) => {}
                Node::Arg(_, _, _, _, _) => {}
            }
        }

        // For prover, the primary result is transcript values.
        if matches!(result_kind, ResultKind::Prover) {
            result_indices = g.mutex_graph.transcript_nodes();
        }

        debug!(
            "[run_graph] total nodes={}, result_indices count={}",
            g.mutex_graph.node_indices().count(),
            result_indices.len()
        );

        let run = Run {
            graph: &g,
            inputs,
            errors: Mutex::new(None),
            transcript: Mutex::new(Transcript {
                sponge: prover_state,
                pending: Vec::new(),
                messages: matches!(result_kind, ResultKind::Prover).then(HashMap::new),
            }),
        };
        // See "Sponge synchronization" above.
        assert!(
            input_markers.len() <= 1,
            "a graph has at most one input marker, found {}",
            input_markers.len()
        );
        let run_ref = &run;
        rayon::scope(|scope| {
            for &marker in &input_markers {
                run_ref.absorb_inputs(scope, marker)?;
            }
            for &root in &initial_roots {
                scope.spawn(move |scope| run_ref.run_node(scope, root));
            }
            Ok(())
        })?;
        let Run {
            errors, transcript, ..
        } = run;

        // A task may have recorded an error; surface it before collecting.
        if let Some(err) = errors.into_inner().unwrap() {
            return Err(err);
        }
        // Without an error every node ran. Checked in release builds too: a
        // verifier check that silently never ran must not read as a pass.
        assert!(
            g.mutex_graph
                .node_indices()
                .filter_map(|n| g.info(n))
                .all(|info| info.executed.load(Ordering::SeqCst)),
            "runtime invariant violation: a node never ran"
        );
        debug_assert!(
            g.mutex_graph
                .node_indices()
                .filter_map(|n| g.info(n))
                .all(|info| info.inbox.is_empty()),
            "a delivered value was never taken"
        );

        // Collect results from the pre-collected indices.
        Ok(match result_kind {
            ResultKind::Prover => {
                let mut messages = transcript
                    .into_inner()
                    .unwrap()
                    .messages
                    .unwrap_or_default();
                // Every reader of a message has run, so each is usually
                // held only here and moves into the proof without a copy. A
                // message that views part of a vector is copied out of it:
                // the proof outlives the run and would keep the whole vector.
                let transcript: Vec<Value<C>> = result_indices
                    .into_iter()
                    .filter_map(|n| messages.remove(&n))
                    .map(|m| Arc::unwrap_or_clone(m).compact())
                    .collect();
                RunResult::Prover(transcript)
            }
            ResultKind::Verifier => {
                let check_results = g.check_results.lock().unwrap();
                RunResult::Verifier {
                    verify_results: result_indices
                        .into_iter()
                        // A check with no result failed (none should be
                        // missing once every node has run).
                        .map(|n| check_results.get(&n).copied().unwrap_or(false))
                        .collect(),
                }
            }
        })
    }
}
