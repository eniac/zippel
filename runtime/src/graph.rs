use backend::{ArkConfig, Value, value_to_bytes};
use graph::{ArgKind, Dag, GOp, Node, Op, UDag};
use lang::id::Vid;
use log::debug;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use rand::rngs::ThreadRng;
use share::Ctx;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::error::RuntimeError;
use crate::inbox::Inbox;
use crate::queue::{SyncMessage, SyncSender, sync_channel};

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

/// A value queued for the Fiat-Shamir sponge (see `run_graph`).
enum PendingAbsorb<C: ArkConfig> {
    /// An instance input, absorbed with [`absorb_instance_input`].
    Instance(Arc<Value<C>>),
    /// A prover message, absorbed as its serialized bytes.
    Message(Arc<Value<C>>),
}

/// Shared first-error slot used to propagate failures out of rayon-spawned
/// workers. The first task to fail records its error here; subsequent
/// workers short-circuit, drop their `SyncSender` clones, and let the sync
/// channel close so the main loop can exit and surface the stored error.
type ErrorSlot = Arc<Mutex<Option<RuntimeError>>>;

/// Record `err` into `slot` if no earlier worker has already done so.
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
    /// Outcome of every terminal `Op::Verify` node in the verifier graph.
    Verifier {
        /// One boolean per `Op::Verify` node, in graph-collection order;
        /// the protocol verifies iff every entry is `true`.
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
/// a mutex-guarded check map) that `rayon` workers and the sponge-owning main
/// thread can drive it concurrently.
pub struct MutexGraph<C: ArkConfig> {
    mutex_graph: Dag<C, Arc<RuntimeInformation<C>>>,
    /// Auxiliary map storing pass/fail results for `Op::Verify` nodes.
    /// Populated by `handle_node` when a Verify node is evaluated;
    /// `run_graph` collects from it for `ResultKind::Verifier`.
    check_results: Mutex<HashMap<NodeIndex, bool>>,
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Returns true if the node requires sponge processing on the main thread.
///
/// Sync nodes are `Inp` and `Transcr` nodes:
/// - `Inp` is source node that sends instance values through the
///   sponge before their successors can run.
/// - `Transcr` nodes (including `Challenge`) require sequential sponge
///   state updates.
///
/// `Op` nodes are compute-only and run on the thread pool.
fn is_sync_node<C: ArkConfig>(g: &MutexGraph<C>, node_idx: NodeIndex) -> bool {
    match &g.mutex_graph[node_idx] {
        Node::Inp(_) | Node::Transcr(_, _) => true,
        Node::Op(op, _) if matches!(**op, Op::Challenge(_, _)) => true,
        _ => false,
    }
}

/// One execution of a graph: what every scheduled task needs. Cheap to
/// clone, since every field is shared.
#[derive(Clone)]
struct Run<C: ArkConfig> {
    graph: Arc<MutexGraph<C>>,
    inputs: Arc<HashMap<Vid, Arc<Value<C>>>>,
    errors: ErrorSlot,
}

impl<C: ArkConfig> Run<C> {
    /// Hands the finished `node`'s `value` (if it has one) to each successor
    /// and schedules the successors that are now ready. An `Arg` successor
    /// is passed through: it finishes at once with its input value.
    fn release_successors(&self, node: NodeIndex, value: Option<&Arc<Value<C>>>, tx: &SyncSender) {
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
                        self.schedule(successor, tx);
                    }
                }
                Node::Arg(vid, _, _, _, _) => match self.inputs.get(vid) {
                    Some(input) => self.release_successors(successor, Some(input), tx),
                    None => record_error(
                        &self.errors,
                        RuntimeError::missing_arg(vid, self.inputs.keys()),
                    ),
                },
                Node::Inp(_) | Node::Rel(_) => {
                    unreachable!("Inp/Rel marker {:?} follows node {:?}", successor, node)
                }
            }
        }
    }

    /// Queues a ready `node`: sync nodes go to the main loop, the rest run
    /// on the pool.
    fn schedule(&self, node: NodeIndex, tx: &SyncSender) {
        if is_sync_node(&self.graph, node) {
            tx.push(node);
        } else {
            self.spawn(node, tx.clone());
        }
    }

    /// Runs the compute `node` on the pool, then releases its successors.
    /// Holding `tx` keeps the sync channel open until the task is done.
    fn spawn(&self, node: NodeIndex, tx: SyncSender) {
        let run = self.clone();
        rayon::spawn(move || {
            // Once a task has failed the run is abandoned; dropping `tx`
            // lets the sync channel close so the main loop can exit.
            if run.errors.lock().unwrap().is_some() {
                return;
            }
            let value = run.graph.handle_node(node);
            run.release_successors(node, Some(&value), &tx);
        });
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
                for source in info.inbox.sources() {
                    assert!(
                        g.mutex_graph
                            .neighbors_directed(node, Direction::Incoming)
                            .any(|p| p == source.0),
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
    /// Evaluation goes through the canonical [`graph::eval::eval_op`], so the
    /// runtime's per-node semantics stay in lockstep with the test executors
    /// and the unit-level `eval_op` callers.
    ///
    /// # Panics
    ///
    /// Panics if `node` is not an `Op`/`Transcr` node, if it has already
    /// run or an operand was not delivered (scheduling bugs), if the
    /// check-results mutex is poisoned, or if `eval_op` fails: every shape
    /// and type precondition is established by the `lang` type checker and
    /// the scheduler, so a failure is a compiler invariant violation.
    pub fn handle_node(&self, node: NodeIndex) -> Arc<Value<C>> {
        let (Node::Op(op, info) | Node::Transcr(op, info)) = &self.mutex_graph[node] else {
            unreachable!("marker node {node:?} has nothing to compute")
        };
        assert!(
            !info.executed.swap(true, Ordering::SeqCst),
            "runtime invariant violation: node {node:?} executed twice"
        );
        let env = info.inbox.take_all();
        let mut check_sink = Vec::new();
        let value = graph::eval::eval_op(op, &env, &mut ThreadRng::default(), &mut check_sink)
            .expect("runtime invariant violation: eval_op failed on a scheduled node");
        // Each node has at most one top-level Check, so the sink has 0 or 1
        // elements.
        if !check_sink.is_empty() {
            let mut results = self.check_results.lock().unwrap();
            for passed in check_sink {
                results.insert(node, passed);
            }
        }
        value
    }

    /// Execute all nodes in the DAG using counter-based readiness tracking
    /// and parallel computation via Rayon.
    ///
    /// # Readiness tracking
    ///
    /// Each Op/Transcr node carries an atomic `remaining_deps` counter
    /// initialized to its number of unique predecessors. When a node
    /// finishes execution, it delivers its value into the inbox of each
    /// unique successor that reads it and decrements that successor's
    /// counter. When a successor's counter reaches zero, it is spawned onto
    /// Rayon (for compute nodes) or pushed to the sync channel (for
    /// sponge-requiring nodes). A value is freed once every node reading it
    /// has run.
    ///
    /// # Sponge synchronization
    ///
    /// Sync nodes (Inp and Transcr) are processed on the main
    /// thread because they require sequential sponge state updates.
    /// Inp node sends instance values through the sponge;
    /// Transcr nodes (including Challenge) update or squeeze sponge state.
    ///
    /// # Parallel execution
    ///
    /// Non-sync compute nodes are spawned onto Rayon worker threads
    /// (`rayon::spawn`), allowing them to run concurrently as soon as their
    /// dependencies are fully satisfied.
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
    /// Panics if a node is executed twice or runs without an operand (see
    /// [`MutexGraph::handle_node`]), if a transcript value cannot be
    /// serialized for the sponge, if a non-sync node reaches the sync
    /// channel, or if the error/check mutexes are poisoned.
    pub fn run_graph<H: DuplexSpongeInterface<U = u8>>(
        g: Arc<MutexGraph<C>>,
        inputs: Arc<Ctx<Vid, Value<C>>>,
        prover_state: &mut ProverState<H>,
        result_kind: ResultKind,
    ) -> Result<RunResult<C>, RuntimeError> {
        // Build an Arc-wrapped inputs map once. Each `Arg` node then delivers
        // a clone of the Arc (cheap) instead of the inner `Value` (which may
        // be a 500 MB matrix vector). This is a one-time clone per input.
        let inputs: Arc<HashMap<Vid, Arc<Value<C>>>> = Arc::new(
            inputs
                .iter()
                .map(|(k, v)| (k.clone(), Arc::new(v.clone())))
                .collect(),
        );
        // Rayon workers and the main loop record failures in `run.errors`;
        // the main loop bails after the sync channel closes.
        let run = Run {
            graph: Arc::clone(&g),
            inputs: Arc::clone(&inputs),
            errors: Arc::new(Mutex::new(None)),
        };
        // Phase 1: Initialization.
        //
        // Set remaining_deps counters, collect result indices, and
        // identify initially-ready nodes — all in one pass.
        //
        // `result_indices` holds the primary output nodes:
        //   - Prover: transcript nodes (proof values in transcript order)
        //   - Verifier: terminal Verify nodes (verify pass/fail booleans)
        let mut result_indices: Vec<NodeIndex> = Vec::new();
        // Capacity of 1 is enough: sync nodes are connected in the DAG,
        // meaning that at any time, only one sync node can be processed.
        let (tx, rx) = sync_channel(1);

        // Root Op/Transcr nodes — those whose `unique_preds.is_empty()` at
        // initialization. We pin these down in Loop 1 from graph topology so
        // Loop 2 can spawn exactly the true roots. We must NOT decide root-ness
        // by reading `remaining_deps` later: by the time Loop 2 runs, a worker
        // spawned earlier may have already decremented some non-root counter to
        // 0, and a counter-driven spawn there would double-execute that node.
        let mut initial_roots: Vec<NodeIndex> = Vec::new();
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

                    // Collect terminal Verify nodes for the verifier (the
                    // prover graph has none).
                    if let Node::Op(op, _) = &g.mutex_graph[node_idx]
                        && matches!(**op, Op::Verify(_))
                        && matches!(result_kind, ResultKind::Verifier)
                    {
                        result_indices.push(node_idx);
                    }
                }
                Node::Inp(_) => {}
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
        // for ni in g.mutex_graph.node_indices() {
        //     match &g.mutex_graph[ni] {
        //         Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
        //             let rd = annotation.remaining_deps.load(Ordering::SeqCst);
        //             let is_sync = is_sync_node(&g, ni);
        //             debug!("[run_graph] init: node {:?} remaining_deps={} is_sync={}", ni, rd, is_sync);
        //         }
        //         Node::Inp(_, _) => debug!("[run_graph] init: node {:?} is Inp", ni),
        //         Node::Rel(_, _) => debug!("[run_graph] init: node {:?} is Rel", ni),
        //     }
        // }

        // Push the Inp markers first (any iteration order is fine; Args don't
        // appear here as roots — `release_successors` passes through them
        // when their Inp parent is processed).
        for ni in g.mutex_graph.node_indices() {
            if matches!(&g.mutex_graph[ni], Node::Inp(_)) {
                debug!("[run_graph] pushing initial sync node {:?}", ni);
                tx.push(ni);
            }
        }
        // Spawn/push only the topological roots gathered in Loop 1. Reading
        // `remaining_deps` here would race with workers spawned earlier in
        // this same loop: a non-root node whose counter just hit 0 via
        // `release_successors` would be visible as `rd == 0` and would be
        // spawned a SECOND time, causing the runtime invariant violation.
        for ni in initial_roots {
            debug!("[run_graph] init: scheduling root node {:?}", ni);
            run.schedule(ni, &tx);
        }

        drop(tx);

        // Phase 2: Main execution loop.
        //
        // Compute values for sync nodes (transcript and challenge).
        // Spawn non-sync computes onto shared worker threads, and wait for completion.
        let mut loop_count = 0u32;
        // Sponge inputs are queued and absorbed, in order, only when a
        // challenge is squeezed: the sponge's only output is challenges, so
        // values after the last challenge (every value, in a protocol with
        // no challenges) never need serializing.
        let mut pending: Vec<PendingAbsorb<C>> = Vec::new();
        // Prover messages by node, for the proof (prover only).
        let mut messages: HashMap<NodeIndex, Arc<Value<C>>> = HashMap::new();
        while let Some(SyncMessage { node_idx, tx }) = rx.pop() {
            loop_count += 1;

            debug!(
                "[run_graph] loop iteration {}, processing sync node {:?}",
                loop_count, node_idx
            );

            let value = match &g.mutex_graph[node_idx] {
                Node::Inp(_) => {
                    // Walk Arg children to send instance values through the sponge.
                    let mut arg_children: Vec<NodeIndex> = g
                        .mutex_graph
                        .nodes_from(node_idx)
                        .filter(|n| g.mutex_graph[*n].is_arg())
                        .collect();
                    arg_children.sort();
                    debug!(
                        "[run_graph] node {:?} is Inp with {} arg children",
                        node_idx,
                        arg_children.len()
                    );
                    for arg_idx in arg_children {
                        if let Node::Arg(name, _, qual, _, kind) = &g.mutex_graph[arg_idx]
                            && qual.is_instance()
                            && !matches!(kind, ArgKind::TranscriptInput)
                        {
                            let vid = name.clone();
                            let value = match inputs.get(&vid) {
                                Some(v) => v,
                                None => {
                                    let err = RuntimeError::missing_arg(&vid, inputs.keys());
                                    record_error(&run.errors, err.clone());
                                    // Drop tx and bail; in-flight workers
                                    // will see the slot set and short-circuit.
                                    return Err(err);
                                }
                            };
                            pending.push(PendingAbsorb::Instance(Arc::clone(value)));
                        }
                    }
                    None
                }
                Node::Transcr(op, _) => {
                    if matches!(**op, Op::Challenge(_, _)) {
                        debug!("[run_graph] node {:?} is Challenge", node_idx);
                        // Challenge node: absorb what is queued, then squeeze.
                        for p in pending.drain(..) {
                            match p {
                                PendingAbsorb::Instance(v) => {
                                    absorb_instance_input::<C, H>(prover_state, &v);
                                }
                                PendingAbsorb::Message(v) => {
                                    let serialized = value_to_bytes(&*v).unwrap();
                                    prover_state.public_message(serialized.as_slice());
                                }
                            }
                        }
                        Some(Arc::new(Value::<C>::challenge(prover_state)))
                    } else {
                        debug!("[run_graph] node {:?} is Transcript", node_idx);
                        // Proof transcript node: compute value and send
                        // through the sponge.
                        let value = g.handle_node(node_idx);
                        pending.push(PendingAbsorb::Message(Arc::clone(&value)));
                        if matches!(result_kind, ResultKind::Prover) {
                            messages.insert(node_idx, Arc::clone(&value));
                        }
                        Some(value)
                    }
                }
                Node::Op(_, _) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => {
                    // Non-sync Op and Rel/Arg nodes should never appear on the sync
                    // channel. Panic indicates a logic error in scheduling.
                    unreachable!("non-sync node {:?} on sync channel", node_idx)
                }
            };

            // Deliver the value — pushes ready sync nodes to the sync queue
            // and spawns non-sync nodes onto shared worker threads.
            debug!("[run_graph] releasing successors of node {:?}", node_idx);
            run.release_successors(node_idx, value.as_ref(), &tx);
        }
        drop(pending);

        debug!(
            "[run_graph] main loop completed after {} iterations",
            loop_count
        );

        // A worker may have recorded an error; surface it before collecting.
        if let Some(err) = run.errors.lock().unwrap().take() {
            return Err(err);
        }
        debug_assert!(
            g.mutex_graph
                .node_indices()
                .filter_map(|n| g.info(n))
                .all(|info| info.inbox.is_empty()),
            "a delivered value was never taken"
        );

        // Phase 3: Collect results from pre-collected indices.
        Ok(match result_kind {
            ResultKind::Prover => {
                // Every reader of a message has run, so each is usually
                // held only here and moves into the proof without a copy.
                let transcript: Vec<Value<C>> = result_indices
                    .into_iter()
                    .filter_map(|n| messages.remove(&n))
                    .map(Arc::unwrap_or_clone)
                    .collect();
                RunResult::Prover(transcript)
            }
            ResultKind::Verifier => {
                let check_results = g.check_results.lock().unwrap();
                RunResult::Verifier {
                    verify_results: result_indices
                        .into_iter()
                        .filter_map(|n| check_results.get(&n).copied())
                        .collect(),
                }
            }
        })
    }
}
