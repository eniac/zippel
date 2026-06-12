use backend::{ArkConfig, Value, value_to_bytes};
use graph::scheduler::TDag;
use graph::{Dag, GOp, Node, Op};
use lang::id::Vid;
use log::debug;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use rand::rngs::ThreadRng;
use share::Ctx;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use crate::error::RuntimeError;
use crate::queue::{SyncMessage, SyncSender, sync_channel};

/// Size threshold (in bytes of serialized form) above which a public
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

/// Absorb a public input value into the Fiat-Shamir sponge.
///
/// For values below `FS_DIGEST_THRESHOLD_BYTES`, serialize as before
/// (preserves transcript bytes for existing small-input protocols). For
/// large values, stream the serialized bytes through a Blake3 hasher and
/// absorb the 32-byte digest — symmetric on prover and verifier sides.
fn absorb_public_input<C: ArkConfig, H>(prover_state: &mut ProverState<H>, value: &Value<C>)
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

/// Runtime information attached to each Op/Transcr node in the DAG.
///
/// `remaining_deps` uses atomic operations for lock-free counter-based
/// readiness tracking: when a node's dependencies finish, they decrement
/// its counter; when the counter reaches zero, the node is ready to execute.
pub struct RuntimeInformation<C: ArkConfig> {
    /// Computed value of this node, set after execution.
    ///
    /// Wrapped in `Arc` so that successors can cheaply share access without
    /// cloning the inner `Value` (which may be a 500 MB matrix vector).
    ///
    /// Stored in a `OnceLock` rather than `Mutex<Option<…>>` because every
    /// node is written exactly once (when its handler completes) and read
    /// many times (by each successor's `get_value`). `OnceLock::get` is a
    /// lock-free atomic load — much cheaper than `Mutex::lock` on the hot
    /// path. Both have identical happy-path semantics for our use.
    return_value: OnceLock<Arc<Value<C>>>,
    /// Number of unfinished dependencies. Atomically decremented;
    /// when it reaches zero, this node is ready to execute.
    pub remaining_deps: AtomicUsize,
}

impl<C: ArkConfig> Default for RuntimeInformation<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig> RuntimeInformation<C> {
    pub fn new() -> Self {
        RuntimeInformation {
            return_value: OnceLock::new(),
            remaining_deps: AtomicUsize::new(0),
        }
    }
}

pub struct MutexGraph<C: ArkConfig> {
    mutex_graph: Dag<C, Arc<RuntimeInformation<C>>>,
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Returns true if the node requires sponge processing on the main thread.
///
/// Sync nodes are `Inp` and `Transcr` nodes:
/// - `Inp` is source node that sends public values through the
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

/// Update successors of a finished node. For each unique successor,
/// atomically decrement its `remaining_deps`. If a successor reaches
/// zero, submit it to the pool manager (non-sync) or return (sync).
fn update_successors<C: ArkConfig>(
    g: &Arc<MutexGraph<C>>,
    inputs: &Arc<HashMap<Vid, Arc<Value<C>>>>,
    tx: SyncSender,
    node_idx: NodeIndex,
    error_slot: &ErrorSlot,
) {
    // Deduplicate successors: remaining_deps is initialized from unique
    // predecessors, so we must only decrement once per (predecessor, successor)
    // pair regardless of how many parallel edges exist between them.
    let successors: HashSet<NodeIndex> = g
        .mutex_graph
        .neighbors_directed(node_idx, Direction::Outgoing)
        .collect();

    for dependent in successors {
        match &g.mutex_graph[dependent] {
            Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                let prev = annotation.remaining_deps.fetch_sub(1, Ordering::SeqCst);
                debug!(
                    "[update_successors] node {:?} -> dependent {:?}, prev={}, is_sync={}",
                    node_idx,
                    dependent,
                    prev,
                    is_sync_node(g, dependent)
                );
                if prev == 1 {
                    if is_sync_node(g, dependent) {
                        debug!(
                            "[update_successors] node {:?} -> sync {:?} ready, pushing",
                            node_idx, dependent
                        );
                        tx.push(dependent);
                        continue;
                    }

                    let g_clone = Arc::clone(g);
                    let inputs_clone = Arc::clone(inputs);
                    let dep_idx = dependent;
                    let tx = tx.clone();
                    let error_slot = Arc::clone(error_slot);
                    debug!(
                        "[update_successors] node {:?} -> non-sync {:?} ready, spawning",
                        node_idx, dependent
                    );
                    rayon::spawn(move || {
                        // Bail out early if another worker has already
                        // recorded a failure; dropping `tx` here lets the
                        // sync channel close so the main loop can exit.
                        if error_slot.lock().unwrap().is_some() {
                            return;
                        }
                        match g_clone.handle_node(dep_idx, &inputs_clone) {
                            Ok(()) => {
                                update_successors(&g_clone, &inputs_clone, tx, dep_idx, &error_slot)
                            }
                            Err(e) => record_error(&error_slot, e),
                        }
                    });
                }
            }
            // Inp/Rel markers and Arg nodes have no compute and no
            // remaining_deps counter. They appear as successors of one
            // another (Inp → Arg) and as successors of compute paths is
            // never expected. Pass through Args by recursively notifying
            // *their* successors so downstream Ops can decrement properly.
            Node::Inp(_) | Node::Rel(_) => {
                unreachable!("Inp/Rel marker {:?} on sync channel", node_idx)
            }
            Node::Arg(_, _, _, _, _) => {
                update_successors(g, inputs, tx.clone(), dependent, error_slot);
            }
        }
    }
}

/// Global counter of detected double-execute attempts. Incremented by
/// `log_double_execute` whenever `handle_node` is reached for an Op/Transcr
/// whose `return_value` is already populated (or whose `set` lost the race).
/// `run_graph` snapshots and prints this after the main loop so the user
/// can see whether the run was clean.
pub static DOUBLE_EXECUTE_COUNT: AtomicUsize = AtomicUsize::new(0);

fn log_double_execute(kind: &str, node: NodeIndex, op_disc: usize) {
    DOUBLE_EXECUTE_COUNT.fetch_add(1, Ordering::SeqCst);
    let bt = std::backtrace::Backtrace::capture();
    eprintln!(
        "[RUNTIME-RACE] {} node {:?} double-execute attempt; op discriminant = {}\n{}",
        kind, node, op_disc, bt,
    );
}

// ---------------------------------------------------------------------------
// MutexGraph implementation
// ---------------------------------------------------------------------------

impl<C: ArkConfig> MutexGraph<C> {
    pub fn new(tdag: TDag<C>) -> Self {
        MutexGraph {
            mutex_graph: tdag.map_annotations(&|_, _| Arc::new(RuntimeInformation::<C>::new())),
        }
    }

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

    pub fn get_value(
        &self,
        r: graph::Ref,
        inputs: &HashMap<Vid, Arc<Value<C>>>,
    ) -> Result<Arc<Value<C>>, RuntimeError> {
        let node = r.node();

        match &self.mutex_graph[node] {
            Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                match annotation.return_value.get() {
                    Some(val) => Ok(Arc::clone(val)),
                    None => panic!("Value should exist for node {:?}", node),
                }
            }
            Node::Inp(_) | Node::Rel(_) => {
                // Should not be referenced directly in Phase B; values
                // come from Arg nodes.
                panic!("get_value on Inp/Rel marker node {:?}", node)
            }
            Node::Arg(vid, _, _, _, _) => match inputs.get(vid) {
                Some(v) => Ok(Arc::clone(v)),
                None => Err(RuntimeError::missing_arg(vid, inputs.keys())),
            },
        }
    }

    /// Compute a node's value by snapshotting the values of every `Op::Ref`
    /// reachable from `operation` (via [`MutexGraph::get_value`]) and routing
    /// the actual dispatch through the canonical [`graph::eval::eval_op`].
    ///
    /// This keeps the runtime's per-node semantics in lockstep with the test
    /// executors and the unit-level `eval_op` callers — there is no separate
    /// runtime-only dispatch table.
    pub fn handle_op(
        &self,
        operation: &GOp<C>,
        inputs: &HashMap<Vid, Arc<Value<C>>>,
    ) -> Result<Arc<Value<C>>, RuntimeError> {
        let refs = graph::eval::collect_refs(operation);
        // Pre-size the env so insertions don't trigger rehash/resize. Most
        // Op trees have ≤ 4 distinct refs; sizing to `refs.len()` slightly
        // over-allocates for duplicates but avoids the 0→1→2→4→… resize
        // sequence HashMap pays when starting empty.
        let mut env: HashMap<graph::Ref, Arc<Value<C>>> = HashMap::with_capacity(refs.len());
        for r in refs {
            if let std::collections::hash_map::Entry::Vacant(e) = env.entry(r) {
                e.insert(self.get_value(r, inputs)?);
            }
        }
        let mut rng = ThreadRng::default();
        Ok(graph::eval::eval_op(operation, &env, &mut rng)
            .expect("runtime invariant violation: eval_op failed on a scheduled node"))
    }

    pub fn handle_node(
        &self,
        node_curr: NodeIndex,
        inputs: &HashMap<Vid, Arc<Value<C>>>,
    ) -> Result<(), RuntimeError> {
        let node = &self.mutex_graph[node_curr];

        match node {
            Node::Op(operation, annotation) => {
                if annotation.return_value.get().is_some() {
                    log_double_execute("Op", node_curr, operation.discriminant_order());
                    return Ok(());
                }
                let return_val = self.handle_op(&**operation, inputs)?;
                if annotation.return_value.set(return_val).is_err() {
                    log_double_execute("Op (set-race)", node_curr, operation.discriminant_order());
                }
            }
            Node::Transcr(operation, annotation) => {
                if annotation.return_value.get().is_some() {
                    log_double_execute("Transcr", node_curr, operation.discriminant_order());
                    return Ok(());
                }
                let return_val = self.handle_op(&**operation, inputs)?;
                if annotation.return_value.set(return_val).is_err() {
                    log_double_execute(
                        "Transcr (set-race)",
                        node_curr,
                        operation.discriminant_order(),
                    );
                }
            }
            Node::Inp(_) => {}
            Node::Rel(_) => {}
            Node::Arg(_, _, _, _, _) => {}
        }
        Ok(())
    }

    /// Execute all nodes in the DAG using counter-based readiness tracking
    /// and parallel computation via Rayon.
    ///
    /// # Readiness tracking
    ///
    /// Each Op/Transcr node carries an atomic `remaining_deps` counter
    /// initialized to its number of unique predecessors. When a node
    /// finishes execution, it atomically decrements the counters of all
    /// its unique successors. When a successor's counter reaches zero,
    /// it is spawned onto Rayon (for compute nodes) or pushes to the sync
    /// channel (for sponge-requiring nodes).
    ///
    /// # Sponge synchronization
    ///
    /// Sync nodes (Inp and Transcr) are processed on the main
    /// thread because they require sequential sponge state updates.
    /// Inp node sends public values through the sponge;
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
    /// - For `ResultKind::Prover`: proof transcript values in transcript order.
    /// - For `ResultKind::Verifier`: terminal Check node values.
    pub fn run_graph<H: DuplexSpongeInterface<U = u8>>(
        g: Arc<MutexGraph<C>>,
        inputs: Arc<Ctx<Vid, Value<C>>>,
        prover_state: &mut ProverState<H>,
        result_kind: ResultKind,
    ) -> Result<Vec<Value<C>>, RuntimeError> {
        let race_count_at_start = DOUBLE_EXECUTE_COUNT.load(Ordering::SeqCst);
        // Build an Arc-wrapped inputs map once. Subsequent per-handle_op
        // accesses clone the Arc (cheap) instead of the inner `Value`
        // (which may be a 500 MB matrix vector). This is a one-time clone
        // per input — the price we pay to avoid per-op clones forever after.
        let inputs: Arc<HashMap<Vid, Arc<Value<C>>>> = Arc::new(
            inputs
                .iter()
                .map(|(k, v)| (k.clone(), Arc::new(v.clone())))
                .collect(),
        );
        // Shared first-error slot. Rayon workers and the main loop record
        // failures here; the main loop bails after the sync channel closes.
        let error_slot: ErrorSlot = Arc::new(Mutex::new(None));
        // Phase 1: Initialization.
        //
        // Set remaining_deps counters, collect result indices, and
        // identify initially-ready nodes — all in one pass.
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

                    // Verifier results are terminal Check nodes. Prover results
                    // are collected below via Dag::transcript_nodes(), which is
                    // already transcript-edge-topologically ordered.
                    match (&g.mutex_graph[node_idx], result_kind) {
                        (Node::Op(op, _), ResultKind::Verifier) if matches!(**op, Op::Check(_)) => {
                            result_indices.push(node_idx);
                        }
                        _ => {}
                    }
                }
                Node::Inp(_) => {}
                Node::Rel(_) => {}
                Node::Arg(_, _, _, _, _) => {}
            }
        }
        let result_indices = match result_kind {
            ResultKind::Prover => g.mutex_graph.transcript_nodes(),
            ResultKind::Verifier => result_indices,
        };

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
        // appear here as roots — they're notified via the Arg-passthrough in
        // update_successors when their Inp parent is processed).
        for ni in g.mutex_graph.node_indices() {
            if matches!(&g.mutex_graph[ni], Node::Inp(_)) {
                debug!("[run_graph] pushing initial sync node {:?}", ni);
                tx.push(ni);
            }
        }
        // Spawn/push only the topological roots gathered in Loop 1. Reading
        // `remaining_deps` here would race with workers spawned earlier in
        // this same loop: a non-root node whose counter just hit 0 via
        // `update_successors` would be visible as `rd == 0` and would be
        // spawned a SECOND time, causing the runtime invariant violation.
        for ni in initial_roots {
            if is_sync_node(&g, ni) {
                debug!("[run_graph] init: pushing sync root node {:?}", ni);
                tx.push(ni);
            } else {
                let g_clone = Arc::clone(&g);
                let inputs_clone = Arc::clone(&inputs);
                let tx = tx.clone();
                let error_slot = Arc::clone(&error_slot);
                debug!("[run_graph] init: spawning non-sync root node {:?}", ni);
                rayon::spawn(move || {
                    if error_slot.lock().unwrap().is_some() {
                        return;
                    }
                    match g_clone.handle_node(ni, &inputs_clone) {
                        Ok(()) => update_successors(&g_clone, &inputs_clone, tx, ni, &error_slot),
                        Err(e) => record_error(&error_slot, e),
                    }
                });
            }
        }

        drop(tx);

        // Phase 2: Main execution loop.
        //
        // Compute values for sync nodes (transcript and challenge).
        // Spawn non-sync computes onto shared worker threads, and wait for completion.
        let mut loop_count = 0u32;
        while let Some(SyncMessage { node_idx, tx }) = rx.pop() {
            loop_count += 1;

            debug!(
                "[run_graph] loop iteration {}, processing sync node {:?}",
                loop_count, node_idx
            );

            match &g.mutex_graph[node_idx] {
                Node::Inp(_) => {
                    // Walk Arg children to send public values through the sponge.
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
                        if let Some(pref) = g.mutex_graph[arg_idx].arg_pref(arg_idx)
                            && pref.qualifier.is_public()
                            && !pref.from_transcript
                        {
                            let vid = pref.name().expect("Arg node must carry a name").clone();
                            let value = match inputs.get(&vid) {
                                Some(v) => v,
                                None => {
                                    let err = RuntimeError::missing_arg(&vid, inputs.keys());
                                    record_error(&error_slot, err.clone());
                                    // Drop tx and bail; in-flight workers
                                    // will see the slot set and short-circuit.
                                    return Err(err);
                                }
                            };
                            absorb_public_input::<C, H>(prover_state, &**value);
                        }
                    }
                }
                Node::Transcr(op, annotation) => {
                    if matches!(**op, Op::Challenge(_, _)) {
                        debug!("[run_graph] node {:?} is Challenge", node_idx);
                        // Challenge node: squeeze the sponge.
                        let return_val = Value::<C>::challenge(prover_state);
                        annotation
                            .return_value
                            .set(Arc::new(return_val))
                            .map_err(|_| ())
                            .expect("runtime invariant violation: Challenge node executed twice");
                    } else {
                        debug!("[run_graph] node {:?} is Transcript", node_idx);
                        // Proof transcript node: compute value and send
                        // through the sponge.
                        if let Err(e) = g.handle_node(node_idx, &inputs) {
                            record_error(&error_slot, e.clone());
                            return Err(e);
                        }
                        let arc_val = annotation
                            .return_value
                            .get()
                            .expect("Transcr node return_value should be set after handle_node");
                        let serialized = value_to_bytes(&**arc_val).unwrap();
                        prover_state.public_message(serialized.as_slice());
                    }
                }
                Node::Op(_, _) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => {
                    // Non-sync Op and Rel/Arg nodes should never appear on the sync
                    // channel. Panic indicates a logic error in scheduling.
                    unreachable!("non-sync node {:?} on sync channel", node_idx)
                }
            };

            // Update successors — pushes ready sync nodes to the sync queue
            // and spawns non-sync nodes onto shared worker threads.
            debug!(
                "[run_graph] calling update_successors for node {:?}",
                node_idx
            );
            update_successors(&g, &inputs, tx, node_idx, &error_slot);
        }

        debug!(
            "[run_graph] main loop completed after {} iterations",
            loop_count
        );

        let race_count = DOUBLE_EXECUTE_COUNT.load(Ordering::SeqCst) - race_count_at_start;
        if race_count > 0 {
            eprintln!(
                "[RUNTIME-RACE] run_graph completed with {} double-execute attempt(s) (see [RUNTIME-RACE] lines above)",
                race_count,
            );
        }

        // A worker may have recorded an error; surface it before collecting.
        if let Some(err) = error_slot.lock().unwrap().take() {
            return Err(err);
        }

        // Phase 3: Collect results from pre-collected result indices.
        Ok(match result_kind {
            ResultKind::Prover => result_indices
                .into_iter()
                .filter_map(|n| match &g.mutex_graph[n] {
                    Node::Transcr(op, annotation) if !matches!(**op, Op::Challenge(_, _)) => {
                        annotation.return_value.get().map(|arc| (**arc).clone())
                    }
                    _ => None,
                })
                .collect(),
            ResultKind::Verifier => result_indices
                .into_iter()
                .filter_map(|n| match &g.mutex_graph[n] {
                    Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                        annotation.return_value.get().map(|arc| (**arc).clone())
                    }
                    _ => None,
                })
                .collect(),
        })
    }
}
