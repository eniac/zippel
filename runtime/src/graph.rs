use log::debug;
use petgraph::graph::NodeIndex;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::sync::{Arc, Mutex};
use backend::{ArkConfig, Value, value_to_bytes};
use backend::values::marginalize as backend_marginalize;
use graph::{Dag, Node, Op, GOp};
use graph::scheduler::{ThreadAlloc, TDag};
use rand::rngs::ThreadRng;
use lang::ast::BinOp;
use lang::id::Vid;
use petgraph::Direction;
use share::Ctx;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::pool::PoolManager;
use crate::queue::{SyncMessage, SyncSender, sync_channel};

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
    return_value: Mutex<Option<Value<C>>>,
    /// Number of unfinished dependencies. Atomically decremented;
    /// when it reaches zero, this node is ready to execute.
    pub remaining_deps: AtomicUsize,
    /// Thread allocation hint from the scheduler.
    pub thread_num: usize,
}

impl<C: ArkConfig> RuntimeInformation<C> {
    pub fn new(thread_num: usize) -> Self {
        RuntimeInformation {
            return_value: Mutex::new(None),
            remaining_deps: AtomicUsize::new(0),
            thread_num,
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
        Node::Inp(_, _) | Node::Transcr(_, _) => true,
        Node::Op(op, _) if matches!(**op, Op::Challenge(_, _)) => true,
        _ => false,
    }
}

/// Update successors of a finished node. For each unique successor,
/// atomically decrement its `remaining_deps`. If a successor reaches
/// zero, submit it to the pool manager (non-sync) or return (sync).
fn update_successors<C: ArkConfig>(
    g: &Arc<MutexGraph<C>>,
    inputs: &Arc<Ctx<Vid, Value<C>>>,
    pool_manager: &Arc<PoolManager>,
    tx: SyncSender,
    node_idx: NodeIndex,
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
                    node_idx, dependent, prev, is_sync_node(g, dependent)
                );
                if prev == 1 {
                    if is_sync_node(g, dependent) {
                        debug!("[update_successors] node {:?} -> sync {:?} ready, pushing", node_idx, dependent);
                        tx.push(dependent);
                        continue;
                    }

                    let thread_num = annotation.thread_num;
                    let g_clone = Arc::clone(g);
                    let inputs_clone = Arc::clone(inputs);
                    let pm_clone = Arc::clone(pool_manager);
                    let dep_idx = dependent;
                    let tx = tx.clone();
                    debug!(
                        "[update_successors] node {:?} -> non-sync {:?} ready (thread_num={})",
                        node_idx, dependent, thread_num
                    );
                    pool_manager.submit(
                        thread_num,
                        Box::new(move || {
                            g_clone.handle_node(dep_idx, inputs_clone.clone());
                            update_successors(&g_clone, &inputs_clone, &pm_clone, tx, dep_idx);
                        }),
                    );
                }
            }
            // Inp and Rel nodes have no remaining_deps counter;
            // they should never appear as successors.
            Node::Inp(_, _) | Node::Rel(_, _) => {
                unreachable!("Inp/Rel node {:?} on sync channel", node_idx)
            }
        }
    }
}

/// Topological sort of transcript node indices.
///
/// Transcript nodes form a chain in the DAG. This function finds the
/// root (no parent in the transcript list) and walks the chain.
fn order_transcript_nodes<C: ArkConfig>(
    transcript_indices: Vec<NodeIndex>,
    graph: &Dag<C, Arc<RuntimeInformation<C>>>,
) -> Vec<NodeIndex> {
    if transcript_indices.is_empty() {
        return Vec::new();
    }

    let transcript_set: HashSet<NodeIndex> = transcript_indices.iter().copied().collect();
    let mut child_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
    let mut has_parent = HashSet::new();

    for &node in &transcript_indices {
        for parent in graph.neighbors_directed(node, Direction::Incoming) {
            if transcript_set.contains(&parent) {
                child_map.insert(parent, node);
                has_parent.insert(node);
            }
        }
    }

    // Find root (no parent in transcript list).
    let root = transcript_indices
        .iter()
        .find(|&&n| !has_parent.contains(&n))
        .expect("Cycle detected in transcript nodes");

    // Walk the chain.
    let mut ordered = vec![*root];
    let mut current = *root;
    while let Some(&child) = child_map.get(&current) {
        ordered.push(child);
        current = child;
    }
    ordered
}

// ---------------------------------------------------------------------------
// MutexGraph implementation
// ---------------------------------------------------------------------------

impl<C: ArkConfig> MutexGraph<C> {
    pub fn new(tdag: TDag<C>) -> Self {
        MutexGraph {
            mutex_graph: tdag.map_annotations(&|_, nthreads: &ThreadAlloc| {
                Arc::new(RuntimeInformation::<C>::new(nthreads.get()))
            }),
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

    pub fn get_value(&self, r: graph::Ref, inputs: Arc<Ctx<Vid, Value<C>>>) -> Value<C> {
        let node = r.node();

        match &self.mutex_graph[node] {
            Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                let return_val = annotation.return_value.lock().unwrap();
                match &*return_val {
                    Some(val) => val.clone(),
                    None => panic!("Value should exist"),
                }
            }
            Node::Inp(_, _) | Node::Rel(_, _) => {
                let vid = r.var().expect("Input should be a variable");
                inputs
                    .get(&vid)
                    .expect(format!("Value for {} should exist", vid).as_str())
                    .clone()
            }
        }
    }

    pub fn handle_op(&self, operation: &GOp<C>, inputs: Arc<Ctx<Vid, Value<C>>>) -> Value<C> {
        match operation {
            Op::Value(val) => {
                return val.clone();
            }
            Op::Ref(r, _atyp) => {
                return self.get_value(r.clone(), inputs);
            }
            Op::Vec(vec) => {
                let value_vector: Vec<Value<C>> = vec
                    .iter()
                    .map(|op| self.handle_op(&*op, Arc::clone(&inputs)))
                    .collect::<Vec<Value<C>>>();
                return Value::value_vec(value_vector);
            }
            Op::Record(fields) => {
                let mut record_values = share::Ctx::new();
                for (name, op) in fields.iter() {
                    let field_value = self.handle_op(&*op, Arc::clone(&inputs));
                    record_values.insert(name, &field_value);
                }
                return Value::Record(record_values);
            }
            Op::Ram(v, index_val) => {
                let inputs_v_clone = Arc::clone(&inputs);
                let inputs_index_val_clone = Arc::clone(&inputs);
                let v_val: Value<C> = self.handle_op(&*v, inputs_v_clone);
                let index_val_value: Value<C> = self.handle_op(&*index_val, inputs_index_val_clone);
                return v_val.ram(index_val_value);
            }
            Op::Check(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val;
            }
            Op::Bin(op, a, b, _typ) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(&*b, inputs_b_clone);
                match op {
                    BinOp::Add => {
                        return a_val + b_val;
                    }
                    BinOp::Mul => {
                        return a_val * b_val;
                    }
                    BinOp::Equ => {
                        return a_val.value_equ(&b_val);
                    }
                    BinOp::Sub => {
                        return a_val - b_val;
                    }
                    BinOp::Div => {
                        return a_val / b_val;
                    }
                    BinOp::Pow => {
                        return a_val ^ b_val;
                    }
                    BinOp::Dot => {
                        return a_val.dot(b_val);
                    }
                    BinOp::Concat => {
                        return a_val.value_concat(b_val);
                    }
                    BinOp::Rem => {
                        return a_val % b_val;
                    }
                    BinOp::And => {
                        return a_val & b_val;
                    }
                }
            }
            Op::Random(typ, _) => {
                let mut rng = ThreadRng::default();
                return Value::random(&mut rng, typ);
            }
            Op::Challenge(typ, _) => {
                let mut rng = ThreadRng::default();
                // TODO: Implement challenge
                return Value::random(&mut rng, typ);
            }
            Op::Eval(p, x) => {
                let inputs_p_clone = Arc::clone(&inputs);
                let inputs_x_clone = Arc::clone(&inputs);
                let p_val: Value<C> = self.handle_op(&*p, inputs_p_clone);
                let x_val: Value<C> = self.handle_op(&*x, inputs_x_clone);
                return p_val.value_eval(x_val);
            }
            Op::Coef(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_coef();
            }
            Op::Pair(a, b, _) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(&*b, inputs_b_clone);
                return a_val.pair(b_val);
            }
            Op::Poly(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_poly();
            }
            Op::Interpolate(points, evals) => {
                let inputs_points_clone = Arc::clone(&inputs);
                let inputs_evals_clone = Arc::clone(&inputs);
                let points_val: Value<C> = self.handle_op(&*points, inputs_points_clone);
                let evals_val: Value<C> = self.handle_op(&*evals, inputs_evals_clone);
                return evals_val.value_interpolate_with_points(&points_val);
            }
            Op::Fft(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_fft();
            }
            Op::Mle(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_mle();
            }
            Op::Reduce(op, v) => {
                let inputs_v_clone = Arc::clone(&inputs);
                let v_val: Value<C> = self.handle_op(&*v, inputs_v_clone);
                return v_val.value_reduce(*op);
            }
            Op::Marginalize(a) => {
                let (poly_val, challenge_val, round_val, num_variables_val, max_degree_val) = match &**a {
                    Op::Record(fields) => {
                        let poly_op = fields
                            .get(&"poly".to_string())
                            .expect("marginalize: missing field 'poly'");
                        let challenge_op = fields
                            .get(&"challenge".to_string())
                            .expect("marginalize: missing field 'challenge'");
                        let round_op = fields.get(&"round".to_string());
                        let num_variables_op = fields.get(&"num_variables".to_string());
                        let max_degree_op = fields.get(&"max_degree".to_string());

                        let poly_val = self.handle_op(poly_op, Arc::clone(&inputs));
                        let challenge_val = self.handle_op(challenge_op, Arc::clone(&inputs));
                        let round_val = round_op.map(|op| self.handle_op(op, Arc::clone(&inputs)));
                        let num_variables_val =
                            num_variables_op.map(|op| self.handle_op(op, Arc::clone(&inputs)));
                        let max_degree_val = max_degree_op.map(|op| self.handle_op(op, Arc::clone(&inputs)));
                        (poly_val, challenge_val, round_val, num_variables_val, max_degree_val)
                    }
                    _ => {
                        let cfg_val: Value<C> = self.handle_op(a, Arc::clone(&inputs));
                        let Value::Record(record) = cfg_val else { unreachable!() };
                        let poly_val = record
                            .get(&"poly".to_string())
                            .cloned()
                            .unwrap();
                        let challenge_val = record
                            .get(&"challenge".to_string())
                            .cloned()
                            .unwrap();
                        let round_val = record.get(&"round".to_string()).cloned();
                        let num_variables_val = record.get(&"num_variables".to_string()).cloned();
                        let max_degree_val = record.get(&"max_degree".to_string()).cloned();
                        (poly_val, challenge_val, round_val, num_variables_val, max_degree_val)
                    }
                };

                let poly = poly_val.into_poly().clone();
                let challenge = Some(challenge_val.into_scalar());
                let round = round_val.map(|v| v.into_index()).unwrap_or(0usize);

                let num_variables = if let Some(v) = num_variables_val {
                    v.into_index()
                } else {
                    let current_poly_vars = poly.num_vars().unwrap_or(1);
                    if round == 0 {
                        current_poly_vars
                    } else {
                        current_poly_vars + (round - 1)
                    }
                };

                let max_degree = max_degree_val
                    .map(|v| v.into_index())
                    .unwrap_or_else(|| poly.degree());
                let (evals, next_poly) =
                    backend_marginalize::<C>(&poly, num_variables, max_degree, round, challenge);

                let mut out_fields = Ctx::new();
                out_fields.insert(&"evaluations".to_string(), &Value::VecScalar(evals));
                out_fields.insert(&"next_poly".to_string(), &Value::Poly(next_poly));

                return Value::Record(out_fields);
            }

            Op::Proj(record_op, field_name, _) => {
                let inputs_rec = Arc::clone(&inputs);
                let rec_val: Value<C> = self.handle_op(record_op, inputs_rec);
                let Value::Record(r) = rec_val else { unreachable!() };
                r.get(&field_name).cloned().unwrap()
            }
        }
    }

    pub fn handle_node(&self, node_curr: NodeIndex, inputs: Arc<Ctx<Vid, Value<C>>>) {
        let node = &self.mutex_graph[node_curr];

        match node {
            Node::Op(operation, annotation) => {
                let return_val = self.handle_op(&**operation, inputs);
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);
            }
            Node::Transcr(operation, annotation) => {
                let return_val = self.handle_op(&**operation, inputs);
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);
            }
            Node::Inp(_, _) => {}
            Node::Rel(_, _) => {}
        }
    }

    /// Execute all nodes in the DAG using counter-based readiness tracking
    /// and parallel computation via a capacity-managed thread pool.
    ///
    /// # Readiness tracking
    ///
    /// Each Op/Transcr node carries an atomic `remaining_deps` counter
    /// initialized to its number of unique predecessors. When a node
    /// finishes execution, it atomically decrements the counters of all
    /// its unique successors. When a successor's counter reaches zero,
    /// it is submitted to the pool manager (for compute nodes) or notifies
    /// the main thread (for sponge-requiring nodes).
    ///
    /// # Sponge synchronization
    ///
    /// Sync nodes (Inp and Transcr) are processed on the main
    /// thread because they require sequential sponge state updates.
    /// Inp node sends public values through the sponge;
    /// Transcr nodes (including Challenge) update or squeeze sponge state.
    ///
    /// # Thread pool
    ///
    /// A `PoolManager` is created with `max_thread_num` capacity (the
    /// maximum per-node thread allocation from the scheduler). Each task
    /// declares its cost (`thread_num`) and the pool manager ensures the
    /// total cost of concurrently running tasks does not exceed capacity.
    /// Per-cost thread pools are cached for reuse. Completed tasks can
    /// submit new tasks (e.g., when successors become ready), enabling
    /// successor-driven scheduling.
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
    ) -> Vec<Value<C>> {
        // Phase 1: Initialization.
        //
        // Set remaining_deps counters, collect result indices, and
        // identify initially-ready nodes — all in one pass.
        // Reserve one core for the main thread (sync node processing).
        // .max(2) before subtraction prevents underflow and ensures the
        // pool capacity is at least 1.
        let mut max_thread_num: usize = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1).max(2) - 1;
        let mut result_indices: Vec<NodeIndex> = Vec::new();
        // Capacity of 1 is enough: sync nodes are connected in the DAG,
        // meaning that at any time, only one sync node can be processed.
        let (tx, rx) = sync_channel(1);

        for node_idx in g.mutex_graph.node_indices() {
            match &g.mutex_graph[node_idx] {
                Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                    max_thread_num = max_thread_num.max(annotation.thread_num);
                    let unique_preds: HashSet<NodeIndex> = g
                        .mutex_graph
                        .neighbors_directed(node_idx, Direction::Incoming)
                        .collect();
                    annotation
                        .remaining_deps
                        .store(unique_preds.len(), Ordering::SeqCst);

                    // Collect result indices inline.
                    match (&g.mutex_graph[node_idx], result_kind) {
                        (Node::Transcr(_, _), ResultKind::Prover) => {
                            result_indices.push(node_idx);
                        }
                        (Node::Op(op, _), ResultKind::Verifier) if matches!(**op, Op::Check(_)) => {
                            result_indices.push(node_idx);
                        }
                        _ => {}
                    }
                }
                Node::Inp(_, _) => {},
                Node::Rel(_, _) => {}
            }
        }
        let result_indices: Vec<NodeIndex> = match result_kind {
            ResultKind::Prover => {
                order_transcript_nodes(result_indices, &g.mutex_graph)
            }
            ResultKind::Verifier => result_indices,
        };

        debug!("[run_graph] max_thread_num={}", max_thread_num);
        debug!("[run_graph] total nodes={}, result_indices count={}", g.mutex_graph.node_indices().count(), result_indices.len());
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

        // Create the pool manager with capacity = max_thread_num.
        let pool_manager = PoolManager::new(max_thread_num);

        // Push the initial sync node (the input node) onto the sync queue
        // and submit any root Op nodes (remaining_deps == 0) that have no
        // predecessors — e.g. random values — to the pool manager.
        for ni in g.mutex_graph.node_indices() {
            match &g.mutex_graph[ni] {
                Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                    let rd = annotation.remaining_deps.load(Ordering::SeqCst);
                    if rd == 0 {
                        if is_sync_node(&g, ni) {
                            debug!("[run_graph] init: pushing sync node {:?} with remaining_deps=0", ni);
                            tx.push(ni);
                        } else {
                            let thread_num = annotation.thread_num;
                            let g_clone = Arc::clone(&g);
                            let inputs_clone = Arc::clone(&inputs);
                            let pm_clone = Arc::clone(&pool_manager);
                            let tx = tx.clone();
                            debug!("[run_graph] init: submitting non-sync node {:?} with remaining_deps=0 thread_num={}", ni, thread_num);
                            pool_manager.submit(
                                thread_num,
                                Box::new(move || {
                                    g_clone.handle_node(ni, inputs_clone.clone());
                                    update_successors(&g_clone, &inputs_clone, &pm_clone, tx, ni);
                                }),
                            );
                        }
                    }
                }
                Node::Inp(_, _) => {
                    debug!("[run_graph] pushing initial sync node {:?}", ni);
                    tx.push(ni);
                }
                Node::Rel(_, _) => {}
            }
        }

        drop(tx);

        // Phase 2: Main execution loop.
        //
        // Compute values for sync nodes (transcript and challenge).
        // Dispatch other computes to the pool manager, and wait for completion.
        let mut loop_count = 0u32;
        while let Some(SyncMessage { node_idx, tx }) = rx.pop() {
            loop_count += 1;

            debug!("[run_graph] loop iteration {}, processing sync node {:?}", loop_count, node_idx);

            match &g.mutex_graph[node_idx] {
                Node::Inp(_, prefs) => {
                    debug!("[run_graph] node {:?} is Inp/Rel with {} prefs", node_idx, prefs.len());
                    // Send public values through the sponge.
                    for pref in prefs.clone() {
                        if pref.qualifier.is_public() && !pref.from_transcript {
                            prover_state.public_message(
                                value_to_bytes(inputs.get(&pref.var().unwrap()).unwrap())
                                    .unwrap()
                                    .as_slice(),
                            );
                        }
                    }
                }
                Node::Transcr(op, annotation) => {
                    if matches!(**op, Op::Challenge(_, _)) {
                        debug!("[run_graph] node {:?} is Challenge", node_idx);
                        // Challenge node: squeeze the sponge.
                        let return_val = Value::<C>::challenge(prover_state);
                        *annotation.return_value.lock().unwrap() = Some(return_val);
                    } else {
                        debug!("[run_graph] node {:?} is Transcript", node_idx);
                        // Proof transcript node: compute value and send
                        // through the sponge.
                        g.handle_node(node_idx, Arc::clone(&inputs));
                        let return_val = annotation.return_value.lock().unwrap();
                        let serialized = value_to_bytes(return_val.as_ref().unwrap()).unwrap();
                        prover_state.public_message(serialized.as_slice());
                    }
                }
                Node::Op(_, _) | Node::Rel(_, _) => {
                    // Non-sync Op and Rel nodes should never appear on the sync
                    // channel. Panic indicates a logic error in scheduling.
                    unreachable!("non-sync Op node {:?} on sync channel", node_idx)
                }
            };

            // Update successors — pushes ready sync nodes to the sync queue
            // and submits non-sync nodes to the pool manager.
            debug!("[run_graph] calling update_successors for node {:?}", node_idx);
            update_successors(&g, &inputs, &pool_manager, tx, node_idx);
        }

        debug!("[run_graph] main loop completed after {} iterations", loop_count);

        // Phase 3: Collect results from pre-collected result indices.
        match result_kind {
            ResultKind::Prover => result_indices
                .into_iter()
                .filter_map(|n| match &g.mutex_graph[n] {
                    Node::Transcr(op, annotation) if !matches!(**op, Op::Challenge(_, _)) => {
                        annotation.return_value.lock().unwrap().clone()
                    }
                    _ => None,
                })
                .collect(),
            ResultKind::Verifier => result_indices
                .into_iter()
                .filter_map(|n| match &g.mutex_graph[n] {
                    Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                        annotation.return_value.lock().unwrap().clone()
                    }
                    _ => None,
                })
                .collect(),
        }
    }
}
