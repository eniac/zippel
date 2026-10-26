//! The executable graph: a scheduled DAG whose compute nodes carry the state
//! one run needs (an inbox of operands, a dependency counter), plus what the
//! scheduler reads on every step, computed once here: each node's distinct
//! successors, the nodes ready at the start, the input marker and the checks.

use crate::eval::Sampler;
use crate::eval::error::EvalError;
use backend::{Backend, Value};
use graph::{Dag, GOp, Node, Op, UDag};
use lang::ast::Exclusion;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crate::error::RuntimeError;
use crate::inbox::Inbox;

/// The state of one compute (`Op`/`Transcr`) node during the run.
///
/// A node never stores its own value: when it finishes, it delivers the
/// value into the [`Inbox`] of each successor that reads it, and the value
/// is freed once the last of them has run.
pub(crate) struct NodeState<C: Backend> {
    /// Operands delivered by the nodes this one reads; taken when it runs.
    pub(crate) inbox: Inbox<Value<C>>,
    /// Set when the node runs, to catch a scheduler running it twice.
    pub(crate) executed: AtomicBool,
    /// Predecessors that have not finished yet; the node is ready when it
    /// reaches zero. Starts at the number of distinct predecessors.
    remaining_deps: AtomicUsize,
}

impl<C: Backend> NodeState<C> {
    /// Records that the predecessor `from` has finished, taking its value if
    /// it produced one, and returns whether this node is now ready to run.
    pub(crate) fn receive(&self, from: NodeIndex, value: Option<&Value<C>>) -> bool {
        if let Some(value) = value {
            self.inbox.deliver(graph::Ref(from), value);
        }
        self.remaining_deps.fetch_sub(1, Ordering::SeqCst) == 1
    }
}

/// A [`UDag`] ready to run once: each compute node carries its
/// [`NodeState`], and the scheduling tables are precomputed.
///
/// The jobs of one `rayon::scope` drive it concurrently (see
/// [`MutexGraph::run_graph`]). A node refuses to run twice, so a
/// `MutexGraph` runs once; build a new one per run.
pub struct MutexGraph<C: Backend> {
    pub(crate) dag: Dag<C, NodeState<C>>,
    /// Each node's distinct successors, sorted, by node index: a run spawns
    /// ready nodes in the same order every time (the order changes which
    /// values are alive at once, so the peak heap).
    successors: Vec<Box<[NodeIndex]>>,
    /// The compute nodes with no predecessor, ready when the run starts.
    roots: Vec<NodeIndex>,
    /// The input marker, whose instance inputs begin the transcript.
    input: Option<NodeIndex>,
    /// The `Verify` nodes, in node-index order.
    checks: Vec<NodeIndex>,
}

impl<C: Backend> MutexGraph<C> {
    /// Wrap a scheduled DAG for execution: give every compute node a fresh
    /// [`NodeState`] and compute the scheduling tables.
    ///
    /// # Panics
    ///
    /// Panics if a node reads a node it has no dependency edge from (its
    /// operand would never be delivered), if two `Arg` nodes read the same
    /// input, or if the graph has more than one input marker (the second's
    /// instance inputs could be queued after a challenge).
    pub fn new(dag: UDag<C>) -> Self {
        let dag = dag.map_annotations(&|op: &GOp<C>, _| NodeState {
            inbox: Inbox::new(op.references()),
            executed: AtomicBool::new(false),
            remaining_deps: AtomicUsize::new(0),
        });
        let distinct = |node, direction| {
            let mut nodes: Vec<NodeIndex> = dag.neighbors_directed(node, direction).collect();
            nodes.sort_unstable();
            nodes.dedup();
            nodes
        };

        let mut successors = Vec::with_capacity(dag.node_count());
        let mut roots = Vec::new();
        let mut inputs = Vec::new();
        let mut checks = Vec::new();
        let mut arg_names = HashSet::new();
        for node in dag.node_indices() {
            debug_assert_eq!(node.index(), successors.len(), "node indices are dense");
            successors.push(distinct(node, Direction::Outgoing).into_boxed_slice());
            match &dag[node] {
                Node::Op(op, state) | Node::Transcr(op, state) => {
                    let predecessors = distinct(node, Direction::Incoming);
                    for source in state.inbox.sources() {
                        assert!(
                            predecessors.binary_search(&source.0).is_ok(),
                            "node {node:?} reads {source:?} without a dependency edge from it"
                        );
                    }
                    state
                        .remaining_deps
                        .store(predecessors.len(), Ordering::SeqCst);
                    if predecessors.is_empty() {
                        roots.push(node);
                    }
                    if matches!(dag[node], Node::Op(_, _)) && matches!(**op, Op::Verify(_)) {
                        checks.push(node);
                    }
                }
                Node::Inp(_) => inputs.push(node),
                Node::Rel(_) => {}
                Node::Arg(name, _, _, _, _) => {
                    assert!(arg_names.insert(name), "two `Arg` nodes read input {name}");
                }
            }
        }
        assert!(
            inputs.len() <= 1,
            "a graph has at most one input marker, found {}",
            inputs.len()
        );
        Self {
            successors,
            roots,
            input: inputs.first().copied(),
            checks,
            dag,
        }
    }

    /// The state of a compute (`Op`/`Transcr`) node; `None` for a marker or
    /// an `Arg`.
    pub(crate) fn state(&self, node: NodeIndex) -> Option<&NodeState<C>> {
        match &self.dag[node] {
            Node::Op(_, state) | Node::Transcr(_, state) => Some(state),
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => None,
        }
    }

    /// Every compute node's state.
    pub(crate) fn states(&self) -> impl Iterator<Item = &NodeState<C>> {
        self.dag.node_indices().filter_map(|n| self.state(n))
    }

    /// `node`'s distinct successors, sorted.
    pub(crate) fn successors(&self, node: NodeIndex) -> &[NodeIndex] {
        &self.successors[node.index()]
    }

    /// The compute nodes ready when the run starts.
    pub(crate) fn roots(&self) -> &[NodeIndex] {
        &self.roots
    }

    /// The input marker, if the graph has one.
    pub(crate) const fn input(&self) -> Option<NodeIndex> {
        self.input
    }

    /// The `Verify` nodes, in node-index order.
    pub(crate) fn checks(&self) -> &[NodeIndex] {
        &self.checks
    }

    /// Evaluates compute node `node` on the operands in its inbox, which are
    /// dropped once the op has been evaluated. Returns its value, and for a
    /// node that evaluated checks whether all of them passed (a later check
    /// must not hide an earlier failure).
    ///
    /// # Errors
    ///
    /// [`RuntimeError::DivisionByZero`] if the node divides by zero.
    ///
    /// # Panics
    ///
    /// Panics if `node` is not a compute node, if an operand was not
    /// delivered (a scheduling bug), or if `eval_op` fails otherwise: every
    /// shape and type precondition is established by the `lang` type checker
    /// and the scheduler, so a failure is a compiler invariant violation.
    pub(crate) fn evaluate(
        &self,
        node: NodeIndex,
        sampler: &mut impl Sampler<C>,
    ) -> Result<(Value<C>, Option<bool>), RuntimeError> {
        let (Node::Op(op, state) | Node::Transcr(op, state)) = &self.dag[node] else {
            unreachable!("node {node:?} has nothing to compute")
        };
        let env = state.inbox.take_all();
        let mut checks = Vec::new();
        let value = match crate::eval::eval_op(op, &env, sampler, &mut checks) {
            Err(EvalError::DivisionByZero) => return Err(RuntimeError::DivisionByZero),
            value => {
                value.expect("runtime invariant violation: eval_op failed on a scheduled node")
            }
        };
        let passed = (!checks.is_empty()).then(|| checks.iter().all(|&p| p));
        Ok((value, passed))
    }

    /// Evaluates what challenge `node` excludes on the operands in its inbox,
    /// which are dropped once read: a lookup, since the excluded vector is a
    /// node or a literal.
    ///
    /// # Panics
    ///
    /// Panics if `node` is not a challenge, or as [`MutexGraph::evaluate`]
    /// does.
    pub(crate) fn evaluate_exclusion(&self, node: NodeIndex) -> Option<Exclusion<Value<C>, usize>> {
        let Node::Transcr(op, state) = &self.dag[node] else {
            unreachable!("node {node:?} is not a challenge")
        };
        let Op::Challenge(_, exclusion) = &**op else {
            unreachable!("node {node:?} is not a challenge")
        };
        let env = state.inbox.take_all();
        exclusion.clone().map(|x| {
            x.map_order(|n| n.node).map_values(|v| {
                crate::eval::eval_op(&v, &env, &mut crate::eval::PureBody, &mut Vec::new())
                    .expect("runtime invariant violation: an exclusion failed to evaluate")
            })
        })
    }
}
