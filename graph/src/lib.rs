#![feature(deref_patterns)]
#![allow(clippy::result_large_err)]
//! Graph intermediate representation for Zippel protocols.
//!
//! This crate sits between `lang` and `runtime` in the pipeline: a type-checked
//! `TypedModule` is lowered into one [`Dag`] per declaration ([`UDags::lower`]),
//! the static analyses (the `analyses` crate) read it, and the prover and
//! verifier are obtained as subgraph projections ([`Dag::project_prover`],
//! [`Dag::project_verifier`]) before scheduling and execution.
//!
//! A [`Dag`] is a `petgraph` graph whose nodes are [`Node`]s carrying
//! hash-consed [`HOp`] operations and whose edges are [`Dep`]s, distinguishing
//! data flow from Fiat-Shamir transcript ordering.

// In #[cfg(test)] builds, alias the crate as `graph` so that test-only
// modules included via `#[path]` from outside the crate root (e.g. the
// `groebner_shared.rs` bench helper sourced by `speedup_bench.rs`) can
// reference `graph::Var`, `graph::analyses::...`, etc. with the same
// paths they use when compiled as external bench / integration test code.
#[cfg(test)]
extern crate self as graph;

mod dep;
/// Fiat-Shamir domain separation derived from a protocol's instance inputs.
pub mod domain_separator;
mod lower;
mod node;
mod pdf;
mod project;
#[cfg(any(test, feature = "testing"))]
pub mod testing;

#[cfg(test)]
mod tests;

pub use backend::op::{GOp, HOp, Op, OpExclusion, Ref, mk};
pub use dep::{Dep, DepType};
use log::debug;
pub use lower::Relations;
pub use node::{ArgKind, Node};

use backend::{Backend, PolyVariant};
use lang::ast::spanned::Spanned;
use lang::diagnostic::{Diagnostic, Phase};
use lang::id::Vid;
use lang::typ::infer::TypeError;
use lang::typ::{Nothing, Qualifier};
use share::{Ctx, Set};

use petgraph::{
    Direction, Graph,
    graph::{EdgeReference, Neighbors, NodeIndex, NodeIndices},
    visit::EdgeRef,
};
use std::collections::{HashMap, HashSet};
use std::ops::Index;
use thiserror::Error;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
#[derive(Clone)]
pub struct Dag<C: Backend, A> {
    /// The underlying `petgraph` structure: each node with the source span that created it
    /// (nodes are never deduplicated, so each has one), and [`Dep`] edges. The span lives here,
    /// not in the hash-consed operation, which every node computing it shares.
    pub graph: Graph<Spanned<Node<C, A>>, Dep>,
    /// The source names bound to each node, in order, each at its binding: an argument's
    /// declaration, then every `let`/`<-` naming it. The first is the node's name.
    pub bindings: Ctx<NodeIndex, Vec<Spanned<Vid>>>,
    /// Which variables are transcript variables (true) vs let-bindings (false)
    pub transcript_vars: Ctx<NodeIndex, bool>,
}

/// Dag with no annotations
pub type UDag<C> = Dag<C, Nothing>;

/// Dag with qualifiers
pub type QDag<C> = Dag<C, Qualifier>;

/// A collection of dags
#[derive(Clone)]
pub struct Dags<C: Backend, A>(Vec<Dag<C, A>>);
/// A collection of unannotated DAGs, one per module declaration.
pub type UDags<C> = Dags<C, Nothing>;
/// A collection of DAGs after qualifier propagation.
pub type QDags<C> = Dags<C, Qualifier>;

/// Failures raised while lowering a module into DAGs or projecting a DAG onto
/// one of the two protocol roles.
#[derive(Error, PartialEq, Debug)]
pub enum GraphError {
    /// A variable was referenced with no binding in the lowering context.
    #[error("Variable `{0}` is not defined")]
    VarNotFound(Spanned<Vid>),
    /// The named protocol has no `Node::Rel` marker, so it has no relation to
    /// project onto.
    #[error("`{0}` has no `where` relation")]
    RelationNotFound(Spanned<Vid>),
    /// The verifier projection reached a value only the prover has: an argument
    /// that is not `Qualifier::Instance`, or a `random` sample.
    #[error("The verifier depends on {}, which only the prover knows", describe_private(*.kind, .name.as_ref()))]
    PrivateValueInVerifier {
        /// What kind of prover-only value was reached.
        kind: PrivateValue,
        /// The value's variable name, if it is bound to one.
        name: Option<Vid>,
        /// Where the value is bound in the source.
        span: std::ops::Range<usize>,
        /// The named values on the way from it to the use, innermost first.
        via: Vec<Spanned<Vid>>,
        /// Where the verifier uses it: a `verify` check, or a challenge's
        /// exclusion.
        check: std::ops::Range<usize>,
    },
    /// A `lang`-level typing failure surfaced during lowering.
    #[error(transparent)]
    Type(Box<TypeError>),
    /// A `fun` body could not be reified as a `PolyVariant` because it uses
    /// operations outside the polynomial fragment (only addition, subtraction,
    /// multiplication and negation of bound variables are supported). Holds
    /// the reason and the source span of the offending subexpression.
    #[error("Fun expression contains non-polynomial operations: {0}")]
    NonPolynomialFun(String, std::ops::Range<usize>),
    /// The protocol needs something the backend lacks (see `GOp::unsupported`).
    #[error("{backend} cannot run this protocol: it needs {what}")]
    Unsupported {
        /// What is missing.
        what: backend::op::Unsupported,
        /// The backend's name.
        backend: String,
        /// The node that needs it.
        span: std::ops::Range<usize>,
    },
}

/// A value reachable from a verifier check that the verifier cannot know or recompute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrivateValue {
    /// An argument that is not qualified `instance`; holds its qualifier.
    Arg(Qualifier),
    /// A `random` sample, which the verifier would draw independently of the prover.
    Random,
}

fn describe_private(kind: PrivateValue, name: Option<&Vid>) -> String {
    let what = match kind {
        PrivateValue::Arg(Qualifier::Witness) => "witness",
        PrivateValue::Arg(Qualifier::Extra) => "`extra` argument",
        PrivateValue::Arg(_) => "argument not marked `instance`",
        PrivateValue::Random => "random value",
    };
    match name {
        Some(name) => format!("{what} `{name}`"),
        None => format!("a {what}"),
    }
}

/// Anchored where the failure is in the source.
impl From<&GraphError> for Diagnostic {
    fn from(e: &GraphError) -> Self {
        match e {
            GraphError::Type(e) => Diagnostic::from(&**e),
            GraphError::NonPolynomialFun(reason, span) => {
                Diagnostic::error(Phase::Type, span.clone(), "`fun` body is not a polynomial")
                    .primary_label(reason)
                    .note(
                        "a `fun` body may only add, subtract, multiply, and negate its parameters and constants",
                    )
            }
            GraphError::PrivateValueInVerifier {
                kind,
                name,
                span,
                via,
                check,
            } => {
                let label = match kind {
                    PrivateValue::Random => {
                        "sampled by the prover; the verifier would draw its own, different value"
                    }
                    PrivateValue::Arg(_) => "the verifier never receives this",
                };
                let mut d = Diagnostic::error(Phase::Type, span.clone(), &e.to_string())
                    .primary_label(label);
                // "`t` depends on `r`", from the value out to the check.
                let mut previous = name.as_ref().map_or("it".to_string(), |n| format!("`{n}`"));
                for step in via {
                    d = d.secondary_label(
                        step.span.clone(),
                        &format!("`{}` depends on {previous}", step.node),
                    );
                    previous = format!("`{}`", step.node);
                }
                d.secondary_label(check.clone(), "the verifier uses it here")
                    .note(
                        "the verifier may only use `instance` arguments, challenges, and values \
                         the prover sends with `<-` (directly or through `let`s)",
                    )
            }
            GraphError::VarNotFound(id) => {
                Diagnostic::error(Phase::Type, id.span.clone(), &e.to_string())
                    .primary_label("not defined here")
            }
            GraphError::RelationNotFound(name) => {
                Diagnostic::error(Phase::Type, name.span.clone(), &e.to_string())
                    .primary_label("declared without a `where` clause")
            }
            GraphError::Unsupported { what, span, .. } => {
                let label = match what {
                    backend::op::Unsupported::Pairing => "needs a pairing",
                    backend::op::Unsupported::Group => "needs a group",
                    backend::op::Unsupported::FftDomain { .. } => "needs a larger FFT domain",
                };
                Diagnostic::error(Phase::Type, span.clone(), &e.to_string())
                    .primary_label(label)
                    .note("compile the protocol for a backend that has it")
            }
        }
    }
}

impl From<GraphError> for Diagnostic {
    fn from(e: GraphError) -> Self {
        Diagnostic::from(&e)
    }
}

/// The Rust name of backend `C` (as `compile::<C>` spells it), without its module path.
fn backend_name<C>() -> String {
    let full = std::any::type_name::<C>();
    let head = full.split('<').next().unwrap_or(full);
    let start = head.rfind("::").map_or(0, |i| i + 2);
    full[start..].to_string()
}

impl From<TypeError> for GraphError {
    fn from(e: TypeError) -> Self {
        GraphError::Type(Box::new(e))
    }
}

/// `weight` with its node replaced by `f` of it, keeping the node's span.
fn respan<C: Backend, A, B>(
    weight: &Spanned<Node<C, A>>,
    f: impl FnOnce(&Node<C, A>) -> Node<C, B>,
) -> Spanned<Node<C, B>> {
    Spanned::new(f(&weight.node), weight.span.clone())
}

/// `name`, or the first of `name#2`, `name#3`, ... not in `taken`, which it is added to.
/// Source identifiers cannot contain `#`, so the result never collides with one.
fn unique_name(name: &Vid, taken: &mut HashSet<Vid>) -> Vid {
    let mut candidate = name.clone();
    let mut k = 2;
    while taken.contains(&candidate) {
        candidate = Vid(format!("{}#{k}", name.0));
        k += 1;
    }
    taken.insert(candidate.clone());
    candidate
}

/// A trait for writing a graph to a PDF file
pub trait WritePdf {
    /// Renders the graph to `filename` as a PDF.
    ///
    /// # Errors
    /// Returns the underlying `std::io::Error` if the intermediate DOT file
    /// cannot be written or the external `dot` invocation fails.
    fn write_pdf(&self, filename: &str) -> std::io::Result<()>;
}

impl GraphError {
    /// Builds a [`GraphError::VarNotFound`] for an unbound variable, at its use.
    pub fn var_not_found(vid: &Spanned<Vid>) -> Self {
        GraphError::VarNotFound(vid.clone())
    }
    /// Builds a [`GraphError::PrivateValueInVerifier`] for the prover-only value bound at `span`,
    /// reaching the check at `check` through the named values `via`.
    pub fn private_value_in_verifier(
        kind: PrivateValue,
        name: Option<Vid>,
        span: std::ops::Range<usize>,
        via: Vec<Spanned<Vid>>,
        check: std::ops::Range<usize>,
    ) -> Self {
        GraphError::PrivateValueInVerifier {
            kind,
            name,
            span,
            via,
            check,
        }
    }
    /// Builds a [`GraphError::RelationNotFound`] for the declaration named `vid`.
    pub fn relation_not_found(vid: &Spanned<Vid>) -> Self {
        GraphError::RelationNotFound(vid.clone())
    }
    /// Attaches `span` to a type error that inference left unlocated.
    fn located(self, span: &std::ops::Range<usize>) -> Self {
        match self {
            GraphError::Type(e) => GraphError::Type(Box::new(TypeError::located(span, *e))),
            e => e,
        }
    }
}

/// Compare two `Node` values for isomorphism-compatible equality.
/// Erases `NodeIndex` inside `GOp` and `Var` so that structurally
/// identical nodes from different graphs compare as equal.
fn nodes_isomorphic_eq<C: Backend, A: PartialEq + Clone>(a: &Node<C, A>, b: &Node<C, A>) -> bool {
    let erase = |_: NodeIndex| NodeIndex::new(0);
    match (a, b) {
        (Node::Inp(v1), Node::Inp(v2)) => v1 == v2,
        (Node::Rel(v1), Node::Rel(v2)) => v1 == v2,
        (Node::Arg(v1, t1, q1, d1, k1), Node::Arg(v2, t2, q2, d2, k2)) => {
            v1 == v2 && t1 == t2 && q1 == q2 && d1 == d2 && k1 == k2
        }
        (Node::Op(op1, ann1), Node::Op(op2, ann2)) => {
            op1.map_node_indices(&erase) == op2.map_node_indices(&erase) && ann1 == ann2
        }
        (Node::Transcr(op1, ann1), Node::Transcr(op2, ann2)) => {
            op1.map_node_indices(&erase) == op2.map_node_indices(&erase) && ann1 == ann2
        }
        _ => false,
    }
}

impl<C: Backend, A: PartialEq + Clone> PartialEq for Dag<C, A> {
    fn eq(&self, other: &Self) -> bool {
        petgraph::algo::is_isomorphic_matching(
            &self.graph,
            &other.graph,
            |a, b| nodes_isomorphic_eq(a, b),
            |a, b| a == b,
        ) && self.bindings == other.bindings
            && self.transcript_vars == other.transcript_vars
    }
}

impl<C: Backend, A> Default for Dag<C, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: Backend, A> Dag<C, A> {
    /// Checks that backend `C` can run every node: no pairing or target-group value
    /// without a pairing, no group value without groups, and no FFT larger than the
    /// field's largest FFT domain.
    ///
    /// # Errors
    /// [`GraphError::Unsupported`] at the first node that needs what `C` lacks.
    pub fn check_backend(&self) -> Result<(), GraphError> {
        for node in self.graph.node_weights() {
            let what = match &node.node {
                Node::Arg(_, typ, ..) => backend::op::unsupported_type::<C>(typ),
                Node::Op(op, _) | Node::Transcr(op, _) => op.unsupported(),
                Node::Inp(_) | Node::Rel(_) => None,
            };
            if let Some(what) = what {
                return Err(GraphError::Unsupported {
                    what,
                    backend: backend_name::<C>(),
                    span: node.span.clone(),
                });
            }
        }
        Ok(())
    }

    /// Creates an empty DAG with no nodes and empty name contexts.
    pub fn new() -> Self {
        Dag {
            graph: Graph::new(),
            bindings: Ctx::new(),
            transcript_vars: Ctx::new(),
        }
    }

    /// Print all edges in the graph
    pub fn print_edges(&self) {
        for edge in self.graph.edge_references() {
            let source = edge.source();
            let target = edge.target();
            debug!("Edge from {:?} to {:?}", source, target);
        }
    }

    /// Get the number of nodes in the graph
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// All node indices, materialised into a `Vec`.
    pub fn node_indices_vec(&self) -> Vec<NodeIndex> {
        self.graph.node_indices().collect()
    }

    /// Get the number of edges in the graph
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// The `Node::Inp` marker that anchors the declaration's arguments.
    ///
    /// # Panics
    /// Panics if the DAG has no input marker, i.e. it was never populated by
    /// `add_decl`.
    pub fn input_node(&self) -> NodeIndex {
        self.graph
            .node_indices()
            .find(|n| self.graph[*n].is_input())
            .expect("No input node found, DAG uninitialized")
    }

    /// The `Node::Rel` marker, present only for protocols (a `fun` declaration
    /// has no `where` clause and therefore no relation).
    pub fn relation_node(&self) -> Option<NodeIndex> {
        self.graph
            .node_indices()
            .find(|n| self.graph[*n].is_relation())
    }

    /// All nodes holding a non-transcript operation.
    pub fn op_nodes(&self) -> Vec<NodeIndex> {
        self.graph
            .node_indices()
            .filter(|n| self[*n].is_op())
            .collect()
    }

    /// All `Arg` nodes belonging to the input marker, in NodeIndex (= source) order.
    pub fn input_args(&self) -> Vec<NodeIndex> {
        let mut out: Vec<NodeIndex> = self
            .graph
            .node_indices()
            .filter(|n| self[*n].is_input_arg())
            .collect();
        out.sort();
        out
    }

    /// All `Arg` nodes belonging to the relation marker, in NodeIndex order.
    pub fn relation_args(&self) -> Vec<NodeIndex> {
        let mut out: Vec<NodeIndex> = self
            .graph
            .node_indices()
            .filter(|n| self[*n].is_relation_arg())
            .collect();
        out.sort();
        out
    }

    /// Adds an edge from `source` to `sink`, unless it would be a self-loop.
    pub fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Dep) {
        // If the edge is not a self-loop add it
        if source != sink {
            self.graph.add_edge(source, sink, edge);
        }
    }

    /// Adds an `edge_type` edge to `sink` from every node `source` references.
    pub fn add_edges(&mut self, edge_type: DepType, sink: NodeIndex, source: GOp<C>) {
        source.references().into_iter().for_each(|refer| {
            self.add_edge(refer.node(), sink, Dep(edge_type));
        });
    }

    /// Returns the reachable nodes (transitive, reflexive closure) from `n` in `direction`
    pub fn trc(&self, n: NodeIndex, direction: Direction) -> Set<NodeIndex> {
        let mut closure = Set::new();
        let mut worklist = vec![n];

        while let Some(n) = worklist.pop() {
            if closure.contains(&n) {
                continue;
            }
            closure.insert(n);
            for neighbor in self.graph.neighbors_directed(n, direction) {
                worklist.push(neighbor);
            }
        }
        closure
    }

    /// Adds `node`, created by the source at `span` (no deduplication).
    pub fn add_node(&mut self, node: Node<C, A>, span: std::ops::Range<usize>) -> NodeIndex {
        self.graph.add_node(Spanned::new(node, span))
    }

    /// Adds a copy of another graph's node, keeping its span.
    fn add_weight(&mut self, weight: Spanned<Node<C, A>>) -> NodeIndex {
        self.graph.add_node(weight)
    }

    /// The source span that created `node`.
    pub fn span(&self, node: NodeIndex) -> std::ops::Range<usize> {
        self.graph[node].span.clone()
    }

    /// Mutable access to a node weight, used by passes that rewrite
    /// annotations in place.
    pub fn node_mut(&mut self, it: NodeIndex) -> &mut Node<C, A> {
        &mut self.graph[it].node
    }

    /// Records that the source binds `name` to `node`.
    pub fn bind(&mut self, node: NodeIndex, name: &Spanned<Vid>) {
        match self.bindings.get_mut(&node) {
            Some(names) => names.push(name.clone()),
            None => {
                self.bindings.insert(&node, &vec![name.clone()]);
            }
        }
    }

    /// The first binding of `node`, if the source names it.
    pub fn binding(&self, node: NodeIndex) -> Option<&Spanned<Vid>> {
        self.bindings.get(&node).and_then(|names| names.first())
    }

    /// The name of `node`: its first binding, or the name on an input or relation marker.
    pub fn find_var(&self, node: NodeIndex) -> Option<Vid> {
        match self.binding(node) {
            Some(name) => Some(name.node.clone()),
            None => self[node].name().cloned(),
        }
    }

    /// The path from `from` to the check that needed it, following `via` (each node ↦ the node
    /// that needed it): the named nodes on the way, innermost first, and the check's span.
    fn use_path(
        &self,
        via: &HashMap<NodeIndex, NodeIndex>,
        from: NodeIndex,
    ) -> (Vec<Spanned<Vid>>, std::ops::Range<usize>) {
        let mut steps = Vec::new();
        let mut node = from;
        while let Some(&next) = via.get(&node) {
            steps.extend(self.binding(node).cloned());
            node = next;
        }
        (steps, self.span(node))
    }

    /// Wraps a node index as a [`Ref`], the form operations use to point at
    /// their children.
    pub fn find_ref(&self, node: NodeIndex) -> Ref {
        Ref(node)
    }

    /// Iterator over the graph's node indices.
    pub fn node_indices(&self) -> NodeIndices {
        self.graph.node_indices()
    }

    /// The highest node index currently allocated.
    ///
    /// # Panics
    /// Panics if the graph is empty.
    pub fn max_node(&self) -> NodeIndex {
        self.graph.node_indices().next_back().unwrap()
    }

    /// The declaration's name, read off its input marker.
    ///
    /// # Panics
    /// Panics if the DAG has no input marker or the marker carries no name.
    pub fn name(&self) -> Vid {
        let inp = self.input_node();
        self[inp].name().unwrap().clone()
    }

    /// Annotate the graph using function `f`
    pub fn map_annotations<B, F: Fn(&GOp<C>, &A) -> B>(&self, f: &F) -> Dag<C, B> {
        Dag {
            graph: self.graph.map(
                |_, w| {
                    respan(w, |node| match node {
                        Node::Op(op, ann) => Node::Op(op.clone(), f(op, ann)),
                        Node::Transcr(op, ann) => Node::Transcr(op.clone(), f(op, ann)),
                        Node::Inp(a) => Node::Inp(a.clone()),
                        Node::Rel(a) => Node::Rel(a.clone()),
                        Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
                    })
                },
                |_, e| *e,
            ),
            bindings: self.bindings.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    /// Neighbours of `node_index` along `direction`, over both data and
    /// transcript edges.
    pub fn neighbors_directed(
        &self,
        node_index: NodeIndex,
        direction: Direction,
    ) -> Neighbors<'_, Dep, u32> {
        self.graph.neighbors_directed(node_index, direction)
    }

    /// The transcript edge incident to `n` in `dir`, if any.
    ///
    /// At most one exists per direction, since transcript nodes form a chain.
    pub fn transcript_edge<'a>(
        &'a self,
        n: NodeIndex,
        dir: Direction,
    ) -> Option<EdgeReference<'a, Dep>> {
        self.graph
            .edges_directed(n, dir)
            .find(|edge| edge.weight().is_transcript())
    }

    /// Get all transcript nodes from the graph (challenges and proof nodes),
    /// topologically ordered with respect to `Dep::Transcript` edges.
    ///
    /// Graph construction maintains transcript nodes as a single transcript-edge
    /// chain, so ordering is just walking from the root transcript node to the end
    /// of that chain.
    ///
    /// # Panics
    /// Panics if no transcript node lacks a transcript parent, which means the
    /// chain contains a cycle.
    pub fn transcript_nodes(&self) -> Vec<NodeIndex> {
        let transcript_nodes: Vec<NodeIndex> = self
            .graph
            .node_indices()
            .filter(|&node| self[node].is_transcript())
            .collect();

        if transcript_nodes.is_empty() {
            return Vec::new();
        }

        let transcript_node_set: HashSet<NodeIndex> = transcript_nodes.iter().copied().collect();
        let mut transcript_child_by_parent: HashMap<NodeIndex, NodeIndex> = HashMap::new();
        let mut nodes_with_transcript_parent: HashSet<NodeIndex> = HashSet::new();

        for &node in &transcript_nodes {
            if let Some(edge) = self.transcript_edge(node, Direction::Incoming) {
                let parent = edge.source();
                if transcript_node_set.contains(&parent) {
                    transcript_child_by_parent.insert(parent, node);
                    nodes_with_transcript_parent.insert(node);
                }
            }
        }

        let root = transcript_nodes
            .iter()
            .find(|&&n| !nodes_with_transcript_parent.contains(&n))
            .expect("Cycle detected in transcript nodes");

        let mut ordered = vec![*root];
        let mut current = *root;
        while let Some(&child) = transcript_child_by_parent.get(&current) {
            ordered.push(child);
            current = child;
        }

        ordered
    }

    /// Get all proof nodes from the graph
    pub fn get_proof_nodes(&self) -> Vec<NodeIndex> {
        self.transcript_nodes()
            .into_iter()
            .filter(|n| self[*n].is_proof())
            .collect()
    }

    /// Get all challenge nodes from the graph
    pub fn get_challenge_nodes(&self) -> Vec<NodeIndex> {
        self.transcript_nodes()
            .into_iter()
            .filter(|n| self[*n].is_challenge())
            .collect()
    }

    /// Get all verifier checks: `Verify` nodes with no outgoing edges. The
    /// `where` clause's `Assert` is not a check and is excluded.
    pub fn find_verify(&self) -> Vec<NodeIndex> {
        self.node_indices()
            .filter(|&n| match &self[n] {
                Node::Op(op, _) | Node::Transcr(op, _) => {
                    matches!(&**op, Op::Verify(_)) && self.nodes_from(n).count() == 0
                }
                _ => false,
            })
            .collect()
    }

    /// Seeds for the prover projection — the nodes whose values the prover
    /// is obliged to produce: the transcript nodes, which carry the proof
    /// values. The `where` clause's `Assert` is not a seed; only the static
    /// analyses, which run on the full DAG, read it.
    fn prover_roots(&self) -> Vec<NodeIndex> {
        self.transcript_nodes()
    }

    /// Successors of `n`: the nodes that consume it or follow it in the
    /// transcript.
    pub fn nodes_from(&self, n: NodeIndex) -> Neighbors<'_, Dep, u32> {
        self.graph.neighbors_directed(n, Direction::Outgoing)
    }

    /// Predecessors of `n`: the nodes it consumes or follows.
    pub fn nodes_to(&self, n: NodeIndex) -> Neighbors<'_, Dep, u32> {
        self.graph.neighbors_directed(n, Direction::Incoming)
    }

    /// Drops every node annotation, yielding an unannotated [`UDag`].
    ///
    /// Used to re-run an analysis from scratch on an already-annotated DAG.
    pub fn erase_ann(self) -> UDag<C> {
        Dag {
            graph: self.graph.map(
                |_, w| {
                    respan(w, |node| match node {
                        Node::Inp(a) => Node::Inp(a.clone()),
                        Node::Rel(a) => Node::Rel(a.clone()),
                        Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
                        Node::Op(op, _) => Node::Op(op.clone(), Nothing),
                        Node::Transcr(op, _) => Node::Transcr(op.clone(), Nothing),
                    })
                },
                |_, e| *e,
            ),
            bindings: self.bindings.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    /// Join two DAGs into one
    /// WARNING: This function does not remap Refs, so it is not safe to use in general.
    pub fn combine_dag(&self, other: &Self) -> Self
    where
        A: Clone,
    {
        let mut combined_graph = Graph::with_capacity(
            self.node_count() + other.node_count(),
            self.edge_count() + other.edge_count(),
        );

        // To map old NodeIndex values from self to new NodeIndex values in combined_graph
        let mut node_map_self = HashMap::<NodeIndex, NodeIndex>::new();
        // To map old NodeIndex values from other to new NodeIndex values in combined_graph
        let mut node_map_other = HashMap::<NodeIndex, NodeIndex>::new();

        // Add nodes from self and populate node_map_self
        for old_node_idx in self.node_indices() {
            if let Some(weight) = self.graph.node_weight(old_node_idx) {
                let new_node_idx = combined_graph.add_node(weight.clone());
                node_map_self.insert(old_node_idx, new_node_idx);
            }
        }

        // Add nodes from other and populate node_map_other
        for old_node_idx in other.node_indices() {
            if let Some(weight) = other.graph.node_weight(old_node_idx) {
                let new_node_idx = combined_graph.add_node(weight.clone());
                node_map_other.insert(old_node_idx, new_node_idx);
            }
        }

        // Add edges from self using the mapped node indices
        for edge_ref in self.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if let (Some(new_source_idx), Some(new_target_idx)) = (
                node_map_self.get(&old_source_idx),
                node_map_self.get(&old_target_idx),
            ) {
                combined_graph.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }

        // Add edges from other using the mapped node indices
        for edge_ref in other.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if let (Some(new_source_idx), Some(new_target_idx)) = (
                node_map_other.get(&old_source_idx),
                node_map_other.get(&old_target_idx),
            ) {
                combined_graph.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }

        // Merge bindings and transcript_vars from both DAGs with remapped keys
        let mut merged_bindings = Ctx::new();
        for (k, v) in self.bindings.iter() {
            if let Some(new_k) = node_map_self.get(k) {
                merged_bindings.insert(new_k, v);
            }
        }
        for (k, v) in other.bindings.iter() {
            if let Some(new_k) = node_map_other.get(k) {
                merged_bindings.insert(new_k, v);
            }
        }
        let mut merged_transcript = Ctx::new();
        for (k, v) in self.transcript_vars.iter() {
            if let Some(new_k) = node_map_self.get(k) {
                merged_transcript.insert(new_k, v);
            }
        }
        for (k, v) in other.transcript_vars.iter() {
            if let Some(new_k) = node_map_other.get(k) {
                merged_transcript.insert(new_k, v);
            }
        }

        Dag {
            graph: combined_graph,
            bindings: merged_bindings,
            transcript_vars: merged_transcript,
        }
    }
}

/// A collection of DAGs
impl<C: Backend, A> Default for Dags<C, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: Backend, A> Dags<C, A> {
    /// Creates an empty collection.
    pub fn new() -> Self {
        Dags(Vec::new())
    }

    /// Removes and returns the last DAG, if any.
    pub fn pop(&mut self) -> Option<Dag<C, A>> {
        self.0.pop()
    }

    /// Number of DAGs in the collection.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the collection holds no DAGs.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The DAGs, in declaration order.
    pub fn iter(&self) -> std::slice::Iter<'_, Dag<C, A>> {
        self.0.iter()
    }

    /// Finds the protocol whose input marker carries `name`.
    ///
    /// Only protocols are searched, so a `fun` declaration sharing the name is
    /// never returned.
    pub fn protocol(&self, name: &String) -> Option<&Dag<C, A>> {
        self.protocols().into_iter().find(|g| {
            if let Some(v) = g[g.input_node()].name() {
                &v.0 == name
            } else {
                false
            }
        })
    }

    /// A protocol has a relation node
    pub fn protocols(&self) -> Vec<&Dag<C, A>> {
        self.0
            .iter()
            .filter(|g| g.relation_node().is_some())
            .collect()
    }

    /// The declarations with no relation node, i.e. plain `fun` definitions.
    pub fn functions(&self) -> Vec<&Dag<C, A>> {
        self.0
            .iter()
            .filter(|g| g.relation_node().is_none())
            .collect()
    }

    /// Annotate all graphs using function `f`
    pub fn map_annotations<B, F: Fn(&GOp<C>, &A) -> B>(&self, f: &F) -> Dags<C, B> {
        Dags(self.0.iter().map(|g| g.map_annotations(f)).collect())
    }
}

impl<C: Backend, A> Index<NodeIndex> for Dag<C, A> {
    type Output = Node<C, A>;
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.graph[index].node
    }
}

impl<C: Backend, A> std::ops::IndexMut<NodeIndex> for Dag<C, A> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.graph[index].node
    }
}

impl<C: Backend, A> Index<usize> for Dags<C, A> {
    type Output = Dag<C, A>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

#[cfg(test)]
use crate::tests::test_helpers::{lowered, parse_and_check};
#[cfg(test)]
use backend::ArkBls12_381;
#[cfg(test)]
use share::unwrap;
#[test]
fn graph_sum() {
    let ex = r#"
        fn sum<N: 1..4, F: Field>(instance a: [F; 2^N]) -> F {
            sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])
        }

        fn sum<F: Field>(instance a: [F; 1]) -> F {
           a[0]
        }"#;
    let m = parse_and_check(ex, &Ctx::new());
    assert_eq!(m.module().len(), 4);
    let gs = unwrap!(UDags::<ArkBls12_381>::lower(&m, Relations::Lower));
    gs.write_pdf("graph_sum").unwrap_or_else(|e| {
        debug!(
            "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
            e
        );
    });
}

#[test]
fn graph_foo() {
    let ex = r#"
        proto foo<F: Field>(witness s: F, instance v: [F; 10]) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r + c + s;
            x <- v[1..5];
            verify(a * s == b * x[3])
        }"#;
    let gs = unwrap!(lowered::<ArkBls12_381>(ex, &Ctx::new()));
    // Output graph
    gs.write_pdf("graph_foo").unwrap_or_else(|e| {
        debug!(
            "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
            e
        );
    });
}

#[test]
fn graph_poly() {
    let ex = r#"
        proto poly_mul<F: Field>(instance a: Uni<F, 4>, instance b: Uni<F, 4>) where a == a {
            let r = random<F>;
            let p = a * b;
            verify(p(r) == (a(r) * b(r)))
        }"#;
    let gs = unwrap!(lowered::<ArkBls12_381>(ex, &Ctx::new()));
    gs.write_pdf("graph_poly").unwrap_or_else(|e| {
        debug!(
            "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
            e
        );
    });
}

#[test]
fn graph_reduce() {
    let ex = r#"
        fn reduction_foo<F: Field>(instance a: [F; 10]) -> F {
            reduce(+, a)
        }"#;
    let gs = unwrap!(lowered::<ArkBls12_381>(ex, &Ctx::new()));
    gs.write_pdf("graph_reduce").unwrap_or_else(|e| {
        debug!(
            "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
            e
        );
    });
}

#[test]
fn graph_fn_call_in_where() {
    // Function call in where clause: double(a) == a + a
    let ex = r#"
        fn double<F: Field>(instance x: F) -> F { x + x }
        proto test<F: Field>(instance a: F)
        where double(a) == a + a {
            verify(a == a)
        }"#;
    let gs = unwrap!(lowered::<ArkBls12_381>(ex, &Ctx::new()));
    gs.write_pdf("graph_fn_in_where").unwrap_or_else(|e| {
        debug!(
            "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
            e
        );
    });
}
