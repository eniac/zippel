#![feature(box_patterns)]
#![allow(clippy::result_large_err)]

// In #[cfg(test)] builds, alias the crate as `graph` so that test-only
// modules included via `#[path]` from outside the crate root (e.g. the
// `groebner_shared.rs` bench helper sourced by `speedup_bench.rs`) can
// reference `graph::PRef`, `graph::analyses::...`, etc. with the same
// paths they use when compiled as external bench / integration test code.
#[cfg(test)]
extern crate self as graph;

pub mod analyses;
mod dep;
pub mod domain_seperator;
pub mod eval;
mod node;
pub mod pref;
pub mod scheduler;

#[cfg(test)]
mod tests;

pub use backend::op::{GOp, HOp, HasOpFactory, Op, ReduceMapDomainFact, Ref, mk};
pub use dep::{Dep, DepType};
use log::debug;
pub use node::{ArgKind, Node};
pub use pref::PRef;

use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, univariate::DensePolynomial};
use backend::{ATyp, ArkConfig, PolyVariant, Value, VirtualPolynomial};
use lang::ast::{Arg, BinOp, CBody, CExp, CModule, CSig};
use lang::id::{Tid, Vid};
use lang::typ::infer::{TypeError, Typeable};
use lang::typ::range::CRange;
use lang::typ::{CKind, CTyp, CTyps, Distribution, Nothing, Qualifier};
use share::{Ctx, Set, traversal::ToTraversal1};

use petgraph::{
    Direction, Graph,
    dot::Dot,
    graph::{EdgeReference, Neighbors, NodeIndex, NodeIndices},
    visit::EdgeRef,
};
use std::collections::{HashMap, HashSet};
use std::ops::Index;
use std::path::PathBuf;
use std::process::Command;
use thiserror::Error;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
#[derive(Clone)]
pub struct Dag<C: ArkConfig, A> {
    pub(crate) graph: Graph<Node<C, A>, Dep>,
    /// Variable names for nodes (both let-bindings and transcript vars)
    pub(crate) vctx: Ctx<NodeIndex, Vid>,
    /// Which variables are transcript variables (true) vs let-bindings (false)
    pub(crate) transcript_vars: Ctx<NodeIndex, bool>,
}

/// Dag with no annotations
pub type UDag<C> = Dag<C, Nothing>;

/// Dag with qualifiers
pub type QDag<C> = Dag<C, Qualifier>;

/// Dag with qualifiers and distributions
pub type DQDag<C> = Dag<C, (Qualifier, Distribution)>;

/// A collection of dags
#[derive(Clone)]
pub struct Dags<C: ArkConfig, A>(Vec<Dag<C, A>>);
pub type UDags<C> = Dags<C, Nothing>;
pub type QDags<C> = Dags<C, Qualifier>;
pub type DQDags<C> = Dags<C, (Qualifier, Distribution)>;

#[derive(Error, PartialEq, Debug)]
pub enum GraphError {
    #[error("Variable not found {0}")]
    VarNotFound(Vid),
    #[error("Node not found: {0}")]
    NodeNotFound(usize),
    #[error("Relation not found in {0}")]
    RelationNotFound(Vid),
    #[error("Private node found in verifier: {0}: {1}")]
    PrivateNodeInVerifier(String, String),
    #[error("{0}\n\n{1}")]
    Next(Box<GraphError>, Box<GraphError>),
    #[error(transparent)]
    Type(Box<TypeError>),
    #[error("Fun expression contains non-polynomial operations: {0}")]
    NonPolynomialFun(String),
}

impl From<TypeError> for GraphError {
    fn from(e: TypeError) -> Self {
        GraphError::Type(Box::new(e))
    }
}

/// A trait for writing a graph to a PDF file
pub trait WritePdf {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()>;
}

impl GraphError {
    pub fn next(e1: GraphError, e2: GraphError) -> Self {
        GraphError::Next(Box::new(e1), Box::new(e2))
    }
    pub fn var_not_found(vid: &Vid) -> Self {
        GraphError::VarNotFound(vid.clone())
    }
    pub fn private_node_in_verifier<C: ArkConfig>(op: &GOp<C>, r: &Ref) -> Self {
        GraphError::PrivateNodeInVerifier(op.to_string(), r.to_string())
    }
    pub fn relation_not_found(vid: &Vid) -> Self {
        GraphError::RelationNotFound(vid.clone())
    }
    pub fn node_not_found(n: NodeIndex) -> Self {
        GraphError::NodeNotFound(n.index())
    }
}

/// Compare two `Node` values for isomorphism-compatible equality.
/// Erases `NodeIndex` inside `GOp` and `PRef` so that structurally
/// identical nodes from different graphs compare as equal.
fn nodes_isomorphic_eq<C: HasOpFactory, A: PartialEq + Clone>(
    a: &Node<C, A>,
    b: &Node<C, A>,
) -> bool {
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

impl<C: HasOpFactory, A: PartialEq + Clone> PartialEq for Dag<C, A> {
    fn eq(&self, other: &Self) -> bool {
        petgraph::algo::is_isomorphic_matching(
            &self.graph,
            &other.graph,
            |a, b| nodes_isomorphic_eq(a, b),
            |a, b| a == b,
        ) && self.vctx == other.vctx
            && self.transcript_vars == other.transcript_vars
    }
}

impl<C: ArkConfig, A> Default for Dag<C, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig, A> Dag<C, A> {
    pub fn new() -> Self {
        Dag {
            graph: Graph::new(),
            vctx: Ctx::new(),
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

    pub fn nodes_indices(&self) -> Vec<NodeIndex> {
        self.graph.node_indices().collect()
    }

    /// Get the number of edges in the graph
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    pub fn input_node(&self) -> NodeIndex {
        self.graph
            .node_indices()
            .find(|n| self.graph[*n].is_input())
            .expect("No input node found, DAG uninitialized")
    }

    pub fn relation_node(&self) -> Option<NodeIndex> {
        self.graph
            .node_indices()
            .find(|n| self.graph[*n].is_relation())
    }

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

    pub fn args(&self) -> Vec<PRef> {
        self.input_args()
            .into_iter()
            .filter_map(|n| self[n].arg_pref(n))
            .collect()
    }

    pub fn relation_args_prefs(&self) -> Vec<PRef> {
        self.relation_args()
            .into_iter()
            .filter_map(|n| self[n].arg_pref(n))
            .collect()
    }

    /// Dep deduplication
    pub(crate) fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Dep) {
        // If the edge is not a self-loop add it
        if source != sink {
            self.graph.add_edge(source, sink, edge);
        }
    }

    pub(crate) fn add_edges(&mut self, edge_type: DepType, sink: NodeIndex, source: GOp<C>) {
        source.references().into_iter().for_each(|refer| {
            self.add_edge(refer.node(), sink, Dep(edge_type));
        });
    }

    /// Returns the reachable nodes (transitive, reflexive closure) from [n] in [direction]
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

    /// Add a node to the graph (no deduplication)
    pub fn add_node(&mut self, node: Node<C, A>) -> NodeIndex {
        self.graph.add_node(node)
    }

    pub fn get_node(&mut self, it: NodeIndex) -> &mut Node<C, A> {
        &mut self.graph[it]
    }

    /// Find the variable name for a node via vctx (let/transcript bindings)
    /// or by reading the name off `Node::Arg`/`Node::Inp`/`Node::Rel` markers.
    pub fn find_var(&self, node: NodeIndex) -> Option<Vid> {
        if let Some(v) = self.vctx.get(&node).cloned() {
            return Some(v);
        }
        self[node].name().cloned()
    }

    pub fn find_ref(&self, node: NodeIndex) -> Ref {
        Ref(node)
    }

    pub fn node_indices(&self) -> NodeIndices {
        self.graph.node_indices()
    }

    /// Get reference to internal graph (for testing)
    #[cfg(test)]
    pub(crate) fn inner_graph(&self) -> &Graph<Node<C, A>, Dep> {
        &self.graph
    }

    pub fn max_node(&self) -> NodeIndex {
        self.graph.node_indices().next_back().unwrap()
    }

    pub fn name(&self) -> Vid {
        let inp = self.input_node();
        self[inp].name().unwrap().clone()
    }

    /// Annotate the graph using function [f]
    pub fn map_annotations<B, F: Fn(&GOp<C>, &A) -> B>(&self, f: &F) -> Dag<C, B> {
        Dag {
            graph: self.graph.map(
                |_, node| match node {
                    Node::Op(op, ann) => Node::Op(op.clone(), f(op, ann)),
                    Node::Transcr(op, ann) => Node::Transcr(op.clone(), f(op, ann)),
                    Node::Inp(a) => Node::Inp(a.clone()),
                    Node::Rel(a) => Node::Rel(a.clone()),
                    Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
                },
                |_, e| *e,
            ),
            vctx: self.vctx.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    pub fn neighbors_directed(
        &self,
        node_index: NodeIndex,
        direction: Direction,
    ) -> Neighbors<'_, Dep, u32> {
        self.graph.neighbors_directed(node_index, direction)
    }

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

    /// Get all verifier assertions, check nodes with no outgoing edges
    pub fn find_check(&self) -> Vec<NodeIndex> {
        self.node_indices()
            .filter(|&n| match &self[n] {
                Node::Op(op, _) | Node::Transcr(op, _) => {
                    matches!(&**op, Op::Check(_)) && self.nodes_from(n).count() == 0
                }
                _ => false,
            })
            .collect()
    }

    pub fn nodes_from(&self, n: NodeIndex) -> Neighbors<'_, Dep, u32> {
        self.graph.neighbors_directed(n, Direction::Outgoing)
    }

    pub fn nodes_to(&self, n: NodeIndex) -> Neighbors<'_, Dep, u32> {
        self.graph.neighbors_directed(n, Direction::Incoming)
    }

    pub fn erase_ann(self) -> UDag<C> {
        Dag {
            graph: self.graph.map(
                |_, node| match node {
                    Node::Inp(a) => Node::Inp(a.clone()),
                    Node::Rel(a) => Node::Rel(a.clone()),
                    Node::Arg(v, t, q, d, k) => Node::Arg(v.clone(), t.clone(), *q, *d, *k),
                    Node::Op(op, _) => Node::Op(op.clone(), Nothing),
                    Node::Transcr(op, _) => Node::Transcr(op.clone(), Nothing),
                },
                |_, e| *e,
            ),
            vctx: self.vctx.clone(),
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

        // Merge vctx and transcript_vars from both DAGs with remapped keys
        let mut merged_vctx = Ctx::new();
        for (k, v) in self.vctx.iter() {
            if let Some(new_k) = node_map_self.get(k) {
                merged_vctx.insert(new_k, v);
            }
        }
        for (k, v) in other.vctx.iter() {
            if let Some(new_k) = node_map_other.get(k) {
                merged_vctx.insert(new_k, v);
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
            vctx: merged_vctx,
            transcript_vars: merged_transcript,
        }
    }
}

/// Methods requiring hash-consing (HasOpFactory)
impl<C: HasOpFactory, A> Dag<C, A> {
    pub fn map_node_indices<F: Fn(NodeIndex) -> NodeIndex>(&self, f: &F) -> Dag<C, A>
    where
        A: Clone,
    {
        Dag {
            graph: self
                .graph
                .map(|_, node| node.map_node_indices(f), |_, e| *e),
            vctx: self.vctx.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    /// Get the prover graph, by reachability analysis starting from the transcript nodes
    pub fn get_prover(&self) -> (Dag<C, A>, HashMap<NodeIndex, Ref>)
    where
        A: Clone,
    {
        let mut prover = Dag::new();
        // Add all nodes to the prover graph
        let mut worklist: Vec<NodeIndex> = self.transcript_nodes();
        // Map old node indices to new references
        let mut node_map: HashMap<NodeIndex, Ref> = HashMap::new();

        // Add input node first, so it is NodeIndex::new(0)
        let n_input = prover.add_node(self[self.input_node()].clone());
        node_map.insert(self.input_node(), Ref(n_input));
        // Replicate input Arg nodes (so the projected dag has the same arg structure).
        for arg_idx in self.input_args() {
            let new_arg = prover.add_node(self[arg_idx].clone());
            prover.add_edge(n_input, new_arg, Dep::data());
            node_map.insert(arg_idx, Ref(new_arg));
        }

        while let Some(n) = worklist.pop() {
            if node_map.contains_key(&n) {
                continue;
            }
            // Add node to prover graph
            let new_node = prover.add_node(self[n].clone());
            node_map.insert(n, Ref(new_node));

            // Add previous neighbors to worklist
            for e in self.graph.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                worklist.push(e.source());
            }
        }

        // Propagate vctx and transcript_vars for mapped nodes
        for (old_idx, new_ref) in &node_map {
            if let Some(vid) = self.vctx.get(old_idx) {
                prover.vctx.insert(&new_ref.node(), vid);
            }
            if let Some(is_transcript) = self.transcript_vars.get(old_idx) {
                prover
                    .transcript_vars
                    .insert(&new_ref.node(), is_transcript);
            }
        }

        // Add edges to prover graph using the mapped node indices
        let source_input_node = self.input_node();
        for edge_ref in self.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if old_source_idx == source_input_node && self[old_target_idx].is_input_arg() {
                continue;
            }

            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map.get(&old_source_idx), node_map.get(&old_target_idx))
            {
                prover.add_edge(new_source_idx.node(), new_target_idx.node(), weight);
            }
        }

        // Remap node indices in Ref to the new node indices
        let remapped = prover.map_node_indices(&|n| {
            node_map.get(&n).map(|r| r.node()).unwrap_or_else(|| {
                panic!(
                    "Aliasing error: node {}: {} in prover not found in {} protocol dag",
                    n.index(),
                    self[n].drop_annotation(),
                    self.name()
                )
            })
        });

        (remapped, node_map)
    }

    /// Get the relation graph, by reachability analysis starting from the relation node
    pub fn get_relation(&self) -> Result<Dag<C, A>, GraphError>
    where
        A: Clone,
    {
        let mut g_relation = Dag::new();
        let relation_node = self
            .relation_node()
            .ok_or(GraphError::RelationNotFound(self.name()))?;

        let mut worklist = vec![relation_node];
        let mut node_map_rel = HashMap::<NodeIndex, NodeIndex>::new();

        while let Some(n) = worklist.pop() {
            if node_map_rel.contains_key(&n) {
                continue;
            }
            let new_node = g_relation.add_node(self[n].clone());
            node_map_rel.insert(n, new_node);
            for e in self.graph.edges_directed(n, Direction::Outgoing) {
                worklist.push(e.target());
            }
        }

        // Add edges to relation graph using the mapped node indices
        for edge_ref in self.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if let (Some(new_source_idx), Some(new_target_idx)) = (
                node_map_rel.get(&old_source_idx),
                node_map_rel.get(&old_target_idx),
            ) {
                g_relation.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }
        Ok(g_relation.map_node_indices(&|n| node_map_rel[&n]))
    }

    pub fn rename_inner_nodes(&mut self) -> Dag<C, A>
    where
        A: Clone,
    {
        // Phase B: Ref carries only NodeIndex; arg names live on Arg nodes
        // and let-binding names live in `vctx`. Renaming inner refs is now
        // a no-op (the structural change in Phase B already disambiguates
        // them by NodeIndex), but we still mangle vctx entries for non-arg
        // bindings to keep PDF labels unique across compositions.
        let arg_names: Vec<String> = self
            .input_args()
            .iter()
            .filter_map(|n| self[*n].name().map(|v| v.0.clone()))
            .collect();
        let mut result = self.clone();
        let mut new_vctx = Ctx::new();
        for (k, v) in result.vctx.iter() {
            if arg_names.contains(&v.0) {
                new_vctx.insert(k, v);
            } else {
                new_vctx.insert(k, &Vid(v.0.clone() + &format!("_{:?}", k)));
            }
        }
        result.vctx = new_vctx;
        result
    }

    pub fn map_ops<F: Fn(&GOp<C>) -> GOp<C>>(&mut self, f: &F) -> Dag<C, A>
    where
        A: Clone,
    {
        Dag {
            graph: self.graph.map(
                |_, node| match node {
                    Node::Op(op, ann) => Node::Op(mk::<C>(f(op)), ann.clone()),
                    Node::Transcr(op, ann) => Node::Transcr(mk::<C>(f(op)), ann.clone()),
                    _ => node.clone(),
                },
                |_, e| *e,
            ),
            vctx: self.vctx.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    /// Get the verifier graph, by reachability analysis starting from the verifier assertion
    /// and stopping at transcript nodes.
    pub fn get_verifier(&self) -> Result<Dag<C, A>, GraphError>
    where
        A: Clone,
    {
        let mut verifier = Dag::new();

        // Public inputs that survive into the verifier (with their source-dag NodeIndex).
        let public_args: Vec<(NodeIndex, PRef)> = self
            .input_args()
            .into_iter()
            .filter_map(|n| {
                let pref = self[n].arg_pref(n)?;
                if pref.is_public() {
                    Some((n, pref))
                } else {
                    None
                }
            })
            .collect();
        let name = self.name();

        // Associate old node indices with new node indices
        let mut node_map_self = HashMap::<NodeIndex, NodeIndex>::new();

        // Make new input node + replicate public Args.
        let n_input = verifier.add_node(Node::Inp(name));
        node_map_self.insert(self.input_node(), n_input);

        for (old_arg_idx, _) in &public_args {
            let new_arg = verifier.add_node(self[*old_arg_idx].clone());
            verifier.add_edge(n_input, new_arg, Dep::data());
            node_map_self.insert(*old_arg_idx, new_arg);
        }

        let mut non_challenge_transcripts: HashSet<NodeIndex> = HashSet::new();

        // Add transcript nodes to verifier graph (source ops are kept as-is;
        // they will be rewritten *after* `map_node_indices` so verifier-local
        // indices are not subject to remapping).
        for &n_transcr in &self.transcript_nodes() {
            let node = &self[n_transcr];
            if node.is_challenge() {
                let new_node = verifier.add_node(node.clone());
                node_map_self.insert(n_transcr, new_node);
                continue;
            }
            non_challenge_transcripts.insert(n_transcr);
            let new_idx = verifier.add_node(node.clone());
            node_map_self.insert(n_transcr, new_idx);
        }

        // Add the verifier nodes, start with the verifier assertions
        let mut worklist = self.find_check();
        assert!(!worklist.is_empty(), "No verifier assertion found");

        while let Some(n) = worklist.pop() {
            if node_map_self.contains_key(&n) {
                continue;
            } else if !self[n].is_op() || self[n].is_transcript() {
                // Only op nodes are added to the verifier, transcript nodes are already added to the prover
                continue;
            }

            // Check if the node refers to a private argument, then it is a leak
            let op = self[n].clone().into_op();
            for r in op.references() {
                let target = r.node();
                if self[target].is_input_arg() {
                    let is_private_input = self[target]
                        .arg_pref(target)
                        .map(|pr| pr.is_private())
                        .unwrap_or(false);
                    if is_private_input {
                        return Err(GraphError::private_node_in_verifier(&op, &r));
                    }
                }
            }

            // Add node to verifier graph
            let new_node = verifier.add_node(self[n].clone());
            node_map_self.insert(n, new_node);

            // Add parent neighbors to worklist
            for e in self.graph.edges_directed(n, Direction::Incoming) {
                if !node_map_self.contains_key(&e.source()) {
                    debug!(
                        "Adding parent {} of {} to worklist",
                        self[e.source()].drop_annotation(),
                        self[n].drop_annotation()
                    );
                    worklist.push(e.source());
                }
            }
        }

        // Add edges to verifier graph using the mapped node indices
        let source_input_node = self.input_node();
        for edge_ref in self.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if old_source_idx == source_input_node && self[old_target_idx].is_input_arg() {
                continue;
            }

            if let Some(new_node) = node_map_self.get(&old_target_idx) {
                if verifier[*new_node].is_input() {
                    continue;
                }
                if non_challenge_transcripts.contains(&old_target_idx)
                    && edge_ref.weight().is_data()
                {
                    continue;
                }
            }
            if let (Some(new_source_idx), Some(new_target_idx)) = (
                node_map_self.get(&old_source_idx),
                node_map_self.get(&old_target_idx),
            ) {
                verifier.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }

        // Translate all source-local node indices in cloned ops to verifier-local indices.
        let mut verifier =
            verifier.map_node_indices(&|n| node_map_self.get(&n).copied().unwrap_or(n));

        // Now that map_node_indices is done, materialise verifier-local
        // Arg nodes for transcript proof values and rewrite each
        // non-challenge Transcr op to reference its Arg. These freshly
        // allocated indices will not be re-mapped.
        let mut transcript_arg_nodes: HashMap<Vid, NodeIndex> = HashMap::new();
        // Snapshot the transcript nodes we added (now at their verifier-local indices).
        // Iterate in source-graph transcript order so that the verifier's
        // transcript Arg nodes are created in the same order the prover
        // emits proof values.
        let transcr_pairs: Vec<(NodeIndex, Vid)> = self
            .transcript_nodes()
            .iter()
            .filter(|src| non_challenge_transcripts.contains(src))
            .filter_map(|src| {
                let new_idx = node_map_self.get(src).copied()?;
                let v = self.find_var(*src)?;
                Some((new_idx, v))
            })
            .collect();

        for (new_idx, transcript_var) in transcr_pairs {
            // Determine/create the Arg node for this transcript var.
            let arg_node = if let Some(&n) = transcript_arg_nodes.get(&transcript_var) {
                n
            } else if let Some((old, _)) = public_args
                .iter()
                .find(|(_, pr)| pr.name() == Some(&transcript_var))
            {
                node_map_self[old]
            } else {
                let typ = match &verifier[new_idx] {
                    Node::Transcr(op, _) => op.typ(),
                    _ => unreachable!("non-challenge transcript must be Transcr"),
                };
                let arg_node = verifier.add_node(Node::Arg(
                    transcript_var.clone(),
                    typ,
                    Qualifier::Public,
                    Distribution::default(),
                    ArgKind::TranscriptInput,
                ));
                verifier.add_edge(n_input, arg_node, Dep::data());
                transcript_arg_nodes.insert(transcript_var.clone(), arg_node);
                arg_node
            };

            // Rewrite Transcr op to reference the Arg, and add the data edge.
            if let Node::Transcr(op, _) = &mut verifier[new_idx] {
                let typ = op.typ();
                *op = mk::<C>(GOp::var(&transcript_var, arg_node, typ));
            }
            verifier.add_edge(arg_node, new_idx, Dep::data());
        }

        Ok(verifier)
    }
}

/// Write graphs with string annotations to PDF
impl<C: ArkConfig> WritePdf for Dag<C, String> {
    /// Write graph to PDF
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        let fdot: String = format!("{filename}.dot");
        // Remove old file if there
        std::fs::remove_file(&fdot).ok();

        // Create graphviz object
        let graphviz = Dot::with_attr_getters(
            &self.graph,
            &[],
            &|_, e| {
                match e.weight().0 {
                    DepType::Data => "color = \"black\"",
                    DepType::Transcript => "color = \"red\"",
                }
                .to_string()
            },
            &|_, n| match n.1 {
                Node::Inp(_) => "shape = \"box\"".to_string(),
                Node::Rel(_) => "shape = \"note\"".to_string(),
                Node::Arg(_, _, _, _, _) => "shape = \"parallelogram\"".to_string(),
                Node::Transcr(_, _) => "color = \"red\"".to_string(),
                _ => "shape = \"ellipse\"".to_string(),
            },
        );

        // Write to file
        std::fs::write(fdot.clone(), graphviz.to_string())?;

        let fpdf: String = format!("{filename}.pdf");

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(fdot.clone())
            .arg("-o")
            .arg(fpdf.clone())
            .spawn()?
            .wait()?;

        // Remove DOT file
        // std::fs::remove_file(fdot)?;

        debug!("Wrote PDF to {:?}", fpdf);
        // Print success
        debug!(
            "Wrote {:?}",
            std::fs::canonicalize(PathBuf::from(fpdf.clone()))
        );
        Ok(())
    }
}

impl<C: ArkConfig> WritePdf for UDag<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, _| "".to_string())
            .write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for QDag<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, q| q.to_string())
            .write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for DQDag<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, (q, d)| format!("{} {}", q, d))
            .write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for Dags<C, String> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        let mut joined_graph = Dag::new();
        for g in self.0.iter() {
            joined_graph = joined_graph.combine_dag(g);
        }
        joined_graph.write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for UDags<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, _| "".to_string())
            .write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for QDags<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, q| q.to_string())
            .write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for DQDags<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, (q, d)| format!("{} {}", q, d))
            .write_pdf(filename)
    }
}

/// A collection of DAGs
impl<C: ArkConfig, A> Default for Dags<C, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ArkConfig, A> Dags<C, A> {
    pub fn new() -> Self {
        Dags(Vec::new())
    }

    pub fn pop(&mut self) -> Option<Dag<C, A>> {
        self.0.pop()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn get_proto(&self, name: &String) -> Option<&Dag<C, A>> {
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

    pub fn functions(&self) -> Vec<&Dag<C, A>> {
        self.0
            .iter()
            .filter(|g| g.relation_node().is_none())
            .collect()
    }

    /// Annotate all graphs using function [f]
    pub fn map_annotations<B, F: Fn(&GOp<C>, &A) -> B>(&self, f: &F) -> Dags<C, B> {
        Dags(self.0.iter().map(|g| g.map_annotations(f)).collect())
    }
}

/// A collection of DAGs without annotations
impl<C: HasOpFactory> UDags<C> {
    /// Create a collection of Dags from a module
    pub fn from_module(m: CModule) -> Result<Self, GraphError> {
        let mut gs = UDags::new();

        let fctx = m
            .iter()
            .map(|(sig, body)| (sig.clone(), body.clone()))
            .collect::<Ctx<CSig, CBody>>();

        debug!("fctx: {}", fctx);
        for (sig, body) in m.into_iter() {
            debug!("Adding declaration: {}", sig);
            let mut g = UDag::new();
            g.add_decl(sig.clone(), body.clone(), &fctx)?;
            gs.0.push(g);
        }
        Ok(gs)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BooleanHypercubeProvenance {
    tail_num_vars: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScalarConstProvenance {
    Zero,
    One,
}

#[derive(Clone, Debug, Default)]
struct LoweringProvenance {
    boolean_hypercube_tails: Ctx<Vid, BooleanHypercubeProvenance>,
    scalar_consts: Ctx<Vid, ScalarConstProvenance>,
}

impl LoweringProvenance {
    fn new() -> Self {
        Self {
            boolean_hypercube_tails: Ctx::new(),
            scalar_consts: Ctx::new(),
        }
    }

    fn remove_binding(&mut self, id: &Vid) {
        self.boolean_hypercube_tails.remove(id);
        self.scalar_consts.remove(id);
    }

    fn shadow_binding(&self, id: &Vid) -> Self {
        let mut next = self.clone();
        next.remove_binding(id);
        next
    }
}

/// Constructors for graphs
impl<C: HasOpFactory> UDag<C> {
    /// Materialize an operation into the DAG.
    ///
    /// If `op` is already `Op::Ref` or `Op::Value`, it is returned as-is.
    /// Otherwise, a new DAG node is created for `op`, edges are added from
    /// that node to all `Op::Ref` children of `op`, and an `Op::Ref` to
    /// the new node is returned.
    ///
    /// This is the primary mechanism for enforcing `add_exp`'s invariant
    /// that its return value is always `Op::Ref` or `Op::Value`.
    fn materialize(&mut self, op: GOp<C>, edge_type: DepType, atyp: ATyp) -> GOp<C> {
        match &op {
            Op::Ref(_, _) | Op::Value(_) => op,
            _ => {
                let node = self.add_node(Node::Op(mk::<C>(op.clone()), Nothing));
                self.add_edges(edge_type, node, op);
                GOp::underscore(node, atyp)
            }
        }
    }

    /// Add a new top-level expression to the graph
    fn add_top_exp(
        &mut self,
        exp: CExp,
        start: &mut NodeIndex,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
    ) -> Result<(), GraphError> {
        debug!("Adding top-level expression: {:?}", exp);
        let op = self.add_exp(exp, start, DepType::Data, kctx, fctx, vctx, vars)?;
        if !op.is_ref() {
            let nr = self.add_node(Node::ret(&op));
            self.add_edges(DepType::Data, nr, op);
        };
        Ok(())
    }

    /// Add a new declaration to the graph
    fn add_decl(
        &mut self,
        sig: CSig,
        body: CBody,
        fctx: &Ctx<CSig, CBody>,
    ) -> Result<(), GraphError> {
        // Kind context
        let kctx = sig.typevars.to_ctx();
        // Add arguments to [vctx] and [vars]
        let mut vctx = Ctx::new();

        // Cast the signature to a arguments and insert to [start] node
        let asig = sig
            .args
            .iter()
            .map(|arg| {
                PRef::from_arg(arg, NodeIndex::new(0), &kctx).ok_or_else(|| {
                    TypeError::decl(
                        &sig.name,
                        TypeError::ark(&kctx, &vctx, &CExp::var(&arg.id), &arg.typ),
                    )
                })
            })
            .collect::<Result<Vec<PRef>, _>>()?;

        // Add arguments to type and fft contexts
        let mut atyps = Ctx::new();
        for Arg { id, typ, .. } in sig.args.iter() {
            let at = ATyp::from_ctyp(typ, &kctx).ok_or_else(|| {
                TypeError::decl(&sig.name, TypeError::ark(&kctx, &vctx, &CExp::var(id), typ))
            })?;
            atyps.insert(id, &at);
            vctx.insert(id, typ);
        }
        // Expose singleton range typevars (e.g. N: 4) as term-level constants.
        for (tid, kind) in kctx.iter() {
            if let CKind::Range(r) = kind
                && r.step == 1
                && r.end == r.start + 1
            {
                vctx.insert(&Vid::new(&tid.0), &CTyp::Fin(*r));
            }
        }

        // Typecheck the body with the type signature
        body.typecheck(sig.clone(), &fctx.keys())?;

        // Add the body to the Graph
        match body {
            CBody::Proto { body, relation } => {
                debug!("Adding proto: {:?}", sig);
                // Start node (input marker)
                let mut start = self.add_node(Node::inp(sig.name.clone()));
                let mut vars: Ctx<Vid, GOp<C>> = Ctx::new();
                for (id, typ) in atyps.iter() {
                    let pref = asig
                        .iter()
                        .find(|p| p.name() == Some(id))
                        .cloned()
                        .expect("PRef built from sig must be present");
                    let arg_node = self.add_node(Node::arg(
                        id.clone(),
                        typ.clone(),
                        pref.qualifier,
                        pref.distribution,
                        ArgKind::Input,
                    ));
                    self.graph.add_edge(start, arg_node, Dep::data());
                    vars.insert(id, &GOp::var(id, arg_node, typ.clone()));
                }
                for (tid, kind) in kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step == 1
                        && r.end == r.start + 1
                    {
                        let vid = Vid::new(&tid.0);
                        vars.insert(&vid, &GOp::Value(Value::Index(r.start)));
                    }
                }
                self.add_top_exp(body, &mut start, &kctx, fctx, &vctx, &vars)?;
                // Relation start: its own per-arg `Node::Arg` children so
                // walking the relation does not pull in the protocol body
                // through shared `Arg` nodes.
                start = self.add_node(Node::rel(sig.name.clone()));
                let mut vars: Ctx<Vid, GOp<C>> = Ctx::new();
                for (id, typ) in atyps.iter() {
                    let pref = asig
                        .iter()
                        .find(|p| p.name() == Some(id))
                        .cloned()
                        .expect("PRef built from sig must be present");
                    let arg_node = self.add_node(Node::arg(
                        id.clone(),
                        typ.clone(),
                        pref.qualifier,
                        pref.distribution,
                        ArgKind::Relation,
                    ));
                    self.graph.add_edge(start, arg_node, Dep::data());
                    vars.insert(id, &GOp::var(id, arg_node, typ.clone()));
                }
                for (tid, kind) in kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step == 1
                        && r.end == r.start + 1
                    {
                        let vid = Vid::new(&tid.0);
                        vars.insert(&vid, &GOp::Value(Value::Index(r.start)));
                    }
                }
                self.add_top_exp(relation, &mut start, &kctx, fctx, &vctx, &vars)?;
            }
            CBody::Func { body } => {
                let mut start = self.add_node(Node::inp(sig.name.clone()));
                let mut vars: Ctx<Vid, GOp<C>> = Ctx::new();
                for (id, typ) in atyps.iter() {
                    let pref = asig
                        .iter()
                        .find(|p| p.name() == Some(id))
                        .cloned()
                        .expect("PRef built from sig must be present");
                    let arg_node = self.add_node(Node::arg(
                        id.clone(),
                        typ.clone(),
                        pref.qualifier,
                        pref.distribution,
                        ArgKind::Input,
                    ));
                    self.graph.add_edge(start, arg_node, Dep::data());
                    vars.insert(id, &GOp::var(id, arg_node, typ.clone()));
                }
                for (tid, kind) in kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step == 1
                        && r.end == r.start + 1
                    {
                        let vid = Vid::new(&tid.0);
                        vars.insert(&vid, &GOp::Value(Value::Index(r.start)));
                    }
                }
                self.add_top_exp(body, &mut start, &kctx, fctx, &vctx, &vars)?;
            }
            CBody::TypeAlias => {
                // Type aliases are expanded inline during module parsing,
                // no graph nodes needed.
            }
        }

        Ok(())
    }

    /// Variables to operations by lookup in [vars]
    fn op_from_var(id: &Vid, vars: &Ctx<Vid, GOp<C>>) -> Result<GOp<C>, GraphError> {
        vars.get(id)
            .cloned()
            .ok_or_else(|| GraphError::var_not_found(id))
    }

    /// Convert a Fun expression body to a PolyVariant
    /// Only polynomial operations (Add, Sub, Mul with scalars, Var, Lit) are allowed
    fn exp_to_poly_variant(
        exp: &CExp,
        vars: &[Vid],
        var_map: &HashMap<Vid, usize>,
    ) -> Result<PolyVariant<C::F>, GraphError> {
        use ark_ff::{One, Zero};

        match exp {
            CExp::Lit(n) => {
                // Scalar constant
                let scalar = C::F::from(*n as u64);
                Ok(PolyVariant::from_scalar(scalar))
            }
            CExp::Var(vid) => {
                // Check if this is a bound variable
                if let Some(&var_idx) = var_map.get(vid) {
                    // Create a polynomial with variable
                    if vars.len() == 1 {
                        // Univariate: create polynomial [0, 1] representing x
                        let poly =
                            DensePolynomial::from_coefficients_vec(vec![C::F::zero(), C::F::one()]);
                        Ok(PolyVariant::DenseUni(poly))
                    } else {
                        // Multilinear: create a basis polynomial
                        let num_vars = vars.len();
                        let mut evals = vec![C::F::zero(); 1 << num_vars];
                        // Set evaluation at the point corresponding to this variable
                        for (i, e) in evals.iter_mut().enumerate().take(1 << num_vars) {
                            if (i >> var_idx) & 1 == 1 {
                                *e = C::F::one();
                            }
                        }
                        let mle = DenseMultilinearExtension::from_evaluations_vec(num_vars, evals);
                        Ok(PolyVariant::DenseMle(mle))
                    }
                } else {
                    Err(GraphError::NonPolynomialFun(format!(
                        "Unbound variable {} in Fun expression",
                        vid
                    )))
                }
            }
            CExp::Bin(BinOp::Add, box a, box b) => {
                let pa = Self::exp_to_poly_variant(a, vars, var_map)?;
                let pb = Self::exp_to_poly_variant(b, vars, var_map)?;
                pa.poly_add(&pb)
                    .map_err(|e| GraphError::NonPolynomialFun(format!("Add failed: {}", e)))
            }
            CExp::Bin(BinOp::Sub, box a, box b) => {
                let pa = Self::exp_to_poly_variant(a, vars, var_map)?;
                let pb = Self::exp_to_poly_variant(b, vars, var_map)?;
                pa.poly_sub(&pb)
                    .map_err(|e| GraphError::NonPolynomialFun(format!("Sub failed: {}", e)))
            }
            CExp::Bin(BinOp::Mul, box a, box b) => {
                let pa = Self::exp_to_poly_variant(a, vars, var_map)?;
                let pb = Self::exp_to_poly_variant(b, vars, var_map)?;
                pa.poly_mul(&pb)
                    .map_err(|e| GraphError::NonPolynomialFun(format!("Mul failed: {}", e)))
            }
            _ => Err(GraphError::NonPolynomialFun(format!(
                "Unsupported operation in Fun expression: {:?}",
                exp
            ))),
        }
    }

    /// Lower a Map/ReduceMap body to an inline `GOp` op-tree (no graph nodes).
    /// `binders` are the enclosing loop binders by de Bruijn level (index =
    /// level); `vctx` is already extended with their CTyps. `Ok(None)` means
    /// the template declines and the caller falls back to the unroll lowerer.
    #[allow(clippy::too_many_arguments)]
    fn lower_loop_body_template(
        &mut self,
        exp: &CExp,
        binders: &[(Vid, ATyp)],
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        provenance: &LoweringProvenance,
    ) -> Result<Option<GOp<C>>, GraphError> {
        match exp {
            CExp::Lit(n) => Ok(Some(GOp::Value(Value::Index(*n)))),
            CExp::Bool(b) => Ok(Some(GOp::Value(Value::Bool(*b)))),
            CExp::Range(r) => Ok(Some(GOp::range(*r))),
            CExp::Var(id) => {
                if let Some(level) = binders.iter().rposition(|(v, _)| v == id) {
                    Ok(Some(GOp::loop_param(level, binders[level].1.clone())))
                } else {
                    Ok(Some(Self::op_from_var(id, vars)?))
                }
            }
            CExp::Bin(op, a, b) => {
                let Some(la) =
                    self.lower_loop_body_template(a, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                let Some(lb) =
                    self.lower_loop_body_template(b, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                let ctyp = exp.infer(kctx, &fctx.keys(), vctx)?;
                let Some(atyp) = ATyp::from_ctyp(&ctyp, kctx) else {
                    return Ok(None);
                };
                Ok(Some(GOp::bin(*op, la, lb, atyp)))
            }
            CExp::Ram(a, b) => {
                let Some(la) =
                    self.lower_loop_body_template(a, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                let Some(lb) =
                    self.lower_loop_body_template(b, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                Ok(Some(GOp::ram(la, lb)))
            }
            CExp::Vec(xs) => {
                let mut out = Vec::with_capacity(xs.0.len());
                for e in xs.0.iter() {
                    let Some(le) = self
                        .lower_loop_body_template(e, binders, kctx, fctx, vctx, vars, provenance)?
                    else {
                        return Ok(None);
                    };
                    out.push(le);
                }
                Ok(Some(GOp::vec(out)))
            }
            CExp::Evaluate(p, selector, opt_points) => {
                let Some(lp) =
                    self.lower_loop_body_template(p, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                match (selector, opt_points) {
                    (None, None) => Ok(Some(GOp::evaluate_grid(lp))),
                    (None, Some(x)) => {
                        let Some(lx) = self.lower_loop_body_template(
                            x, binders, kctx, fctx, vctx, vars, provenance,
                        )?
                        else {
                            return Ok(None);
                        };
                        Ok(Some(GOp::evaluate(lp, lx)))
                    }
                    (Some(range), Some(fixed)) => {
                        let Some(lfixed) = self.lower_loop_body_template(
                            fixed, binders, kctx, fctx, vctx, vars, provenance,
                        )?
                        else {
                            return Ok(None);
                        };
                        Ok(Some(GOp::evaluate_selected(lp, *range, lfixed)))
                    }
                    (Some(_), None) => Ok(None),
                }
            }
            CExp::Poly(p) => {
                let Some(lp) =
                    self.lower_loop_body_template(p, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                Ok(Some(Op::Poly(mk::<C>(lp))))
            }
            CExp::Coef(p) => {
                let Some(lp) =
                    self.lower_loop_body_template(p, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                Ok(Some(Op::Coef(mk::<C>(lp))))
            }
            CExp::Mle(p) => {
                let Some(lp) =
                    self.lower_loop_body_template(p, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                Ok(Some(Op::Mle(mk::<C>(lp))))
            }
            CExp::Interpolate(points_opt, evals) => {
                let Some(levals) = self
                    .lower_loop_body_template(evals, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                match points_opt {
                    None => Ok(Some(Op::Ifft(mk::<C>(levals)))),
                    Some(p) => {
                        let Some(lp) = self.lower_loop_body_template(
                            p, binders, kctx, fctx, vctx, vars, provenance,
                        )?
                        else {
                            return Ok(None);
                        };
                        Ok(Some(Op::Interpolate(mk::<C>(lp), mk::<C>(levals))))
                    }
                }
            }
            CExp::Proj(r, field) => {
                let Some(lr) =
                    self.lower_loop_body_template(r, binders, kctx, fctx, vctx, vars, provenance)?
                else {
                    return Ok(None);
                };
                let ctyp = exp.infer(kctx, &fctx.keys(), vctx)?;
                let Some(atyp) = ATyp::from_ctyp(&ctyp, kctx) else {
                    return Ok(None);
                };
                Ok(Some(Op::Proj(mk::<C>(lr), field.clone(), atyp)))
            }
            CExp::Record(fields) => {
                let mut out: Ctx<String, HOp<C>> = Ctx::new();
                for (k, v) in fields.iter() {
                    let Some(lv) = self
                        .lower_loop_body_template(v, binders, kctx, fctx, vctx, vars, provenance)?
                    else {
                        return Ok(None);
                    };
                    out.insert(k, &mk::<C>(lv));
                }
                Ok(Some(Op::Record(out)))
            }
            CExp::Map(body, binder, domain) => {
                let domain_typ = domain.infer(kctx, &fctx.keys(), vctx)?;
                let (elem_ctyp, _) = match domain_typ {
                    CTyp::Vec(box e, n) => (e, n),
                    _ => return Ok(None),
                };
                let Some(binder_atyp) = ATyp::from_ctyp(&elem_ctyp, kctx) else {
                    return Ok(None);
                };
                let Some(ld) = self.lower_loop_body_template(
                    domain, binders, kctx, fctx, vctx, vars, provenance,
                )?
                else {
                    return Ok(None);
                };
                let mut inner_binders = binders.to_vec();
                inner_binders.push((binder.clone(), binder_atyp));
                let mut inner_vctx = vctx.clone();
                inner_vctx.insert(binder, &elem_ctyp);
                let inner_prov = provenance.shadow_binding(binder);
                let Some(lb) = self.lower_loop_body_template(
                    body,
                    &inner_binders,
                    kctx,
                    fctx,
                    &inner_vctx,
                    vars,
                    &inner_prov,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(GOp::map(ld, lb)))
            }
            CExp::Reduce(rop, v) => {
                if let CExp::Map(body, binder, domain) = v.as_ref() {
                    self.try_build_reduce_map(
                        *rop,
                        body.as_ref().clone(),
                        binder.clone(),
                        domain.as_ref().clone(),
                        binders,
                        kctx,
                        fctx,
                        vctx,
                        vars,
                        provenance,
                    )
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    /// Capture-avoiding substitution of `replacement` for free `target` in
    /// `exp`. Handles pure value/arithmetic/polynomial forms precisely; any
    /// binder-introducing or effectful form is kept verbatim when it does not
    /// mention `target`, else declines (`None`) so composition stays safe.
    fn substitute_var(exp: CExp, target: &Vid, replacement: &CExp) -> Option<CExp> {
        Some(match exp {
            CExp::Var(id) => {
                if &id == target {
                    replacement.clone()
                } else {
                    CExp::Var(id)
                }
            }
            CExp::Lit(_)
            | CExp::Bool(_)
            | CExp::Range(_)
            | CExp::Random(_, _)
            | CExp::Challenge(_, _) => exp,
            CExp::Bin(op, a, b) => CExp::Bin(
                op,
                Box::new(Self::substitute_var(*a, target, replacement)?),
                Box::new(Self::substitute_var(*b, target, replacement)?),
            ),
            CExp::Ram(a, b) => CExp::Ram(
                Box::new(Self::substitute_var(*a, target, replacement)?),
                Box::new(Self::substitute_var(*b, target, replacement)?),
            ),
            CExp::Pair(a, b) => CExp::Pair(
                Box::new(Self::substitute_var(*a, target, replacement)?),
                Box::new(Self::substitute_var(*b, target, replacement)?),
            ),
            CExp::Vec(xs) => {
                let mut out = Vec::with_capacity(xs.0.len());
                for e in xs.0 {
                    out.push(Self::substitute_var(e, target, replacement)?);
                }
                CExp::vec(out)
            }
            CExp::Evaluate(p, sel, pts) => CExp::Evaluate(
                Box::new(Self::substitute_var(*p, target, replacement)?),
                sel,
                match pts {
                    Some(x) => Some(Box::new(Self::substitute_var(*x, target, replacement)?)),
                    None => None,
                },
            ),
            CExp::Poly(p) => CExp::Poly(Box::new(Self::substitute_var(*p, target, replacement)?)),
            CExp::Coef(p) => CExp::Coef(Box::new(Self::substitute_var(*p, target, replacement)?)),
            CExp::Mle(p) => CExp::Mle(Box::new(Self::substitute_var(*p, target, replacement)?)),
            CExp::Interpolate(pts, evals) => CExp::Interpolate(
                match pts {
                    Some(p) => Some(Box::new(Self::substitute_var(*p, target, replacement)?)),
                    None => None,
                },
                Box::new(Self::substitute_var(*evals, target, replacement)?),
            ),
            CExp::Proj(p, field) => CExp::Proj(
                Box::new(Self::substitute_var(*p, target, replacement)?),
                field,
            ),
            other => {
                if Self::exp_mentions_free_var(&other, target) {
                    return None;
                }
                other
            }
        })
    }

    /// Fuse `reduce(rop, [f(x) for x in [g(y) for y in D]])` into a single
    /// reduce-map over `D` with body `f(g(y))`, repeatedly while the inner
    /// comprehension and outer body are pure and substitution is capture-safe.
    /// Returns the maximally composed `(body, binder, domain)` (unchanged when
    /// no safe composition applies).
    fn compose_nested_map_domain(
        mut body: CExp,
        mut binder: Vid,
        mut domain: CExp,
    ) -> (CExp, Vid, CExp) {
        while let CExp::Map(g, y, d2) = domain.clone() {
            if !body.is_pure() || !g.is_pure() {
                break;
            }
            let Some(b2) = Self::substitute_var(body.clone(), &binder, g.as_ref()) else {
                break;
            };
            body = b2;
            binder = y;
            domain = *d2;
        }
        (body, binder, domain)
    }

    /// Classify whether `reduce(rop, [body for binder in domain])` is the
    /// canonical fused sumcheck shape. Mirrors the old
    /// `try_lower_hypercube_reduce_selected` recognizer exactly.
    #[allow(clippy::too_many_arguments)]
    fn classify_reduce_map_fact(
        rop: BinOp,
        body: &CExp,
        binder: &Vid,
        domain: &CExp,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        provenance: &LoweringProvenance,
    ) -> Result<ReduceMapDomainFact, GraphError> {
        if rop != BinOp::Add {
            return Ok(ReduceMapDomainFact::Unknown);
        }
        let CExp::Evaluate(poly, Some(range), Some(fixed)) = body else {
            return Ok(ReduceMapDomainFact::Unknown);
        };
        let CExp::Var(fv) = fixed.as_ref() else {
            return Ok(ReduceMapDomainFact::Unknown);
        };
        if fv != binder || range.start != 0 || range.step != 1 || range.len() != 1 {
            return Ok(ReduceMapDomainFact::Unknown);
        }
        if Self::exp_mentions_free_var(poly, binder) {
            return Ok(ReduceMapDomainFact::Unknown);
        }
        if !Self::is_poly_hoist_safe(poly) {
            return Ok(ReduceMapDomainFact::Unknown);
        }
        let poly_typ = poly.infer(kctx, &fctx.keys(), vctx)?;
        let Some(poly_atyp) = ATyp::from_ctyp(&poly_typ, kctx) else {
            return Ok(ReduceMapDomainFact::Unknown);
        };
        let arity = match poly_atyp {
            ATyp::Uni(_) => 1,
            ATyp::Mle(n) | ATyp::VPoly(n, _) => n,
            _ => return Ok(ReduceMapDomainFact::Unknown),
        };
        let Some(tail_num_vars) = arity.checked_sub(range.len()) else {
            return Ok(ReduceMapDomainFact::Unknown);
        };
        if !Self::is_boolean_hypercube_tail_domain(domain, tail_num_vars, provenance) {
            return Ok(ReduceMapDomainFact::Unknown);
        }
        Ok(ReduceMapDomainFact::CompleteBooleanHypercube { tail_num_vars })
    }

    /// Build an inline `Op::ReduceMap` for `reduce(rop, [body for binder in
    /// domain])`. Classifies the fast-path fact on the un-composed form, fuses
    /// nested-map domains for the generic case, then lowers domain and body via
    /// the template. Declines (`None`) if any sub-lowering declines.
    #[allow(clippy::too_many_arguments)]
    fn try_build_reduce_map(
        &mut self,
        rop: BinOp,
        body: CExp,
        binder: Vid,
        domain: CExp,
        binders: &[(Vid, ATyp)],
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        provenance: &LoweringProvenance,
    ) -> Result<Option<GOp<C>>, GraphError> {
        let fact = Self::classify_reduce_map_fact(
            rop, &body, &binder, &domain, kctx, fctx, vctx, provenance,
        )?;
        let (body, binder, domain) = match fact {
            ReduceMapDomainFact::Unknown => Self::compose_nested_map_domain(body, binder, domain),
            ReduceMapDomainFact::CompleteBooleanHypercube { .. } => (body, binder, domain),
        };
        let domain_typ = domain.infer(kctx, &fctx.keys(), vctx)?;
        let (elem_ctyp, _) = match domain_typ {
            CTyp::Vec(box e, n) => (e, n),
            _ => return Ok(None),
        };
        let Some(binder_atyp) = ATyp::from_ctyp(&elem_ctyp, kctx) else {
            return Ok(None);
        };
        let Some(domain_op) =
            self.lower_loop_body_template(&domain, binders, kctx, fctx, vctx, vars, provenance)?
        else {
            return Ok(None);
        };
        let mut body_binders = binders.to_vec();
        body_binders.push((binder.clone(), binder_atyp));
        let mut body_vctx = vctx.clone();
        body_vctx.insert(&binder, &elem_ctyp);
        let body_prov = provenance.shadow_binding(&binder);
        let Some(body_op) = self.lower_loop_body_template(
            &body,
            &body_binders,
            kctx,
            fctx,
            &body_vctx,
            vars,
            &body_prov,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(GOp::reduce_map(rop, domain_op, body_op, fact)))
    }

    fn is_boolean_hypercube_tail_domain(
        exp: &CExp,
        tail_num_vars: usize,
        provenance: &LoweringProvenance,
    ) -> bool {
        match exp {
            CExp::Var(id) => provenance
                .boolean_hypercube_tails
                .get(id)
                .is_some_and(|p| p.tail_num_vars == tail_num_vars),
            other => Self::classify_boolean_hypercube_tail_domain(other, provenance)
                .is_some_and(|p| p.tail_num_vars == tail_num_vars),
        }
    }

    fn classify_boolean_hypercube_tail_domain(
        exp: &CExp,
        provenance: &LoweringProvenance,
    ) -> Option<BooleanHypercubeProvenance> {
        let CExp::Map(inner, i_var, outer_domain) = exp else {
            return None;
        };
        let CExp::Range(outer_range) = outer_domain.as_ref() else {
            return None;
        };
        if outer_range.start != 0 || outer_range.step != 1 {
            return None;
        }

        let CExp::Map(bit_expr, j_var, inner_domain) = inner.as_ref() else {
            return None;
        };
        let CExp::Range(inner_range) = inner_domain.as_ref() else {
            return None;
        };
        if inner_range.start != 0 || inner_range.step != 1 {
            return None;
        }

        let tail_num_vars = inner_range.len();
        let expected_outer_len = 1usize.checked_shl(tail_num_vars as u32)?;
        if outer_range.len() != expected_outer_len {
            return None;
        }
        let bit_expr_provenance = provenance.shadow_binding(i_var).shadow_binding(j_var);
        if !Self::is_canonical_tail_bit_expr(bit_expr, i_var, j_var, &bit_expr_provenance) {
            return None;
        }

        Some(BooleanHypercubeProvenance { tail_num_vars })
    }

    fn is_canonical_tail_bit_expr(
        exp: &CExp,
        i_var: &Vid,
        j_var: &Vid,
        provenance: &LoweringProvenance,
    ) -> bool {
        match exp {
            CExp::Bin(BinOp::Mul, left, right) => {
                (Self::is_tail_bit_core(left.as_ref(), i_var, j_var)
                    && Self::is_one_factor(right.as_ref(), provenance))
                    || (Self::is_one_factor(left.as_ref(), provenance)
                        && Self::is_tail_bit_core(right.as_ref(), i_var, j_var))
            }
            other => Self::is_tail_bit_core(other, i_var, j_var),
        }
    }

    fn is_one_factor(exp: &CExp, provenance: &LoweringProvenance) -> bool {
        Self::classify_scalar_const(exp, provenance) == Some(ScalarConstProvenance::One)
    }

    fn is_tail_bit_core(exp: &CExp, i_var: &Vid, j_var: &Vid) -> bool {
        let CExp::Bin(BinOp::Rem, div, modulus) = exp else {
            return false;
        };
        if !matches!(modulus.as_ref(), CExp::Lit(2)) {
            return false;
        }
        let CExp::Bin(BinOp::Div, dividend, pow) = div.as_ref() else {
            return false;
        };
        let CExp::Var(i) = dividend.as_ref() else {
            return false;
        };
        if i != i_var {
            return false;
        }
        let CExp::Bin(BinOp::Pow, base, exponent) = pow.as_ref() else {
            return false;
        };
        matches!(base.as_ref(), CExp::Lit(2))
            && matches!(exponent.as_ref(), CExp::Var(j) if j == j_var)
    }

    fn classify_scalar_const(
        exp: &CExp,
        provenance: &LoweringProvenance,
    ) -> Option<ScalarConstProvenance> {
        use ScalarConstProvenance::{One, Zero};

        match exp {
            CExp::Lit(0) => Some(Zero),
            CExp::Lit(1) => Some(One),
            CExp::Var(id) => provenance.scalar_consts.get(id).copied(),
            CExp::Bin(BinOp::Add, left, right) => {
                match (
                    Self::classify_scalar_const(left, provenance),
                    Self::classify_scalar_const(right, provenance),
                ) {
                    (Some(Zero), rhs) => rhs,
                    (lhs, Some(Zero)) => lhs,
                    _ => None,
                }
            }
            CExp::Bin(BinOp::Sub, left, right) => {
                if left == right && Self::is_pure_value_expr(left) {
                    return Some(Zero);
                }
                match (
                    Self::classify_scalar_const(left, provenance),
                    Self::classify_scalar_const(right, provenance),
                ) {
                    (Some(lhs), Some(Zero)) => Some(lhs),
                    _ => None,
                }
            }
            CExp::Bin(BinOp::Mul, left, right) => {
                match (
                    Self::classify_scalar_const(left, provenance),
                    Self::classify_scalar_const(right, provenance),
                ) {
                    (Some(Zero), Some(_)) | (Some(_), Some(Zero)) => Some(Zero),
                    (Some(One), Some(One)) => Some(One),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_poly_hoist_safe(exp: &CExp) -> bool {
        // Bound values have already been evaluated in ordinary lexical order,
        // so `Var(_)` is accepted by the baseline even when its RHS had
        // effects. Inline expressions must pass the conservative pure-value
        // proof below before the fused path may hoist them.
        Self::is_pure_value_expr(exp)
    }

    fn is_pure_value_expr(exp: &CExp) -> bool {
        match exp {
            CExp::Lit(_) | CExp::Bool(_) | CExp::Var(_) | CExp::Range(_) => true,
            CExp::Interpolate(points, evals) => {
                points.as_ref().is_none_or(|p| Self::is_pure_value_expr(p))
                    && Self::is_pure_value_expr(evals)
            }
            CExp::Evaluate(p, _, points) => {
                Self::is_pure_value_expr(p)
                    && points.as_ref().is_none_or(|x| Self::is_pure_value_expr(x))
            }
            CExp::Poly(p) | CExp::Coef(p) | CExp::Mle(p) | CExp::Proj(p, _) => {
                Self::is_pure_value_expr(p)
            }
            CExp::Vec(xs) => xs.0.iter().all(Self::is_pure_value_expr),
            CExp::Bin(_, left, right) | CExp::Pair(left, right) | CExp::Ram(left, right) => {
                Self::is_pure_value_expr(left) && Self::is_pure_value_expr(right)
            }
            CExp::Record(fields) => fields
                .iter()
                .all(|(_, field)| Self::is_pure_value_expr(field)),
            CExp::SetRecord(record, _, value) => {
                Self::is_pure_value_expr(record) && Self::is_pure_value_expr(value)
            }
            // Be conservative around binders, assertions, transcript/random
            // sources, and calls whose bodies are not available in this local
            // syntactic proof.
            CExp::Map(_, _, _)
            | CExp::Reduce(_, _)
            | CExp::Let(_, _, _)
            | CExp::Log(_, _, _)
            | CExp::Assert(_)
            | CExp::Verify(_)
            | CExp::Fun(_, _)
            | CExp::App(_, _)
            | CExp::Random(_, _)
            | CExp::Challenge(_, _) => false,
        }
    }

    fn exp_mentions_free_var(exp: &CExp, target: &Vid) -> bool {
        match exp {
            CExp::Var(id) => id == target,
            CExp::Lit(_) | CExp::Bool(_) | CExp::Range(_) => false,
            CExp::Interpolate(points, evals) => {
                points
                    .as_ref()
                    .is_some_and(|p| Self::exp_mentions_free_var(p, target))
                    || Self::exp_mentions_free_var(evals, target)
            }
            CExp::Evaluate(p, _, points) => {
                Self::exp_mentions_free_var(p, target)
                    || points
                        .as_ref()
                        .is_some_and(|x| Self::exp_mentions_free_var(x, target))
            }
            CExp::Poly(p)
            | CExp::Coef(p)
            | CExp::Mle(p)
            | CExp::Reduce(_, p)
            | CExp::Assert(p)
            | CExp::Verify(p)
            | CExp::Proj(p, _) => Self::exp_mentions_free_var(p, target),
            CExp::Vec(xs) | CExp::App(_, xs) => {
                xs.0.iter().any(|x| Self::exp_mentions_free_var(x, target))
            }
            CExp::Bin(_, left, right)
            | CExp::Pair(left, right)
            | CExp::Ram(left, right)
            | CExp::Let(None, left, right) => {
                Self::exp_mentions_free_var(left, target)
                    || Self::exp_mentions_free_var(right, target)
            }
            CExp::Map(body, binder, domain) => {
                Self::exp_mentions_free_var(domain, target)
                    || (binder != target && Self::exp_mentions_free_var(body, target))
            }
            CExp::Let(Some(id), left, right) | CExp::Log(id, left, right) => {
                Self::exp_mentions_free_var(left, target)
                    || (id != target && Self::exp_mentions_free_var(right, target))
            }
            CExp::Fun(vars, body) => {
                !vars.iter().any(|v| v == target) && Self::exp_mentions_free_var(body, target)
            }
            CExp::Record(fields) => fields
                .iter()
                .any(|(_, field)| Self::exp_mentions_free_var(field, target)),
            CExp::SetRecord(record, _, value) => {
                Self::exp_mentions_free_var(record, target)
                    || Self::exp_mentions_free_var(value, target)
            }
            CExp::Random(_, _) | CExp::Challenge(_, _) => false,
        }
    }

    /// Add an expression [exp] to the graph.
    #[allow(clippy::too_many_arguments)]
    /// Convert a `CExp` to a `GOp` while creating the graph.
    ///
    /// # Invariant
    ///
    /// This method guarantees that its return value is always `Op::Ref` or
    /// `Op::Value`. Compound operations that would produce other variants
    /// (e.g., `Op::Bin`, `Op::Vec`, `Op::Record`) are *materialized*: a DAG
    /// node is created, edges are added, and an `Op::Ref` to the new node is
    /// returned. The sole exception is the trampoline loop body, which may
    /// produce intermediate non-Ref values that are consumed by later
    /// iterations (e.g., `CExp::Let` bindings, `CExp::App` inlining).
    ///
    /// Downstream consumers (notably `trans_clos_op` and `ref_vars` in the
    /// Groebner analysis) rely on this invariant: every top-level result from
    /// `add_exp` can be assumed to be a `Ref` or `Value`.
    fn add_exp(
        &mut self,
        initial_exp: CExp,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
    ) -> Result<GOp<C>, GraphError> {
        self.add_exp_with_provenance(
            initial_exp,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            &LoweringProvenance::new(),
        )
    }

    /// Add an expression [exp] to the graph while preserving lowering-only
    /// provenance used by conservative private optimizer fusions.
    #[allow(clippy::too_many_arguments)]
    fn add_exp_with_provenance(
        &mut self,
        initial_exp: CExp,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>,
        vars: &Ctx<Vid, GOp<C>>,
        provenance: &LoweringProvenance,
    ) -> Result<GOp<C>, GraphError> {
        // Own mutable copies for trampoline loop
        let mut exp = initial_exp;
        let mut vctx = vctx.clone();
        let mut vars = vars.clone();
        let mut provenance = provenance.clone();
        loop {
            // Type inference for [self]
            let typ = exp.infer(kctx, &fctx.keys(), &vctx)?;
            // Convert [CExp] to [Op] while creating the graph
            match exp.clone() {
                // Literals get appended to the last node [self.it]
                CExp::Lit(n) => return Ok(GOp::Value(Value::Index(n))),

                CExp::Bool(b) => return Ok(GOp::Value(Value::Bool(b))),

                // Variables are edges, no new nodes are added
                CExp::Var(id) => return Self::op_from_var(&id, &vars),

                CExp::Evaluate(box p, selector, opt_points) => {
                    let vp = self.add_exp_with_provenance(
                        p.clone(),
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    match (selector, opt_points) {
                        // Unary form: eval(p) -> materialized merged Op::Evaluate(p, None, None).
                        // This preserves the old Node::fft sharing behavior for reusable bindings.
                        (None, None) => {
                            let neval = self.add_node(Node::evaluate_grid(&vp));
                            self.add_edges(edge_type, neval, vp);

                            return Ok(GOp::underscore(
                                neval,
                                ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                                    TypeError::next(
                                        TypeError::exp(kctx, &vctx, &exp),
                                        TypeError::ark(kctx, &vctx, &exp, &typ),
                                    )
                                })?,
                            ));
                        }
                        // Binary form: eval(p, points) -> Op::Evaluate(p, None, Some(points)).
                        (None, Some(box x)) => {
                            let vx = self.add_exp_with_provenance(
                                x,
                                transcr,
                                edge_type,
                                kctx,
                                fctx,
                                &vctx,
                                &vars,
                                &provenance,
                            )?;
                            let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                                TypeError::next(
                                    TypeError::exp(kctx, &vctx, &exp),
                                    TypeError::ark(kctx, &vctx, &exp, &typ),
                                )
                            })?;
                            return Ok(self.materialize(GOp::evaluate(vp, vx), edge_type, atyp));
                        }
                        // Selected form: eval<range>(p, fixed).
                        (Some(range), Some(box fixed)) => {
                            let vfixed = self.add_exp_with_provenance(
                                fixed,
                                transcr,
                                edge_type,
                                kctx,
                                fctx,
                                &vctx,
                                &vars,
                                &provenance,
                            )?;
                            let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                                TypeError::next(
                                    TypeError::exp(kctx, &vctx, &exp),
                                    TypeError::ark(kctx, &vctx, &exp, &typ),
                                )
                            })?;
                            return Ok(self.materialize(
                                GOp::evaluate_selected(vp, range, vfixed),
                                edge_type,
                                atyp,
                            ));
                        }
                        // Parser conversion rejects this; inference is defensive too.
                        (Some(range), None) => {
                            return Err(TypeError::evaluate_selector_without_points(
                                kctx, &vctx, &p, range,
                            )
                            .into());
                        }
                    }
                }

                CExp::Poly(box v) => {
                    let child = self.add_exp_with_provenance(
                        v,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;

                    let npoly = self.add_node(Node::poly(&child));

                    self.add_edges(edge_type, npoly, child);

                    return Ok(GOp::underscore(
                        npoly,
                        ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, &vctx, &exp),
                                TypeError::ark(kctx, &vctx, &exp, &typ),
                            )
                        })?,
                    ));
                }

                CExp::Coef(box v) => {
                    let child = self.add_exp_with_provenance(
                        v,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;

                    let npoly = self.add_node(Node::coef(&child));

                    self.add_edges(edge_type, npoly, child);

                    return Ok(GOp::underscore(
                        npoly,
                        ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, &vctx, &exp),
                                TypeError::ark(kctx, &vctx, &exp, &typ),
                            )
                        })?,
                    ));
                }

                // Lower CExp::Interpolate(opt_points, evals) into either Op::Ifft (unary)
                // or Op::Interpolate (binary) — monomorphic per variant.
                CExp::Interpolate(points_opt, box evals) => {
                    let evals_op = self.add_exp_with_provenance(
                        evals,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    match points_opt {
                        // Unary: interpolate(evs) → Op::Ifft(evs)  (FFT-grid interpolation)
                        None => {
                            let nifft = self.add_node(Node::ifft(&evals_op));
                            self.add_edges(edge_type, nifft, evals_op);

                            return Ok(GOp::underscore(
                                nifft,
                                ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                                    TypeError::next(
                                        TypeError::exp(kctx, &vctx, &exp),
                                        TypeError::ark(kctx, &vctx, &exp, &typ),
                                    )
                                })?,
                            ));
                        }
                        // Binary: interpolate(pts, evs) → Op::Interpolate(pts, evs)
                        Some(box p) => {
                            let points_op = self.add_exp_with_provenance(
                                p,
                                transcr,
                                edge_type,
                                kctx,
                                fctx,
                                &vctx,
                                &vars,
                                &provenance,
                            )?;
                            let ninterp = self.add_node(Node::interpolate(&points_op, &evals_op));
                            self.add_edges(edge_type, ninterp, points_op);
                            self.add_edges(edge_type, ninterp, evals_op);

                            return Ok(GOp::underscore(
                                ninterp,
                                ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                                    TypeError::next(
                                        TypeError::exp(kctx, &vctx, &exp),
                                        TypeError::ark(kctx, &vctx, &exp, &typ),
                                    )
                                })?,
                            ));
                        }
                    }
                }
                // Create a new [vec] value
                CExp::Vec(vs) => {
                    let vec_op = GOp::vec(vs.0.traverse1(&mut |v| {
                        self.add_exp_with_provenance(
                            v,
                            transcr,
                            edge_type,
                            kctx,
                            fctx,
                            &vctx,
                            &vars,
                            &provenance,
                        )
                    })?);
                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    return Ok(self.materialize(vec_op, edge_type, atyp));
                }

                // MLE is a noop?
                // CExp::Mle(box inner) => self.add_exp(inner, transcr, edge_type, kctx, fctx, &vctx, &vars),
                CExp::Mle(box v) => {
                    let child = self.add_exp_with_provenance(
                        v,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;

                    let nmle = self.add_node(Node::mle(&child));

                    self.add_edges(edge_type, nmle, child);

                    return Ok(GOp::underscore(
                        nmle,
                        ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, &vctx, &exp),
                                TypeError::ark(kctx, &vctx, &exp, &typ),
                            )
                        })?,
                    ));
                }

                // Billinear pairing
                CExp::Pair(box a, box b) => {
                    let va = self.add_exp_with_provenance(
                        a,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    let vb = self.add_exp_with_provenance(
                        b,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;

                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;

                    return Ok(self.materialize(GOp::pair(va, vb, atyp.clone()), edge_type, atyp));
                }
                // Create a new [bin] node
                CExp::Bin(op, box a, box b) => {
                    // Add children first
                    let vl = self.add_exp_with_provenance(
                        a,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    let vr = self.add_exp_with_provenance(
                        b,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;

                    // Convert type [typ] to [ATyp]
                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;

                    let bop = GOp::bin(op, vl.clone(), vr.clone(), atyp.clone());

                    // Maybe there will be no node
                    if let GOp::Bin(op, vl, vr, atyp) = bop {
                        // Add new node
                        let nbin = self.add_node(Node::bin(op, &vl, &vr, &atyp));

                        // Add edges from [nbin] to [vl] and [vr]
                        self.add_edges(edge_type, nbin, (*vl).clone());
                        self.add_edges(edge_type, nbin, (*vr).clone());
                        return Ok(GOp::underscore(nbin, atyp));
                    } else {
                        return Ok(self.materialize(bop, edge_type, atyp));
                    }
                }

                // Create a [range] value, no new nodes added
                CExp::Range(r) => return Ok(GOp::range(r)),

                CExp::Map(box l, x, box e) => {
                    let map_atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    // Fast path: lower to a persistent `Op::Map` when the body
                    // and domain are pure. Falls back to the unroll otherwise.
                    if let Some(map_op) = self.lower_loop_body_template(
                        &CExp::Map(Box::new(l.clone()), x.clone(), Box::new(e.clone())),
                        &[],
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )? {
                        return Ok(self.materialize(map_op, edge_type, map_atyp));
                    }

                    let te = e.infer(kctx, &fctx.keys(), &vctx)?;

                    // Op for [e]
                    let oe = self.add_exp_with_provenance(
                        e,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;

                    let (ie, n) = te.into_vec();

                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;

                    let input_element_typ = ATyp::from_ctyp(&ie, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &ie),
                        )
                    })?;

                    let mut res = Vec::with_capacity(n);
                    for i in 0..n {
                        // Add oe[i] to local vars and vctx. The map binder shadows
                        // any same-named let provenance in the comprehension body.
                        let mut local_vars = vars.clone();
                        let mut local_vctx = vctx.clone();
                        let mut local_provenance = provenance.clone();
                        let ram_op = GOp::ram(oe.clone(), GOp::index(i));
                        let ram_ref =
                            self.materialize(ram_op, edge_type, input_element_typ.clone());
                        local_vars.insert(&x, &ram_ref);
                        local_vctx.insert(&x, &ie);
                        local_provenance.remove_binding(&x);
                        // Add subexpression
                        let ol = self.add_exp_with_provenance(
                            l.clone(),
                            transcr,
                            edge_type,
                            kctx,
                            fctx,
                            &local_vctx,
                            &local_vars,
                            &local_provenance,
                        )?;
                        res.push(ol);
                    }
                    return Ok(self.materialize(GOp::vec(res), edge_type, atyp));
                }

                CExp::Reduce(op, box v) => {
                    let reduce_map = if let CExp::Map(box body, binder, box domain) = v.clone() {
                        self.try_build_reduce_map(
                            op,
                            body,
                            binder,
                            domain,
                            &[],
                            kctx,
                            fctx,
                            &vctx,
                            &vars,
                            &provenance,
                        )?
                    } else {
                        None
                    };
                    if let Some(rm) = reduce_map {
                        let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, &vctx, &exp),
                                TypeError::ark(kctx, &vctx, &exp, &typ),
                            )
                        })?;
                        return Ok(self.materialize(rm, edge_type, atyp));
                    }
                    let ov = self.add_exp_with_provenance(
                        v,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    return Ok(self.materialize(GOp::reduce(op, ov), edge_type, atyp));
                }
                CExp::Ram(box a, box b) => {
                    // Add children
                    let oa = self.add_exp_with_provenance(
                        a,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    let ob = self.add_exp_with_provenance(
                        b,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    return Ok(self.materialize(GOp::ram(oa, ob), edge_type, atyp));
                }
                CExp::Challenge(_, non_zero) => {
                    let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    let nchallenge = self.add_node(Node::challenge(&at, non_zero));
                    // Add transcript edge to [nchallenge]
                    self.add_edge(*transcr, nchallenge, Dep::transcript());
                    // Update transcript node
                    *transcr = nchallenge;

                    // If the challenge is non-zero, add a prover assertion
                    return Ok(GOp::underscore(nchallenge, at));
                }
                CExp::Random(_, non_zero) => {
                    let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    let nrand = self.add_node(Node::random(&at, non_zero));
                    return Ok(GOp::underscore(nrand, at));
                }
                CExp::App(fid, params) => {
                    // type inference for each parameter
                    let param_types: CTyps = params
                        .iter()
                        .map(|p| p.infer(kctx, &fctx.keys(), &vctx))
                        .collect::<Result<_, _>>()?;

                    // Is it a polynomial, MLE, or a function?
                    match &vctx.get(&fid) {
                        Some(CTyp::Poly(tbase, 1, _n)) => {
                            // It is a univariate polynomial
                            let k = kctx.get(tbase).unwrap();

                            // Only field elements can be evaluated and only 1 argument can be given
                            assert!(k.is_scalar());
                            assert_eq!(param_types.len(), 1);

                            // Phase B: desugar `p(x)` directly to
                            // `evaluate(p, x)` using `Op::Evaluate`. The
                            // pre-Phase-B route went through
                            // `dot(p, [x^0, x^1, ..., x^n])` which required
                            // implicitly reinterpreting the polynomial as a
                            // coefficient list — that lub_dot(Poly, Vec) arm
                            // has been removed.
                            let eval_exp = CExp::evaluate_at(CExp::var(&fid), params[0].clone());
                            // Trampoline
                            exp = eval_exp;
                            continue;
                        }
                        Some(CTyp::Poly(tbase, n, 1)) => {
                            // It is a multilinear extension
                            let k = kctx.get(tbase).unwrap();

                            // Only field elements can be evaluated and only 1 argument can be given
                            assert!(k.is_scalar());
                            assert_eq!(param_types.len(), 1);

                            // https://github.com/microsoft/Nova/blob/ad4d77ac89d6bbe9ef943056806e65ceb4ba3b3e/src/spartan/polys/multilinear.rs#L58
                            let mle_l =
                                CExp::ram(CExp::var(&fid), CExp::range(CRange::new(0, n - 1)));

                            let mle_r =
                                CExp::ram(CExp::var(&fid), CExp::range(CRange::new(n - 1, *n)));

                            // mle_l + (mle_r - mle_l) * params[0]
                            let fold = CExp::add(
                                mle_l.clone(),
                                CExp::mul(params[0].clone(), CExp::sub(mle_r, mle_l)),
                            );

                            // Trampoline
                            exp = fold;
                            continue;
                        }
                        _ => {
                            let mut matching_sigs: Vec<_> = fctx
                                .iter()
                                .filter_map(|(sig, body)| {
                                    if sig.name != fid {
                                        return None;
                                    }
                                    let (sig, subs) = sig.clone().unify(&param_types, kctx).ok()?;
                                    Some((sig, body, subs))
                                })
                                .collect();

                            if matching_sigs.len() > 1 {
                                matching_sigs.retain(|(sig, _, _)| {
                                    sig.args
                                        .iter()
                                        .zip(param_types.0.iter())
                                        .all(|(a, t)| a.typ == *t)
                                });
                            }

                            // Only one function shoud match (enforced by the type system)
                            assert_eq!(matching_sigs.len(), 1);
                            let triple = matching_sigs[0].clone();
                            let sig = triple.0;
                            let mut body = triple.1.clone();
                            let subs = triple.2;
                            subs.tid_subst(&mut body);

                            // First add the arguments to the graph
                            let oparams: Vec<GOp<C>> = params
                                .into_iter()
                                .map(|p| {
                                    self.add_exp_with_provenance(
                                        p,
                                        transcr,
                                        edge_type,
                                        kctx,
                                        fctx,
                                        &vctx,
                                        &vars,
                                        &provenance,
                                    )
                                })
                                .collect::<Result<_, _>>()?;

                            // Trampoline: replace context and continue with body
                            let mut next_vctx = vctx.clone();
                            for (vid, typ) in sig.args.to_ctx().iter() {
                                next_vctx.insert(vid, typ);
                            }
                            vctx = next_vctx;
                            let mut next_vars = vars.clone();
                            for (arg, op) in sig.args.iter().zip(oparams.iter()) {
                                next_vars.insert(&arg.id, op);
                            }
                            vars = next_vars;
                            provenance = LoweringProvenance::new();
                            let fn_kctx = sig.typevars.to_ctx();
                            for (tid, kind) in fn_kctx.iter() {
                                if let CKind::Range(r) = kind
                                    && r.step == 1
                                    && r.end == r.start + 1
                                {
                                    let vid = Vid::new(&tid.0);
                                    vctx.insert(&vid, &CTyp::Fin(*r));
                                    vars.insert(&vid, &GOp::Value(Value::Index(r.start)));
                                }
                            }
                            exp = body.body();
                            continue;
                        }
                    }
                }
                CExp::Let(Some(id), box l, box r) => {
                    let scalar_const = Self::classify_scalar_const(&l, &provenance);
                    let hypercube_tail =
                        Self::classify_boolean_hypercube_tail_domain(&l, &provenance);
                    // Infer the type of [l]
                    let tl = l.infer(kctx, &fctx.keys(), &vctx)?;
                    // Add left-hand side as node
                    let nl = self.add_exp_with_provenance(
                        l,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    // Add [id] to the variable context (clone-on-write)
                    vctx.insert(&id, &tl);
                    vars.insert(&id, &nl);
                    provenance.remove_binding(&id);
                    if let Some(tail) = hypercube_tail {
                        provenance.boolean_hypercube_tails.insert(&id, &tail);
                    }
                    if let Some(scalar) = scalar_const {
                        provenance.scalar_consts.insert(&id, &scalar);
                    }
                    // Trampoline: continue loop with r
                    exp = r;
                    continue;
                }
                CExp::Let(None, box l, box r) => {
                    self.add_exp_with_provenance(
                        l,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    // Trampoline: continue loop with r
                    exp = r;
                    continue;
                }
                CExp::Log(id, box l, box r) => {
                    // Infer the type of [l]
                    let tl = l.infer(kctx, &fctx.keys(), &vctx)?;
                    // Add left-hand side as node
                    let ol = self.add_exp_with_provenance(
                        l,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    // Record transcript interaction
                    let transcr_op = match &ol {
                        GOp::Ref(r, _)
                            if self[r.node()].is_transcript()
                                && !self.vctx.get(&r.node()).map(|v| v != &id).unwrap_or(false) =>
                        {
                            let n = r.node();
                            // Node is already a transcript node and either has no name
                            // or the same name — register directly.
                            self.vctx.insert(&n, &id);
                            self.transcript_vars.insert(&n, &true);
                            GOp::Ref(Ref(n), ol.typ())
                        }
                        GOp::Ref(r, _) => {
                            let n = r.node();
                            // Reuse: create a wrapper transcript node.
                            let nl = self.add_node(Node::transcr(&GOp::Ref(Ref(n), ol.typ())));
                            self.add_edges(DepType::Data, nl, ol.clone());
                            self.add_edge(*transcr, nl, Dep::transcript());
                            self.graph.node_weight_mut(nl).unwrap().set_transcript();
                            self.vctx.insert(&nl, &id);
                            self.transcript_vars.insert(&nl, &true);
                            *transcr = nl;
                            GOp::Ref(Ref(nl), ol.typ())
                        }
                        _ => {
                            // Add new transcript node
                            let nl = self.add_node(Node::transcr(&ol));
                            self.add_edges(DepType::Data, nl, ol.clone());
                            self.add_edge(*transcr, nl, Dep::transcript());
                            self.graph.node_weight_mut(nl).unwrap().set_transcript();
                            self.vctx.insert(&nl, &id);
                            self.transcript_vars.insert(&nl, &true);
                            *transcr = nl;
                            GOp::Ref(Ref(nl), ol.typ())
                        }
                    };
                    // Add [id] to the variable context (clone-on-write)
                    vctx.insert(&id, &tl);
                    vars.insert(&id, &transcr_op);
                    provenance.remove_binding(&id);
                    // Trampoline: continue loop with r
                    exp = r;
                    continue;
                }
                CExp::Assert(box a) => {
                    let oa = self.add_exp_with_provenance(
                        a,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    // Add new node
                    let nassert = self.add_node(Node::check(&oa));
                    // Add edges
                    self.add_edges(edge_type, nassert, oa);
                    // Assert depends on the full transcript (implicit ordering)
                    self.add_edge(*transcr, nassert, Dep::transcript());
                    return Ok(GOp::underscore(
                        nassert,
                        ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, &vctx, &exp),
                                TypeError::ark(kctx, &vctx, &exp, &typ),
                            )
                        })?,
                    ));
                }
                CExp::Verify(box a) => {
                    let oa = self.add_exp_with_provenance(
                        a,
                        transcr,
                        edge_type,
                        kctx,
                        fctx,
                        &vctx,
                        &vars,
                        &provenance,
                    )?;
                    // Add new node
                    let nverify = self.add_node(Node::check(&oa));
                    self.add_edges(edge_type, nverify, oa);
                    // Verify depends on the full transcript (implicit ordering)
                    self.add_edge(*transcr, nverify, Dep::transcript());
                    return Ok(GOp::underscore(
                        nverify,
                        ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, &vctx, &exp),
                                TypeError::ark(kctx, &vctx, &exp, &typ),
                            )
                        })?,
                    ));
                }
                CExp::Fun(fun_vars, box body) => {
                    // Convert the Fun expression body to a PolyVariant
                    let var_map: HashMap<Vid, usize> = fun_vars
                        .iter()
                        .enumerate()
                        .map(|(i, v)| (v.clone(), i))
                        .collect();

                    let poly = Self::exp_to_poly_variant(&body, &fun_vars, &var_map)?;

                    // Create a Value::Poly from the PolyVariant wrapped in VirtualPolynomial
                    let poly_value = Value::Poly(VirtualPolynomial::from_poly(poly));

                    return Ok(GOp::Value(poly_value));
                }
                CExp::Record(fields) => {
                    let mut field_ops: Ctx<String, HOp<C>> = Ctx::new();

                    for (field_name, field_exp) in fields.iter() {
                        let field_op = self.add_exp_with_provenance(
                            field_exp.clone(),
                            transcr,
                            edge_type,
                            kctx,
                            fctx,
                            &vctx,
                            &vars,
                            &provenance,
                        )?;
                        let hop = mk::<C>(field_op);
                        field_ops.insert(field_name, &hop);
                    }

                    let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, &vctx, &exp),
                            TypeError::ark(kctx, &vctx, &exp, &typ),
                        )
                    })?;
                    return Ok(self.materialize(GOp::Record(field_ops), edge_type, atyp));
                }
                CExp::Proj(box record_exp, field_name) => {
                    // For projection, we need to extract the field from the record
                    // Check if the record expression is a Record literal
                    return match record_exp {
                        CExp::Record(fields) => {
                            let field_exp = fields.get(&field_name).ok_or_else(|| {
                                let mut field_types = Ctx::new();
                                for (name, exp) in fields.iter() {
                                    if let Ok(typ) = exp.infer(kctx, &fctx.keys(), &vctx) {
                                        field_types.insert(name, &typ);
                                    }
                                }
                                GraphError::from(TypeError::field_not_found(
                                    kctx,
                                    &vctx,
                                    &CExp::Record(fields.clone()),
                                    field_name.as_str(),
                                    &field_types,
                                ))
                            })?;

                            // Add the field expression to the graph
                            self.add_exp_with_provenance(
                                field_exp.clone(),
                                transcr,
                                edge_type,
                                kctx,
                                fctx,
                                &vctx,
                                &vars,
                                &provenance,
                            )
                        }
                        CExp::Var(id) => {
                            let id_clone = id.clone();
                            let record_op = vars.get(&id_clone).ok_or_else(|| {
                                GraphError::from(TypeError::exp(
                                    kctx,
                                    &vctx,
                                    &CExp::Var(id_clone.clone()),
                                ))
                            })?;

                            // Try to infer the record type to verify the field exists
                            let record_typ =
                                CExp::Var(id_clone.clone()).infer(kctx, &fctx.keys(), &vctx)?;

                            match &record_typ {
                                CTyp::Record(fields) => {
                                    // Verify the field exists and get its type
                                    let field_typ_ctyp =
                                        fields.get(&field_name).ok_or_else(|| {
                                            GraphError::from(TypeError::field_not_found(
                                                kctx,
                                                &vctx,
                                                &CExp::Var(id_clone.clone()),
                                                field_name.as_str(),
                                                fields,
                                            ))
                                        })?;

                                    // Extract the field from the record operation
                                    match record_op {
                                        Op::Record(record_fields) => {
                                            // Direct field access from Record operation
                                            record_fields
                                                .get(&field_name)
                                                .ok_or_else(|| {
                                                    GraphError::from(TypeError::field_not_found(
                                                        kctx,
                                                        &vctx,
                                                        &CExp::Var(id_clone.clone()),
                                                        field_name.as_str(),
                                                        fields,
                                                    ))
                                                })
                                                .map(|op| (**op).clone())
                                        }
                                        Op::Ref(r, _op_typ) => {
                                            // If the DAG node stores a Record, extract the
                                            // field directly (avoiding an unnecessary Proj node).
                                            if let Some(inner) = self[r.node()].op() {
                                                if let Op::Record(fields) = inner.get() {
                                                    if let Some(field_op) = fields.get(&field_name)
                                                    {
                                                        return Ok(field_op.get().clone());
                                                    }
                                                }
                                            }
                                            // Record produced by a node (e.g. a record-typed op); add Proj node
                                            let field_typ_atyp =
                                                ATyp::from_ctyp(field_typ_ctyp, kctx).ok_or_else(
                                                    || {
                                                        GraphError::from(TypeError::ark(
                                                            kctx,
                                                            &vctx,
                                                            &CExp::Var(id_clone.clone()),
                                                            field_typ_ctyp,
                                                        ))
                                                    },
                                                )?;
                                            // If the record source is an Arg node we don't need
                                            // to materialise a Proj node — the field is selected
                                            // directly off the typed reference.
                                            if self[r.node()].is_arg() {
                                                return Ok(Op::Ref(Ref(r.node()), field_typ_atyp));
                                            }
                                            let proj_node = self.add_node(Node::proj(
                                                record_op,
                                                &field_name,
                                                &field_typ_atyp,
                                            ));
                                            self.add_edges(edge_type, proj_node, record_op.clone());
                                            Ok(Op::Ref(Ref(proj_node), field_typ_atyp))
                                        }
                                        _ => Err(GraphError::from(TypeError::not_a_record(
                                            kctx,
                                            &vctx,
                                            &CExp::Var(id_clone.clone()),
                                            &record_typ,
                                        ))),
                                    }
                                }
                                _ => Err(GraphError::from(TypeError::not_a_record(
                                    kctx,
                                    &vctx,
                                    &CExp::Var(id_clone.clone()),
                                    &record_typ,
                                ))),
                            }
                        }
                        _ => {
                            // For other expressions, try to infer the record type
                            let record_typ = record_exp.infer(kctx, &fctx.keys(), &vctx)?;

                            match record_typ {
                                CTyp::Record(fields) => {
                                    // Get the field type
                                    let _field_typ = fields.get(&field_name).ok_or_else(|| {
                                        GraphError::from(TypeError::field_not_found(
                                            kctx,
                                            &vctx,
                                            &record_exp,
                                            field_name.as_str(),
                                            &fields,
                                        ))
                                    })?;

                                    // For complex expressions, we'd need to evaluate them first
                                    // For now, return an error indicating this isn't fully supported
                                    Err(GraphError::from(TypeError::next(
                                        TypeError::exp(kctx, &vctx, &exp),
                                        TypeError::ark(kctx, &vctx, &exp, &typ),
                                    )))
                                }
                                _ => Err(GraphError::from(TypeError::not_a_record(
                                    kctx,
                                    &vctx,
                                    &record_exp,
                                    &record_typ,
                                ))),
                            }
                        }
                    };
                }
                CExp::SetRecord(box record_exp, field_name, box value_exp) => {
                    // Build new record as expression: all fields from record_exp, with field_name replaced by value_exp
                    let record_typ = record_exp.infer(kctx, &fctx.keys(), &vctx)?;
                    let CTyp::Record(typ_fields) = &record_typ else {
                        return Err(GraphError::from(TypeError::not_a_record(
                            kctx,
                            &vctx,
                            &record_exp,
                            &record_typ,
                        )));
                    };
                    let mut new_record_fields = Ctx::new();
                    for (fname, _) in typ_fields.iter() {
                        let field_exp = if fname == &field_name {
                            value_exp.clone()
                        } else {
                            CExp::Proj(Box::new(record_exp.clone()), fname.clone())
                        };
                        new_record_fields.insert(fname, &field_exp);
                    }
                    let new_record_exp = CExp::Record(new_record_fields);
                    // Trampoline
                    exp = new_record_exp;
                    continue;
                }
            }
        } // end loop
    }
}

impl<C: ArkConfig, A> Index<NodeIndex> for Dag<C, A> {
    type Output = Node<C, A>;
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.graph[index]
    }
}

impl<C: ArkConfig, A> std::ops::IndexMut<NodeIndex> for Dag<C, A> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.graph[index]
    }
}

impl<C: ArkConfig, A> Index<usize> for Dags<C, A> {
    type Output = Dag<C, A>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

#[cfg(test)]
use backend::ArkBls12_381;
#[cfg(test)]
use lang::ast::UModule;
#[cfg(test)]
use share::unwrap;
#[test]
fn graph_sum() {
    let ex = r#"
        fn sum<N: 1..4, F: Field>(public a: [F; 2^N]) -> F {
            sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])
        }

        fn sum<F: Field>(public a: [F; 1]) -> F {
           a[0]
        }"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    assert_eq!(m.len(), 4);
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
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
        proto foo<F: Field>(private s: F, public v: [F; 10]) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r + c + s;
            x <- v[1..5];
            verify(a * s == b * x[3])
        }"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
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
        proto poly_mul<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 4>) where a == a {
            let r = random<F*>;
            let p = a * b;
            verify(p(r) == (a(r) * b(r)))
        }"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
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
        fn reduction_foo<F: Field>(public a: [F; 10]) -> F {
            reduce(+, a)
        }"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_reduce").unwrap_or_else(|e| {
        debug!(
            "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
            e
        );
    });
}
