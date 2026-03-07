#![feature(box_patterns)]
#![feature(trait_alias)]
mod node;
mod dep;
mod op;
pub mod analyses;
pub mod scheduler;
pub mod pref;
pub mod domain_seperator;
pub mod eval;

#[cfg(test)]
mod tests;

use log::debug;
pub use op::{Ref, Op, GOp};
pub use node::Node;
pub use dep::{DepType, Dep};
pub use pref::PRef;
pub use analyses::StaticAnalysis;

use backend::{ArkConfig, Value, ATyp, PolyVariant, VirtualPolynomial};
use share::{traversal::ToTraversal1, Set, Ctx};
use lang::ast::{CModule, BinOp, CExp, Arg, CSig, CBody};
use lang::id::{Tid, Vid};
use lang::typ::{Qualifier, Distribution, Nothing, CTyp, CTyps, Kind};
use lang::typ::range::CRange;
use lang::typ::infer::{Typeable, TypeError};
use ark_poly::{univariate::DensePolynomial, DenseMultilinearExtension, DenseUVPolynomial};

use thiserror::Error;
use petgraph::{dot::Dot, graph::{EdgeReference, NodeIndex, NodeIndices, Neighbors}, visit::EdgeRef, Direction, Graph};
use std::process::Command;
use std::ops::Index;
use std::path::PathBuf;
use std::collections::{HashMap, HashSet};

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
#[derive(Clone)]
pub struct Dag<C: ArkConfig, A>(Graph<Node<C, A>, Dep>);

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
    Type(#[from] TypeError),
    #[error("Fun expression contains non-polynomial operations: {0}")]
    NonPolynomialFun(String),
}

/// A trait for writing a graph to a PDF file
pub trait WritePdf {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()>;
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

impl<C: ArkConfig, A> Dag<C, A> {

    pub fn new() -> Self {
        Dag(Graph::new())
    }

    /// Print all edges in the graph
    pub fn print_edges(&self) {
        for edge in self.0.edge_references() {
            let source = edge.source();
            let target = edge.target();
            debug!("Edge from {:?} to {:?}", source, target);
        }
    }

    /// Get the number of nodes in the graph
    pub fn node_count(&self) -> usize {
        self.0.node_count()
    }

    pub fn nodes_indices(&self) -> Vec<NodeIndex> {
        self.0.node_indices().collect()
    }

    /// Get the number of edges in the graph
    pub fn edge_count(&self) -> usize {
        self.0.edge_count()
    }

    pub fn input_node(&self) -> NodeIndex {
        self.0.node_indices().find(|n| self.0[*n].is_input())
            .expect("No input node found, DAG uninitialized")
    }

    pub fn relation_node(&self) -> Option<NodeIndex> {
        self.0.node_indices().find(|n| self.0[*n].is_relation())
    }

    pub fn op_nodes(&self) -> Vec<NodeIndex> {
        self.0.node_indices().filter(|n| self[*n].is_op()).collect()
    }

    pub fn args(&self) -> Vec<PRef> {
        match &self[self.input_node()] {
            Node::Inp(_, args) => args.clone(),
            Node::Rel(_, args) => args.clone(),
            _ => unreachable!("All Dags should have an input node")
        }
    }

    pub fn map_node_indices<F: Fn(NodeIndex) -> NodeIndex>(&self, f: &F) -> Dag<C, A> where A: Clone {
        Dag(self.0.map(
            |_, node| node.map_node_indices(f),
            |_, e| e.clone()
        ))
    }

    /// Dep deduplication
    fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Dep) {
        // If the edge is not a self-loop add it
        if source != sink {
            self.0.add_edge(source, sink, edge);
        }
    }

    pub(crate) fn add_edges(&mut self, edge_type: DepType, sink: NodeIndex, source: GOp<C>) {
        source.references().into_iter().for_each(|refer| {
            match refer {
                Ref::Node(n) =>  // Add edge from [n] to [sink]
                    self.add_edge(n, sink, Dep::new(edge_type, None)),
                Ref::Var(v, i) => // Add edge from [i] to [sink]
                    self.add_edge(i, sink, Dep::new(edge_type, Some(v))),
            }
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
            for neighbor in self.0.neighbors_directed(n, direction) {
                worklist.push(neighbor);
            }
        }
        closure
    }

    /// Add a node to the graph (no deduplication)
    pub fn add_node(&mut self, node: Node<C, A>) -> NodeIndex {
        self.0.add_node(node)
    }

    pub fn get_node(&mut self, it: NodeIndex) -> &mut Node<C, A> {
        &mut self.0[it]
    }

    /// Slow, look around to find a var for a node
    pub fn find_var(&self, node: NodeIndex) -> Option<Vid> {
        self.node_indices().find_map(|n| {
            self[n].references().into_iter().find_map(|r| {
                if r.node() == node {
                    r.var()
                } else {
                    None
                }
            })
        })
    }

    pub fn find_ref(&self, node: NodeIndex) -> Ref {
        if let Some(v) = self.find_var(node) {
            Ref::Var(v, node)
        } else {
            Ref::Node(node)
        }
    }

    pub fn node_indices(&self) -> NodeIndices {
        self.0.node_indices()
    }

    /// Get reference to internal graph (for testing)
    #[cfg(test)]
    pub(crate) fn inner_graph(&self) -> &Graph<Node<C, A>, Dep> {
        &self.0
    }

    pub fn max_node(&self) -> NodeIndex {
        self.0.node_indices().last().unwrap()
    }

    pub fn name(&self) -> Vid {
        let inp = self.input_node();
        self[inp].name().unwrap().clone()
    }

    /// Annotate the graph using function [f]
    pub fn map_annotations<B, F: Fn(&GOp<C>, &A) -> B>(&self, f: &F) -> Dag<C, B> {
        Dag(self.0.map(
            |_, node|
                match node {
                    Node::Op(op, ann) => Node::Op(op.clone(), f(op, ann)),
                    Node::Transcr(op, ann) => Node::Transcr(op.clone(), f(op, ann)),
                    Node::Inp(a, b) => Node::Inp(a.clone(), b.clone()),
                    Node::Rel(a, b) => Node::Rel(a.clone(), b.clone()),
                },
                |_, e| e.clone()
        ))
    }

    pub fn neighbors_directed(&self, node_index: NodeIndex, direction: Direction) -> Neighbors<'_, Dep, u32> {
        self.0.neighbors_directed(node_index, direction)
    }

    pub fn transcript_edge<'a>(&'a self, n: NodeIndex, dir: Direction) -> Option<EdgeReference<'a, Dep>> {
        self.0.edges_directed(n, dir)
            .find(|edge| edge.weight().is_transcript())
    }

    /// Get all transcript node from the graph (challenges and proof nodes)
    pub fn transcript_nodes(&self) -> Vec<NodeIndex> {
        let transcript_nodes_list: Vec<NodeIndex> = self.0.node_indices()
            .filter(|n| self[*n].is_transcript())
            .collect();
        
        // Do a topological sort of the transcript nodes
        let mut ordered = Vec::new();
        if !transcript_nodes_list.is_empty() {
            let mut parent_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
            let mut has_parent_in_list = HashSet::new();
            
            for &node in &transcript_nodes_list {
                for parent in self.0.neighbors_directed(node, petgraph::Direction::Incoming) {
                    if transcript_nodes_list.contains(&parent) {
                        parent_map.insert(node, parent);
                        has_parent_in_list.insert(node);
                    }
                }
            }        
 
            let root = transcript_nodes_list.iter()
                .find(|&&n| !has_parent_in_list.contains(&n))
                .expect("Cycle detected in transcript nodes");
            
            let mut current = *root;
            ordered.push(current);
            while let Some(&child) = transcript_nodes_list.iter()
                .find(|&&n| parent_map.get(&n) == Some(&current)) {
                ordered.push(child);
                current = child;
            }  
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

    /// Get the prover graph, by reachability analysis starting from the transcript nodes
    pub fn get_prover(&self) -> (Dag<C, A>, HashMap<NodeIndex, Ref>) where A: Clone {
        let mut prover = Dag::new();
        // Add all nodes to the prover graph
        let mut worklist: Vec<NodeIndex> = self.transcript_nodes();
        // Map old node indices to new references
        let mut node_map: HashMap<NodeIndex, Ref> = HashMap::new();

        // Add input node first, so it is NodeIndex::new(0)
        let n_input = prover.add_node(self[self.input_node()].clone());
        node_map.insert(self.input_node(), Ref::Node(n_input));

        while let Some(n) = worklist.pop() {
            if node_map.contains_key(&n) {
                continue;
            }
            // Add node to prover graph
            let new_node = prover.add_node(self[n].clone());
            if let Some(v) = self.find_var(n) {
                node_map.insert(n, Ref::Var(v, new_node));
            } else {
                node_map.insert(n, Ref::Node(new_node));
            }

            // Add previous neighbors to worklist
            for e in self.0.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                worklist.push(e.source());
            }
        }

        // Add edges to prover graph using the mapped node indices
        for edge_ref in self.0.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = edge_ref.weight().clone();

            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map.get(&old_source_idx), node_map.get(&old_target_idx))
            {
                prover.add_edge(new_source_idx.node(), new_target_idx.node(), weight);
            }
        }

        // Remap node indices in Ref to the new node indices
        let remapped = prover.map_node_indices(&|n|
            node_map.get(&n).map(|r| r.node()).unwrap_or_else(||
                panic!("Aliasing error: node {}: {} in prover not found in {} protocol dag",
                    n.index(), self[n].drop_annotation(), self.name())));

        (remapped, node_map)
    }

    /// Get the relation graph, by reachability analysis starting from the relation node
    pub fn get_relation(&self) -> Result<Dag<C, A>, GraphError> where A: Clone {
        let mut g_relation = Dag::new();
        let relation_node =
            self.relation_node().ok_or(GraphError::RelationNotFound(self.name()))?;

        let mut worklist = vec![relation_node];
        let mut node_map_rel = HashMap::<NodeIndex, NodeIndex>::new();

        while let Some(n) = worklist.pop() {
            if node_map_rel.contains_key(&n) {
                continue;
            }
            let new_node = g_relation.add_node(self[n].clone());
            node_map_rel.insert(n, new_node);
            for e in self.0.edges_directed(n, Direction::Outgoing) {
                worklist.push(e.target());
            }

            for e in self.0.edges_directed(n, Direction::Outgoing) {
                worklist.push(e.target());
            }
        }

        // Add edges to relation graph using the mapped node indices
        for edge_ref in self.0.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = edge_ref.weight().clone();

            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map_rel.get(&old_source_idx), node_map_rel.get(&old_target_idx))
            {
                g_relation.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }
        Ok(g_relation.map_node_indices(&|n| node_map_rel[&n]))
    }

    pub fn rename_inner_nodes(&mut self)  -> Dag<C, A> where A: Clone {
        let arg_names: Vec<String> = self.args().iter().map(|arg| arg.var().unwrap().0).collect();
        debug!("args_name: {:?}", arg_names);
        self.map_ops(&|op| op.map_refs(&|r| 
            match r {
                Ref::Var(Vid(s), n) =>
                    if arg_names.contains(&s) {
                        Ref::Var(Vid(s), n)
                    } else {
                        Ref::Var(Vid(s + &format!("_{:?}", n)), n)
                    },
                _ => r,
            }))
    }

    pub fn map_ops<F: Fn(&GOp<C>) -> GOp<C>>(&mut self, f: &F) -> Dag<C, A> where A: Clone {
        Dag(self.0.map(|_, node| 
            match node {
                Node::Op(op, ann) => Node::Op(f(op), ann.clone()),
                Node::Transcr(op, ann) => Node::Transcr(f(op), ann.clone()),
                _ => node.clone(),
            },
        |_, e| e.clone()
        ))
    }

    /// Get the verifier graph, by reachability analysis starting from the verifier assertion
    /// and stopping at transcript nodes.
    pub fn get_verifier(&self) -> Result<Dag<C, A>, GraphError> where A: Clone {
        let mut verifier = Dag::new();
        let proof_nodes = self.get_proof_nodes();

        // Rebuild the input node to take transcript arguments
        let mut args = self.args().into_iter().filter(|pr| pr.is_public()).collect::<Vec<_>>();
        let name = self.name();

        // Add the transcript nodes (public) to the arguments
        for node in &proof_nodes {
            let transcript_var = self.find_var(*node).ok_or(GraphError::node_not_found(*node))?;
            if args.iter().any(|a| a.var() == Some(transcript_var.clone())) {
                continue;
            }
            args.push(
                PRef::from_var(transcript_var,
                    self.input_node(),
                    self[*node].clone().into_op().typ(),
                    0,
                    Qualifier::Public,
                    Distribution::default())
                    .mark_transcript_source());
        }
        // Associate old node indices with new node indices
        let mut node_map_self = HashMap::<NodeIndex, NodeIndex>::new();

        // Make new input node
        let n_input = verifier.add_node(Node::Inp(name, args));
        node_map_self.insert(self.input_node(), n_input);
        let mut non_challenge_transcripts: HashSet<NodeIndex> = HashSet::new();

        // Add transcript nodes to verifier graph
        for &n_transcr in &self.transcript_nodes() {
            let node = &self[n_transcr];
            if node.is_challenge() {
                let new_node = verifier.add_node(node.clone());
                node_map_self.insert(n_transcr, new_node);
                continue;
            }
            non_challenge_transcripts.insert(n_transcr);
            if let Some(transcript_var) = self.find_var(n_transcr) {
                let typ = node.op().expect("Transcript node must have op").typ();
                let mut new_node = node.clone();
                if let Node::Transcr(op, _) = &mut new_node {
                    *op = GOp::var(&transcript_var, n_input, typ);
                }
                let new_idx = verifier.add_node(new_node);
                verifier.add_edge(n_input, new_idx, Dep::data());
                node_map_self.insert(n_transcr, new_idx);
            } else {
                node_map_self.insert(n_transcr, n_input);
            }
        }

        // Add the verifier nodes, start with the verifier assertion
        let n_check = self.find_check().expect("No verifier assertion found");
        let mut worklist = vec![n_check];

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
                if r.node() == self.input_node() {
                    if let Some(r_var) = r.var() {
                        let is_private_input = self.args().iter()
                            .any(|a| a.var().as_ref() == Some(&r_var) && a.is_private());
                        if is_private_input {
                            return Err(GraphError::private_node_in_verifier(&op, &r));
                        }
                    }
                }
            }

            // Add node to prover graph
            let new_node = verifier.add_node(self[n].clone());
            node_map_self.insert(n, new_node);

            // Add parent neighbors to worklist
            for e in self.0.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                if !node_map_self.contains_key(&e.source()) {
                    debug!("Adding parent {} of {} to worklist", self[e.source()].drop_annotation(), self[n].drop_annotation());
                    worklist.push(e.source());
                }
            }
        }

        // Add edges to prover graph using the mapped node indices
        for edge_ref in self.0.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = edge_ref.weight().clone();

            if let Some(new_node) = node_map_self.get(&old_target_idx) {
                if verifier[*new_node].is_input() {
                    continue;
                }
                if non_challenge_transcripts.contains(&old_target_idx) && edge_ref.weight().is_data() {
                    continue;
                }
            }
            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map_self.get(&old_source_idx), node_map_self.get(&old_target_idx))
            {
                verifier.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }
        Ok(verifier.map_node_indices(&|n| node_map_self[&n]))
    }

    /// Get the verifier assertion, a check node with no outgoing edges
    pub fn find_check(&self) -> Option<NodeIndex> {
        self.node_indices()
            .find_map(|n| match self[n] {
                Node::Op(Op::Check(_), _)
                | Node::Transcr(Op::Check(_), _) if self.nodes_from(n).count() == 0 => Some(n),
                _ => None
            })
    }

    pub fn nodes_from(&self, n: NodeIndex) -> Neighbors<'_, Dep, u32> {
        self.0.neighbors_directed(n, Direction::Outgoing)
    }

    pub fn nodes_to(&self, n: NodeIndex) -> Neighbors<'_, Dep, u32> {
        self.0.neighbors_directed(n, Direction::Incoming)
    }

    pub fn erase_ann(self) -> UDag<C> {
        Dag(self.0.map(
            |_, node|
                match node {
                    Node::Inp(a, b) => Node::Inp(a.clone(), b.clone()),
                    Node::Rel(a, b) => Node::Rel(a.clone(), b.clone()),
                    Node::Op(op, _) => Node::Op(op.clone(), Nothing),
                    Node::Transcr(op, _) => Node::Transcr(op.clone(), Nothing),
                },
            |_, e| e.clone()))
    }

    /// Join two DAGs into one
    /// WARNING: This function does not remap Refs, so it is not safe to use in general.
    pub fn combine_dag(&self, other: &Self) -> Self where A: Clone {
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
            if let Some(weight) = self.0.node_weight(old_node_idx) {
                let new_node_idx = combined_graph.add_node(weight.clone());
                node_map_self.insert(old_node_idx, new_node_idx);
            }
        }

        // Add nodes from other and populate node_map_other
        for old_node_idx in other.node_indices() {
            if let Some(weight) = other.0.node_weight(old_node_idx) {
                let new_node_idx = combined_graph.add_node(weight.clone());
                node_map_other.insert(old_node_idx, new_node_idx);
            }
        }

        // Add edges from self using the mapped node indices
        for edge_ref in self.0.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = edge_ref.weight().clone();

            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map_self.get(&old_source_idx), node_map_self.get(&old_target_idx))
            {
                combined_graph.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }

        // Add edges from other using the mapped node indices
        for edge_ref in other.0.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = edge_ref.weight().clone();

            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map_other.get(&old_source_idx), node_map_other.get(&old_target_idx))
            {
                combined_graph.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }

        Dag(combined_graph)
    }
}

/// Write graphs with string annotations to PDF
impl<C: ArkConfig> WritePdf for Dag<C, String> {
    /// Write graph to PDF
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        // Write graphviz file
        let fdot: String = format!("{}.dot", filename.to_string());
        // Remove old file if there
        std::fs::remove_file(&fdot).ok();

        // Create graphviz object
        let graphviz =  Dot::with_attr_getters(
                &self.0,
                &[],
                &|_, e|
                        match e.weight().0 {
                            DepType::Data => "color = \"black\"",
                            DepType::Transcript => "color = \"red\"",
                        }.to_string(),
                &|_, n|
                        match n.1 {
                            Node::Inp(_, _) => "shape = \"box\"".to_string(),
                            Node::Rel(_, _) => "shape = \"note\"".to_string(),
                            Node::Transcr(_, _) => "color = \"red\"".to_string(),
                            _ => "shape = \"ellipse\"".to_string(),
                        }.to_string()
            );

        // Write to file
        std::fs::write(fdot.clone(), graphviz.to_string())?;

        let fpdf: String = format!("{}.pdf", filename.to_string());

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
        debug!("Wrote {:?}", std::fs::canonicalize(PathBuf::from(fpdf.clone())));
        Ok(())
    }
}

impl<C: ArkConfig> WritePdf for UDag<C> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, _| "".to_string()).write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for QDag<C> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, q| q.to_string()).write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for DQDag<C> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, (q, d)| format!("{} {}", q, d)).write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for Dags<C, String> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        let mut joined_graph = Dag::new();
        for g in self.0.iter() {
            joined_graph = joined_graph.combine_dag(g);
        }
        joined_graph.write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for UDags<C> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, _| "".to_string()).write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for QDags<C> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, q| q.to_string()).write_pdf(filename)
    }
}

impl<C: ArkConfig> WritePdf for DQDags<C> {
    fn write_pdf<'a, 'b>(&'a self, filename: &'b str) -> std::io::Result<()> {
        self.map_annotations(&|_, (q, d)| format!("{} {}", q, d)).write_pdf(filename)
    }
}

/// A collection of DAGs
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

    /// A protocol has a verifier assertion
    pub fn get_proto(&self, name: &String) -> Option<&Dag<C, A>> {
        self.protocols().into_iter().find(|g| 
            if let Some(v) = g[g.input_node()].name() {
                &v.0 == name
            } else {
                false
            })
    }

    pub fn protocols(&self) -> Vec<&Dag<C, A>> {
        self.0.iter().filter(|g| g.find_check().is_some()).collect()
    }

    pub fn functions(&self) -> Vec<&Dag<C, A>> {
        self.0.iter().filter(|g| !g.find_check().is_some()).collect()
    }

    /// Annotate all graphs using function [f]
    pub fn map_annotations<B, F: Fn(&GOp<C>, &A) -> B>(&self, f: &F) -> Dags<C, B> {
        Dags(self.0.iter().map(|g| g.map_annotations(f)).collect())
    }
}

/// A collection of DAGs without annotations
impl<C: ArkConfig> UDags<C> {
    /// Create a collection of Dags from a module
    pub fn from_module(m: CModule) -> Result<Self, GraphError> {
        let mut gs = UDags::new();

        let fctx =
            m.iter().map(|(sig, body)|
                (sig.clone(), body.clone())).collect::<Ctx<CSig, CBody>>();

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

/// Constructors for graphs
impl<C: ArkConfig> UDag<C> {
    /// Add a new top-level expression to the graph
    fn add_top_exp(&mut self, exp: CExp, start: &mut NodeIndex,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, GOp<C>>) -> Result<(), GraphError> {
        debug!("Adding top-level expression: {:?}", exp);
        let op = self.add_exp(exp, start, DepType::Data, &kctx, &fctx, &vctx, &vars)?;
        if !matches!(op, GOp::Ref(Ref::Node(_), _)) {
            let nr = self.add_node(Node::ret(&op));
            self.add_edges(DepType::Data, nr, op);
        };
        Ok(())
    }

    /// Add a new declaration to the graph
    fn add_decl(&mut self, sig: CSig, body: CBody, fctx: &Ctx<CSig, CBody>) -> Result<(), GraphError> {
        // Kind context
        let kctx = sig.typevars.to_ctx();
        // Add arguments to [vctx] and [vars]
        let mut vctx = Ctx::new();

        // Cast the signature to a arguments and insert to [start] node
        let asig = sig.args
            .iter()
            .map(|arg|
                PRef::from_arg(arg, NodeIndex::new(0), &kctx).ok_or_else(|| {
                    TypeError::decl(&sig.name,
                        TypeError::ark(&kctx, &vctx, &CExp::var(&arg.id), &arg.typ))
                })
            ).collect::<Result<Vec<PRef>, _>>()?;

        // Add arguments to type and fft contexts
        let mut atyps = Ctx::new();
        for Arg { id, typ, .. } in sig.args.iter() {
            let at = ATyp::from_ctyp(typ, &kctx).ok_or_else(|| {
                TypeError::decl(&sig.name,
                    TypeError::ark(&kctx, &vctx, &CExp::var(id), typ))
            })?;
            atyps.insert(id, &at);
            vctx.insert(id, typ);
        }

        // Typecheck the body with the type signature
        body.typecheck(sig.clone(), &fctx.keys())?;

        // Add the body to the Graph
        match body {
            CBody::Proto { body, relation } => {
                debug!("Adding proto: {:?}", sig);
                // Start node
                let mut start = self.add_node(Node::inp(sig.name.clone(), asig.clone()));
                let vars =
                    atyps.iter().map(|(id, typ)| (id.clone(), GOp::var(id, start, typ.clone()))).collect();
                self.add_top_exp(body, &mut start, &kctx, &fctx, &vctx, &vars)?;
                // Relation start
                start = self.add_node(Node::rel(sig.name.clone(), asig));
                let vars =
                    atyps.iter().map(|(id, typ)| (id.clone(), GOp::var(id, start, typ.clone()))).collect();
                self.add_top_exp(relation, &mut start, &kctx, &fctx, &vctx, &vars)?;
            },
            CBody::Func { body } => {
                let mut start = self.add_node(Node::inp(sig.name.clone(), asig));
                let vars =
                    atyps.iter().map(|(id, typ)| (id.clone(), GOp::var(id, start, typ.clone()))).collect();
                self.add_top_exp(body, &mut start, &kctx, &fctx, &vctx, &vars)?;
            }
        }

        Ok(())
    }

    /// Variables to operations by lookup in [vars]
    fn op_from_var(id: &Vid, vars: &Ctx<Vid, GOp<C>>) -> Result<GOp<C>, GraphError> {
        let nop = vars.get(&id).ok_or_else(|| GraphError::var_not_found(&id))?;
        match nop {
            GOp::Ref(Ref::Node(n), typ) => Ok(GOp::Ref(Ref::Var(id.clone(), *n), typ.clone())),
            op => Ok(op.clone())
        }
    }

    /// Convert a Fun expression body to a PolyVariant
    /// Only polynomial operations (Add, Sub, Mul with scalars, Var, Lit) are allowed
    fn exp_to_poly_variant(
        exp: &CExp,
        vars: &[Vid],
        var_map: &HashMap<Vid, usize>
    ) -> Result<PolyVariant<C::F>, GraphError> {
        use ark_ff::{Zero, One};
        
        match exp {
            CExp::Lit(n) => {
                // Scalar constant
                let scalar = C::F::from(*n as u64);
                Ok(PolyVariant::from_scalar(scalar))
            },
            CExp::Var(vid) => {
                // Check if this is a bound variable
                if let Some(&var_idx) = var_map.get(vid) {
                    // Create a polynomial with variable
                    if vars.len() == 1 {
                        // Univariate: create polynomial [0, 1] representing x
                        let poly = DensePolynomial::from_coefficients_vec(vec![C::F::zero(), C::F::one()]);
                        Ok(PolyVariant::DenseUni(poly))
                    } else {
                        // Multilinear: create a basis polynomial
                        let num_vars = vars.len();
                        let mut evals = vec![C::F::zero(); 1 << num_vars];
                        // Set evaluation at the point corresponding to this variable
                        for i in 0..(1 << num_vars) {
                            if (i >> var_idx) & 1 == 1 {
                                evals[i] = C::F::one();
                            }
                        }
                        let mle = DenseMultilinearExtension::from_evaluations_vec(num_vars, evals);
                        Ok(PolyVariant::DenseMle(mle))
                    }
                } else {
                    Err(GraphError::NonPolynomialFun(format!("Unbound variable {} in Fun expression", vid)))
                }
            },
            CExp::Bin(BinOp::Add, box a, box b) => {
                let pa = Self::exp_to_poly_variant(a, vars, var_map)?;
                let pb = Self::exp_to_poly_variant(b, vars, var_map)?;
                pa.poly_add(&pb).map_err(|e| GraphError::NonPolynomialFun(format!("Add failed: {}", e)))
            },
            CExp::Bin(BinOp::Sub, box a, box b) => {
                let pa = Self::exp_to_poly_variant(a, vars, var_map)?;
                let pb = Self::exp_to_poly_variant(b, vars, var_map)?;
                pa.poly_sub(&pb).map_err(|e| GraphError::NonPolynomialFun(format!("Sub failed: {}", e)))
            },
            CExp::Bin(BinOp::Mul, box a, box b) => {
                let pa = Self::exp_to_poly_variant(a, vars, var_map)?;
                let pb = Self::exp_to_poly_variant(b, vars, var_map)?;
                pa.poly_mul(&pb).map_err(|e| GraphError::NonPolynomialFun(format!("Mul failed: {}", e)))
            },
            _ => Err(GraphError::NonPolynomialFun(format!("Unsupported operation in Fun expression: {:?}", exp)))
        }
    }

    /// Add an expression [exp] to the graph
    fn add_exp(&mut self,
        exp: CExp,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, GOp<C>>) -> Result<GOp<C>, GraphError> {
        debug!("Adding expressions: {:?}", exp);
        // Type inference for [self]
        let typ = exp.infer(kctx, &fctx.keys(), vctx)?;
        debug!("Type of expression: {:?}", typ);
        // Convert [CExp] to [Op] while creating the graph
        match exp.clone() {
            // Literals get appended to the last node [self.it]
            CExp::Lit(n) =>
                Ok(GOp::Value(Value::Index(n))),

            CExp::Bool(b) =>
                Ok(GOp::Value(Value::Bool(b))),

            // Variables are edges, no new nodes are added
            CExp::Var(id) => Self::op_from_var(&id, vars),

            CExp::Eval(box p, box x) => {
                let vp = self.add_exp(p, transcr, edge_type, kctx, fctx, vctx, vars)?;
                let vx = self.add_exp(x, transcr, edge_type, kctx, fctx, vctx, vars)?;

                let eval_op = GOp::eval(vp, vx);
                
                Ok(eval_op)
            },

            CExp::Poly(box v) => {
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;

                let npoly = self.add_node(Node::poly(&child));

                self.add_edges(edge_type, npoly, child);

                Ok(GOp::underscore(npoly, ATyp::from_ctyp(&typ, kctx).ok_or_else( || {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },

            CExp::Coef(box v) => {
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;

                let npoly = self.add_node(Node::coef(&child));

                self.add_edges(edge_type, npoly, child);

                Ok(GOp::underscore(npoly, ATyp::from_ctyp(&typ, kctx).ok_or_else( || {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },

            // Create a new [ifft], [fft] or [mle] node
            CExp::Ifft(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let nifft = self.add_node(Node::ifft(&child));

                // Add edge from [nifft] to [child]
                self.add_edges(edge_type, nifft, child);

                Ok(GOp::underscore(nifft, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },
            CExp::Fft(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let nfft = self.add_node(Node::fft(&child));

                // Add edge from [nifft] to [child]
                self.add_edges(edge_type, nfft, child);

                Ok(GOp::underscore(nfft, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },

            // Create a new [vec] value
            CExp::Vec(vs) =>
                Ok(GOp::vec(vs.0.traverse1(&mut |v|
                            self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars))?)),


            // MLE is a noop?
            // CExp::Mle(box inner) => self.add_exp(inner, transcr, edge_type, kctx, fctx, vctx, vars),
            CExp::Mle(box v) => {
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;

                let nmle = self.add_node(Node::mle(&child));

                self.add_edges(edge_type, nmle, child);

                Ok(GOp::underscore(nmle, ATyp::from_ctyp(&typ, kctx).ok_or_else( || {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },

            // Billinear pairing
            CExp::Pair(box a, box b) => {
                a.infer(kctx, &fctx.keys(), vctx)?;
                b.infer(kctx, &fctx.keys(), vctx)?;

                let va = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                let vb = self.add_exp(b, transcr, edge_type, kctx, fctx, vctx, vars)?;

                let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;

                Ok(GOp::pair(va, vb, atyp))
            },
            // Create a new [bin] node
            CExp::Bin(op, box a, box b) => {
                a.infer(kctx, &fctx.keys(), vctx)?;
                b.infer(kctx, &fctx.keys(), vctx)?;

                // Add children first
                let vl = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                let vr = self.add_exp(b, transcr, edge_type, kctx, fctx, vctx, vars)?;

                // Convert type [typ] to [ATyp]
                let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;

                let bop = GOp::bin(op, vl.clone(), vr.clone(), atyp.clone());

                // Maybe there will be no node
                if let GOp::Bin(op, box vl, box vr, atyp) = bop {
                    // Add new node
                    let nbin = self.add_node(Node::bin(op, &vl, &vr, &atyp));

                    // Add edges from [nbin] to [vl] and [vr]
                    self.add_edges(edge_type, nbin, vl);
                    self.add_edges(edge_type, nbin, vr);
                    Ok(GOp::underscore(nbin, atyp))
                } else {
                    Ok(bop)
                }
            },

            // Create a [range] value, no new nodes added
            CExp::Range(r) => Ok(GOp::range(r)),

            CExp::Map(box l, x, box e) => {
                // Type of [e]
                let te = e.infer(kctx, &fctx.keys(), vctx)?;

                // Op for [e]
                let oe = self.add_exp(e, transcr, edge_type, kctx, fctx, vctx, vars)?;

                // Get the size [n] from type [te]
                let (ie, n) = te.into_vec();

                // Ops are saved here
                let mut res = Vec::with_capacity(n);
                // Create operations
                for i in 0..n {
                    // Add oe[i] to vars and vctx
                    let mut vars = vars.clone();
                    let mut vctx = vctx.clone();
                    vars.insert(&x, &GOp::ram(oe.clone(), GOp::index(i)));
                    vctx.insert(&x, &ie);
                    // Add subexpression
                    let ol = self.add_exp(l.clone(), transcr, edge_type, kctx, fctx, &vctx, &vars)?;
                    res.push(ol);
                }
                Ok(GOp::vec(res))
            },

            CExp::Reduce(op, box v) => {
                // Type of [v]
                let tv = v.infer(kctx, &fctx.keys(), vctx)?;
                let atv = ATyp::from_ctyp(&tv, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &tv))
                })?;

                // Get the size [n] from type [tv]
                let (_, n) = atv.into_vec();

                let mut redexp = CExp::ram(v.clone(), CExp::lit(0));
                for i in 1..n {
                    redexp = CExp::bin(op, redexp, CExp::ram(v.clone(), CExp::lit(i)));
                }
                self.add_exp(redexp, transcr, edge_type, kctx, fctx, vctx, vars)
            },
            CExp::Ram(box a, box b) => {
                // Add children
                let oa = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                let ob = self.add_exp(b, transcr, edge_type, kctx, fctx, vctx, vars)?;
                Ok(GOp::ram(oa, ob))
            },
            CExp::Challenge(_, non_zero) => {
                let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;
                let nchallenge = self.add_node(Node::challenge(&at, non_zero));
                // Add transcript edge to [nchallenge]
                self.add_edge(*transcr, nchallenge, Dep::transcript());
                // Update transcript node
                *transcr = nchallenge;

                // If the challenge is non-zero, add a prover assertion
                Ok(GOp::underscore(nchallenge, at))
            },
            CExp::Random(_, non_zero) => {
                let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;
                let nrand = self.add_node(Node::random(&at, non_zero));
                Ok(GOp::underscore(nrand, at))
            },
            CExp::App(fid, params) => {
                // type inference for each parameter
                let param_types: CTyps = params.iter()
                        .map(|p| p.infer(kctx, &fctx.keys(), vctx))
                        .collect::<Result<_, _>>()?;

                // Is it a polynomial, MLE, or a function?
                match vctx.get(&fid) {
                    Some(CTyp::Poly(tbase, 1, n)) => {
                        // It is a univariate polynomial
                        let k = kctx.get(&tbase).unwrap();

                        // Only field elements can be evaluated and only 1 argument can be given
                        assert!(k.is_scalar());
                        assert_eq!(param_types.len(), 1);

                        // Add the argument to the graph
                        let x_pow = CExp::vec(
                            (0..*n).map(|i| CExp::pow(params[0].clone(), i.into()))
                            .collect());

                        // Polynomial evaluation by dot-product of ifft with [x_pow]
                        let dot_exp =
                            CExp::bin(BinOp::Dot, CExp::var(&fid), x_pow);
                        self.add_exp(dot_exp, transcr, edge_type, kctx, fctx, vctx, vars)
                    },
                    Some(CTyp::Poly(tbase, n, 1)) => {
                        // It is a multilinear extension
                        let k = kctx.get(&tbase).unwrap();

                        // Only field elements can be evaluated and only 1 argument can be given
                        assert!(k.is_scalar());
                        assert_eq!(param_types.len(), 1);

                        // https://github.com/microsoft/Nova/blob/ad4d77ac89d6bbe9ef943056806e65ceb4ba3b3e/src/spartan/polys/multilinear.rs#L58
                        let mle_l = CExp::ram(
                            CExp::var(&fid),
                            CExp::range(CRange::new(0, n-1))
                        );

                        let mle_r = CExp::ram(
                            CExp::var(&fid),
                            CExp::range(CRange::new(n-1, *n))
                        );

                        // mle_l + (mle_r - mle_l) * params[0]
                        let fold = CExp::add(mle_l.clone(),
                            CExp::mul(
                                params[0].clone(),
                                CExp::sub(mle_r, mle_l)
                            )
                        );

                        self.add_exp(fold, transcr, edge_type, kctx, fctx, vctx, vars)
                    },
                    _ => {
                        // It is a function. Find all matching functions in function context [fctx]
                        let matching_sigs = fctx.iter().filter_map(|(sig, body)|
                            // If the function name matches
                            if sig.name == fid {
                                    // The argument types must match the parameter types
                                    let (sig, subs) = sig.clone()
                                        .unify(&param_types, &kctx)
                                        .ok()?;
                                    // Return new signature
                                    Some((sig, body, subs))
                                } else {
                                    None
                                }
                        ).collect::<Vec<_>>();

                        // Only one function shoud match (enforced by the type system)
                        assert_eq!(matching_sigs.len(), 1);
                        let triple = matching_sigs[0].clone();
                        let sig = triple.0;
                        let mut body = triple.1.clone();
                        let subs = triple.2;
                        subs.tid_subst(&mut body);

                        // First add the arguments to the graph
                        let oparams: Vec<GOp<C>> = params.into_iter()
                           .map(|p| self.add_exp(p, transcr, edge_type, kctx, fctx, vctx, vars))
                           .collect::<Result<_, _>>()?;

                        // Create a new context
                        let vctx = sig.args.to_ctx();
                        let vars =
                            sig.args.iter().zip(oparams.iter())
                            .map(|(arg, op)| (arg.id.clone(), op.clone())).collect::<Ctx<Vid, _>>();

                        // Add the body to the graph
                        self.add_exp(body.body(), transcr, edge_type, kctx, fctx, &vctx, &vars)
                    }
                }
            },
            CExp::Let(Some(id), box l, box r) => {
                // Infer the type of [l]
                let tl = l.infer(kctx, &fctx.keys(), vctx)?;
                // Add left-hand side as node
                let nl = self.add_exp(l, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add [id] to the variable context
                let mut vctx = vctx.clone();
                vctx.insert(&id, &tl);
                let mut vars = vars.clone();
                vars.insert(&id, &nl);
                // Add right-hand side as Node
                self.add_exp(r, transcr, edge_type, kctx, fctx, &vctx, &vars)
            },
            CExp::Let(None, box l, box r) => {
                self.add_exp(l, transcr, edge_type, kctx, fctx, vctx, vars)?;
                self.add_exp(r, transcr, edge_type, kctx, fctx, vctx, vars)
            },
            CExp::Log(id, box l, box r) => {
                // Infer the type of [l]
                let tl = l.infer(kctx, &fctx.keys(), vctx)?;
                // Add left-hand side as node
                let ol = self.add_exp(l, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Record transcript interaction
                match ol {
                    GOp::Ref(Ref::Node(n) | Ref::Var(_, n), _) => {
                        self.add_edge(*transcr, n, Dep::transcript_var(id.clone()));
                        self.0.node_weight_mut(n).unwrap().set_transcript();
                        *transcr = n;
                    },
                    _ => {
                        // Add new node
                        let nl = self.add_node(Node::transcr(&ol));
                        self.add_edge(*transcr, nl, Dep::transcript_var(id.clone()));
                        *transcr = nl;
                    }
                }
                // Add [id] to the variable context
                let mut vctx = vctx.clone();
                vctx.insert(&id, &tl);
                let mut vars = vars.clone();
                vars.insert(&id, &ol);
                // Add right-hand side as Node
                self.add_exp(r, transcr, edge_type, kctx, fctx, &vctx, &vars)
            },
            CExp::Assert(box a) => {
                let oa = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let nassert = self.add_node(Node::check(&oa));
                // Add edges
                self.add_edges(edge_type, nassert, oa);
                Ok(GOp::underscore(nassert, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?))
            },
            CExp::Verify(box a) => {
                let oa = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let nverify = self.add_node(Node::check(&oa));
                self.add_edges(edge_type, nverify, oa);
                Ok(GOp::underscore(nverify, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?))
            },
            CExp::Fun(fun_vars, box body) => {
                // Convert the Fun expression body to a PolyVariant
                let var_map: HashMap<Vid, usize> = fun_vars.iter()
                    .enumerate()
                    .map(|(i, v)| (v.clone(), i))
                    .collect();
                
                let poly = Self::exp_to_poly_variant(&body, &fun_vars, &var_map)?;
                
                // Create a Value::Poly from the PolyVariant wrapped in VirtualPolynomial
                let poly_value = Value::Poly(VirtualPolynomial::from_poly(poly));
                
                Ok(GOp::Value(poly_value))
            },
            CExp::Record(fields) => {
                // For records, we add each field to the graph and create a Record operation
                let mut field_ops = Ctx::new();
                
                for (field_name, field_exp) in fields.iter() {
                    let field_op = self.add_exp(field_exp.clone(), transcr, edge_type, kctx, fctx, vctx, vars)?;
                    field_ops.insert(field_name, &field_op);
                }
                
                // Return a Record operation with named fields
                Ok(GOp::Record(field_ops))
            },
            CExp::Proj(box record_exp, field_name) => {
                // For projection, we need to extract the field from the record
                // Check if the record expression is a Record literal
                match record_exp {
                    CExp::Record(fields) => {
                        let field_exp = fields.get(&field_name)
                            .ok_or_else(|| {
                                let mut field_types = Ctx::new();
                                for (name, exp) in fields.iter() {
                                    if let Ok(typ) = exp.infer(kctx, &fctx.keys(), vctx) {
                                        field_types.insert(name, &typ);
                                    }
                                }
                                GraphError::Type(TypeError::field_not_found(
                                    kctx, vctx, &CExp::Record(fields.clone()), field_name.as_str(), &field_types
                                ))
                            })?;
                        
                        // Add the field expression to the graph
                        self.add_exp(field_exp.clone(), transcr, edge_type, kctx, fctx, vctx, vars)
                    },
                    CExp::Var(id) => {
                        let id_clone = id.clone();
                        let record_op = vars.get(&id_clone)
                            .ok_or_else(|| GraphError::Type(TypeError::exp(kctx, vctx, &CExp::Var(id_clone.clone()))))?;
                        
                        // Try to infer the record type to verify the field exists
                        let record_typ = CExp::Var(id_clone.clone()).infer(kctx, &fctx.keys(), vctx)?;
                        
                        match &record_typ {
                            CTyp::Record(fields) => {
                                // Verify the field exists and get its type
                                let field_typ_ctyp = fields.get(&field_name)
                                    .ok_or_else(|| GraphError::Type(TypeError::field_not_found(
                                        kctx, vctx, &CExp::Var(id_clone.clone()), field_name.as_str(), fields
                                    )))?;
                                
                                // Extract the field from the record operation
                                match record_op {
                                    GOp::Record(record_fields) => {
                                        // Direct field access from Record operation
                                        record_fields.get(&field_name)
                                            .ok_or_else(|| GraphError::Type(TypeError::field_not_found(
                                                kctx, vctx, &CExp::Var(id_clone.clone()), field_name.as_str(), fields
                                            )))
                                            .map(|op| op.clone())
                                    },
                                    GOp::Ref(Ref::Var(vid, node), _op_typ) => {
                                        let field_typ_atyp = ATyp::from_ctyp(field_typ_ctyp, kctx)
                                            .ok_or_else(|| GraphError::Type(TypeError::ark(
                                                kctx, vctx, &CExp::Var(id_clone.clone()), field_typ_ctyp
                                            )))?;
                                        
                                        // The field is accessed via projection, so we return a Ref with the field type
                                        Ok(GOp::Ref(Ref::Var(vid.clone(), *node), field_typ_atyp))
                                    },
                                    _ => {
                                        Err(GraphError::Type(TypeError::not_a_record(
                                            kctx, vctx, &CExp::Var(id_clone.clone()), &record_typ
                                        )))
                                    }
                                }
                            }
                            _ => {
                                Err(GraphError::Type(TypeError::not_a_record(
                                    kctx, vctx, &CExp::Var(id_clone.clone()), &record_typ
                                )))
                            }
                        }
                    },
                    _ => {
                        // For other expressions, try to infer the record type
                        let record_typ = record_exp.infer(kctx, &fctx.keys(), vctx)?;
                        
                        match record_typ {
                            CTyp::Record(fields) => {
                                // Get the field type
                                let _field_typ = fields.get(&field_name)
                                    .ok_or_else(|| GraphError::Type(TypeError::field_not_found(
                                        kctx, vctx, &record_exp, field_name.as_str(), &fields
                                    )))?;
                                
                                // For complex expressions, we'd need to evaluate them first
                                // For now, return an error indicating this isn't fully supported
                                Err(GraphError::Type(TypeError::next(
                                    TypeError::exp(kctx, vctx, &exp),
                                    TypeError::ark(kctx, vctx, &exp, &typ)
                                )))
                            },
                            _ => {
                                Err(GraphError::Type(TypeError::not_a_record(
                                    kctx, vctx, &record_exp, &record_typ
                                )))
                            }
                        }
                    }
                }
            },
            CExp::SetRecord(box record_exp, field_name, box value_exp) => {
                // Build new record as expression: all fields from record_exp, with field_name replaced by value_exp
                let record_typ = record_exp.infer(kctx, &fctx.keys(), vctx)?;
                let CTyp::Record(typ_fields) = &record_typ else {
                    return Err(GraphError::Type(TypeError::not_a_record(
                        kctx, vctx, &record_exp, &record_typ
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
                self.add_exp(new_record_exp, transcr, edge_type, kctx, fctx, vctx, vars)
            }
        }
    }
}

impl<C: ArkConfig, A> Index<NodeIndex> for Dag<C, A> {
    type Output = Node<C, A>;
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.0[index]
    }
}

impl<C: ArkConfig, A> std::ops::IndexMut<NodeIndex> for Dag<C, A> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<C: ArkConfig, A> Index<usize> for Dags<C, A> {
    type Output = Dag<C, A>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

#[cfg(test)] use share::unwrap;
#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn graph_sum() {
    let ex = r#"
        fn sum<N: 1..4, F: Field>(public a: [F; 2^N]) -> F {
            sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])
        }

        fn sum<F: Field>(public a: [F; 1]) -> F {
           a[0]
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    assert_eq!(m.len(), 4);
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_sum").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
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
            verify(a * s == b * x[3]);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    // Output graph
    gs.write_pdf("graph_foo").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn graph_poly() {
    let ex = r#"
        proto poly_mul<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 4>) where a == a {
            let r = random<F*>;
            let p = a * b;
            verify(p(r) == (a(r) * b(r)));
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_poly").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn graph_reduce() {
    let ex = r#"
        fn reduction_foo<F: Field>(public a: [F; 10]) -> F {
            reduce(+, a)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    debug!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_reduce").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
