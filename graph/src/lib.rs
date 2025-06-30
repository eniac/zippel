#![feature(box_patterns)]
#![feature(trait_alias)]
mod node;
mod dep;
mod op;
pub mod analyses;
pub mod scheduler;
pub mod pref;
pub mod domain_seperator;

pub use op::{Ref, Op, GOp};
pub use node::Node;
pub use dep::{DepType, Dep};
use petgraph::Directed;
pub use pref::{PRef, LexTerm};
pub use analyses::StaticAnalysis;

use backend::{ArkConfig, Value, ATyp};
use share::{traversal::ToTraversal1, Set, Ctx};
use lang::ast::{CModule, BinOp, CExp, Arg, CSig, CBody};
use lang::id::{Fresh, Tid, Vid};
use lang::typ::{Qualifier, Distribution, Nothing, CTyp, CTyps, Kind};
use lang::typ::range::CRange;
use lang::typ::infer::{Typeable, TypeError};

use thiserror::Error;
use petgraph::{dot::Dot, graph::{EdgeReference, NodeIndex, NodeIndices, Neighbors}, visit::EdgeRef, Direction, Graph};
use std::process::Command;
use std::fmt;
use std::ops::Index;
pub use std::collections::HashMap;
use std::path::PathBuf;

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
    #[error("Relation not found in {0}")]
    RelationNotFound(Vid),
    #[error("Private node found in verifier: {0}: {1}")]
    PrivateNodeInVerifier(String, String),
    #[error("{0}\n\n{1}")]
    Next(Box<GraphError>, Box<GraphError>),
    #[error(transparent)]
    Type(#[from] TypeError)
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
            println!("Edge from {:?} to {:?}", source, target);
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

    fn add_edges(&mut self, edge_type: DepType, sink: NodeIndex, source: GOp<C>) {
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
    fn add_node(&mut self, node: Node<C, A>) -> NodeIndex {
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

    pub fn neighbors_directed(&self, node_index: NodeIndex, direction: Direction) -> Neighbors<Dep, u32> {
        self.0.neighbors_directed(node_index, direction)
    }

    pub fn transcript_edge<'a>(&'a self, n: NodeIndex, dir: Direction) -> Option<EdgeReference<'a, Dep>> {
        self.0.edges_directed(n, dir)
            .find(|edge| edge.weight().is_transcript())
    }

    /// Get all transcript node from the graph
    pub fn transcript_nodes(&self) -> Vec<NodeIndex> {
        self.0.node_indices()
            .filter(|n| self[*n].is_transcript())
            .collect()
    }

    /// Get the prover graph, by reachability analysis starting from the transcript nodes
    pub fn get_prover(&self) -> (Dag<C, A>, HashMap<NodeIndex, NodeIndex>) where A: Clone {
        let mut prover = Dag::new();
        // Add all nodes to the prover graph
        let mut worklist: Vec<NodeIndex> = self.transcript_nodes();

        let mut node_map_self = HashMap::<NodeIndex, NodeIndex>::new();

        // Add input node first, so it is NodeIndex::new(0)
        let n_input = prover.add_node(self[self.input_node()].clone());
        node_map_self.insert(self.input_node(), n_input);

        while let Some(n) = worklist.pop() {
            if node_map_self.contains_key(&n) {
                continue;
            }
            // Add node to prover graph
            let new_node = prover.add_node(self[n].clone());
            node_map_self.insert(n, new_node);

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
                (node_map_self.get(&old_source_idx), node_map_self.get(&old_target_idx))
            {
                prover.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }

        (prover.map_node_indices(&|n| {
            if let Some(new_node) = node_map_self.get(&n) {
                *new_node
            } else {
                println!("Node {:?} not found in node_map_self {}", n, self[n].drop_annotation());
                panic!("Node {:?} not found in node_map_self {}", n, self[n].drop_annotation());
            }
        }), node_map_self)
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

    pub fn process_op(op: GOp<C>, args_name: &Vec<String>) -> GOp<C> {
        match op {
            Op::Value(val) => {
                Op::Value(val)
            },
            Op::Ref(r, typ) => {
                let r_new = match r {
                    Ref::Node(n) => r,
                    Ref::Var(v, n) => {
                        match v {
                            Vid(v_string) => {
                                if args_name.contains(&v_string) {
                                    Ref::Var(Vid(v_string), n)
                                } else {
                                    Ref::Var(Vid(v_string + &format!("_{:?}", n)), n)
                                }
                            }
                        }
                    },
                };
                Op::Ref(r_new, typ)
            },
            Op::Bin(op, a, b, typ) => {
                let a_val: GOp<C> = Self::process_op(*a, args_name);
                let b_val: GOp<C> = Self::process_op(*b, args_name);
                Op::Bin(op, Box::new(a_val), Box::new(b_val), typ)
            },
            Op::Vec(vec) => {
                let value_vector: Vec<Op<C, Ref>> = vec.iter().map(|op| Self::process_op(op.clone(), args_name)).collect::<Vec<Op<C, Ref>>>();
                Op::Vec(value_vector)
            },
            Op::Ram(box v, box index_val) => {
                let v_val: Op<C, Ref> = Self::process_op(v, args_name);
                let index_val_value: Op<C, Ref> = Self::process_op(index_val, args_name);
                Op::Ram(Box::new(v_val), Box::new(index_val_value))
            }
            Op::Random(typ, val) => {
                Op::Random(typ, val)
            },
            Op::Challenge(typ, val) => {
                Op::Challenge(typ, val)
            },
            Op::Pair(a, b, typ) => {
                let a_val: GOp<C> = Self::process_op(*a, args_name);
                let b_val: GOp<C> = Self::process_op(*b, args_name);
                Op::Pair(Box::new(a_val), Box::new(b_val), typ) 
            },
            Op::Coef(a) => {
                let a_val: GOp<C> = Self::process_op(*a, args_name);
                Op::Coef(Box::new(a_val))
            },
            Op::Eval(a) => {
                let a_val: GOp<C> = Self::process_op(*a, args_name);
                Op::Eval(Box::new(a_val))
            },
            Op::Check(a) => {
                let a_val: GOp<C> = Self::process_op(*a, args_name);
                Op::Check(Box::new(a_val))
            }
        }
    }

    pub fn map_transcript_nodes(&mut self)  -> Dag<C, Nothing> {
        let args: Vec<PRef> = self.args().into_iter().collect::<Vec<_>>();
        let mut args_name = Vec::<String>::new();
        for arg in args {
            match arg.var() {
                Some(v) => {
                    match v {
                        Vid(v_string) => {
                            args_name.push(v_string);
                        }
                    }
                }
                None => {}
            }
        }
        println!("args_name: {:?}", args_name);
        Dag(self.0.map(
            |_, node|
                match node {
                    Node::Op(op, _) => Node::Op(Self::process_op(op.clone(), &args_name), Nothing),
                    Node::Transcr(op, _) => Node::Transcr(Self::process_op(op.clone(), &args_name), Nothing),
                    Node::Inp(a, b) => Node::Inp(a.clone(), b.clone()),
                    Node::Rel(a, b) => Node::Rel(a.clone(), b.clone()),
                },
                |_, e| e.clone()
        ))
    }

    /// Get the verifier graph, by reachability analysis starting from the verifier assertion
    /// and stopping at transcript nodes.
    pub fn get_verifier(&self) -> Result<Dag<C, A>, GraphError> where A: Clone {
        let mut verifier = Dag::new();

        // Rebuild the input node to take transcript arguments
        let mut args = self.args().into_iter().filter(|pr| pr.is_public()).collect::<Vec<_>>();
        let name = self.name();

        // Add the transcript nodes (public) to the arguments
        for node in self.transcript_nodes() {
            if let Some(transcript_var) = self.find_var(node) {
                if args.iter().any(|a| a.var() == Some(transcript_var.clone())) {
                    continue;
                }
                args.push(
                    PRef::from_var(transcript_var,
                        self.input_node(),
                        self[node].clone().into_op().typ(),
                        0,
                        Qualifier::Public,
                        Distribution::default()));
            } else {
                println!("No transcript var found for node: {}", node.index());
            }
        }
        // Associate old node indices with new node indices
        let mut node_map_self = HashMap::<NodeIndex, NodeIndex>::new();

        // Make new input node
        let n_input = verifier.add_node(Node::Inp(name, args));
        node_map_self.insert(self.input_node(), n_input);
        // Map all transcript arguments to to the new input node
        for n_transcr in self.transcript_nodes().into_iter() {
            node_map_self.insert(n_transcr, n_input);
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

            let op = self[n].clone().into_op();
            // Check if the node refers to a private argument, then it is a leak
            //for r in op.references() {
            //    if r.node() == self.input_node() {
            //        if args.iter().all(|a| a.var() != r.var()) {
            //            return Err(GraphError::private_node_in_verifier(&op, &r));
            //        }
            //    }
            // }

            // Add node to prover graph
            let new_node = verifier.add_node(self[n].clone());
            node_map_self.insert(n, new_node);

            // Add parent neighbors to worklist
            for e in self.0.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                if !node_map_self.contains_key(&e.source()) {
                    println!("Adding parent {} of {} to worklist", self[e.source()].drop_annotation(), self[n].drop_annotation());
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

        // Print success
        println!("Wrote {:?}", std::fs::canonicalize(PathBuf::from(fpdf.clone())));
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
    pub fn get_proto(&self, name: &Vid) -> Option<&Dag<C, A>> {
        self.protocols().into_iter().find(|g| g[g.input_node()].name() == Some(name))
    }

    /// A function has no verifier assertion
    pub fn get_function(&self, name: &Vid) -> Option<&Dag<C, A>> {
        self.functions().into_iter().find(|g| g[g.input_node()].name() == Some(name))
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

        for (sig, body) in m.into_iter() {
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

        // Add arguments to type and evaluation contexts
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

    /// Add an expression [exp] to the graph
    fn add_exp(&mut self,
        exp: CExp,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, GOp<C>>) -> Result<GOp<C>, GraphError> {
        println!("Testing");
        // Type inference for [self]
        let typ = exp.infer(kctx, &fctx.keys(), vctx)?;
        println!("Testing 2");
        // Convert [CExp] to [Op] while creating the graph
        match exp.clone() {
            // Literals get appended to the last node [self.it]
            CExp::Lit(n) =>
                Ok(GOp::Value(Value::Index(n))),

            CExp::Bool(b) =>
                Ok(GOp::Value(Value::Bool(b))),

            // Variables are edges, no new nodes are added
            CExp::Var(id) => Self::op_from_var(&id, vars),

            // Create a new [coef], [eval] or [mle] node
            CExp::Coef(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let ncoef = self.add_node(Node::coef(&child));

                // Add edge from [ncoef] to [child]
                self.add_edges(edge_type, ncoef, child);

                Ok(GOp::underscore(ncoef, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },
            CExp::Eval(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let neval = self.add_node(Node::eval(&child));

                // Add edge from [ncoef] to [child]
                self.add_edges(edge_type, neval, child);

                Ok(GOp::underscore(neval, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
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
            CExp::Mle(box inner) => self.add_exp(inner, transcr, edge_type, kctx, fctx, vctx, vars),

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
                let ta = a.infer(kctx, &fctx.keys(), vctx)?;
                let tb = b.infer(kctx, &fctx.keys(), vctx)?;

                // Convert polynomials to vectors
                match (&typ, ta, tb, op) {
                    // Polynomial multiplication and division
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), CTyp::Uni(_, r),
                        op @(BinOp::Mul | BinOp::Div)) => {
                        let mut ex_a = a.clone();
                        let mut ex_b = b.clone();
                        // Pad with zeroes
                        if &l < n {
                            ex_a = CExp::concat(a, CExp::zeroes(*n - l + 1));
                        }
                        if &r < n {
                            ex_b = CExp::concat(b, CExp::zeroes(*n - r + 1));
                        }
                        return self.add_exp(CExp::coef(CExp::bin(op, CExp::eval(ex_a), CExp::eval(ex_b))),
                                transcr, edge_type, kctx, fctx, vctx, vars);
                    },
                    // Polynomial remainder
                    (CTyp::Uni(_, _n), CTyp::Uni(_, _l), CTyp::Uni(_, _r), BinOp::Rem) =>
                        unimplemented!("Polynomial remainder"),
                    // Polynomial exponentiation
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), _, BinOp::Pow) => {
                        // Pad with zeroes
                        let ex = CExp::eval(CExp::concat(a, CExp::zeroes(*n - l)));
                        return self.add_exp(CExp::coef(CExp::pow(ex, b)),
                            transcr, edge_type, kctx, fctx, vctx, vars);
                    },
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), CTyp::Base(t), BinOp::Add) 
                    | (CTyp::Uni(_, n), CTyp::Base(t), CTyp::Uni(_, l), BinOp::Add)  
                    if (kctx.get(&t).unwrap().is_scalar()) 
                    => {
                        println!("adding a and b");
                        let zero_vec: lang::ast::Exp<usize> = CExp::zeroes(n - 1);
                        let b_vec = CExp::vec(vec![b.clone()]);
                        let vec_value = CExp::concat(b_vec, zero_vec);
                        return self.add_exp(CExp::add(a, vec_value), transcr, edge_type, kctx, fctx, vctx, vars);
                    },
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), CTyp::Base(t), BinOp::Sub) 
                    if (kctx.get(&t).unwrap().is_scalar()) 
                    => {
                        println!("subtracting a and b");
                        let zero_vec: lang::ast::Exp<usize> = CExp::zeroes(n - 1);
                        let b_vec = CExp::vec(vec![b.clone()]);
                        let vec_value = CExp::concat(b_vec, zero_vec);
                        println!("vec_value: {}", vec_value);
                        return self.add_exp(CExp::sub(a, vec_value), transcr, edge_type, kctx, fctx, vctx, vars);
                    },
                    _ => ()
                };

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
                    Some(CTyp::Uni(tbase, n)) => {
                        // It is a polynomial
                        let k = kctx.get(&tbase).unwrap();

                        // Only field elements can be evaluated and only 1 argument can be given
                        assert!(k.is_scalar());
                        assert_eq!(param_types.len(), 1);

                        // Add the argument to the graph
                        let x_pow = CExp::vec(
                            (0..*n).map(|i| CExp::pow(params[0].clone(), i.into()))
                            .collect());

                        // Polynomial evaluation by dot-product of coefficients with [x_pow]
                        let dot_exp =
                            CExp::bin(BinOp::Dot, CExp::var(&fid), x_pow);
                        self.add_exp(dot_exp, transcr, edge_type, kctx, fctx, vctx, vars)
                    },
                    Some(CTyp::Mle(tbase, n)) => {
                        // It is an MLE
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
                        let matching_sigs = fctx.iter().filter_map(|(sig, body)| {
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
                        }).collect::<Vec<_>>();

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
                    GOp::Ref(Ref::Node(n) | Ref::Var(_, n), _)=> {
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
        }
    }
}

impl<C: ArkConfig, A> Index<NodeIndex> for Dag<C, A> {
    type Output = Node<C, A>;
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.0[index]
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
#[cfg(test)] use crate::analyses::QualifierPropagation;
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
    println!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_sum").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
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
    println!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    // Output graph
    gs.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
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
    println!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_poly").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn graph_reduce() {
    let ex = r#"
        fn reduction_foo<F: Field>(public a: [F; 10]) -> F {
            reduce(+, a)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    gs.write_pdf("graph_reduce").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
