#![feature(box_patterns)]
mod node;
mod scope;
mod edge;
mod principal;

pub use node::{Op, Node, UNode, Value};
pub use edge::{Dependency, Edge};
pub use scope::{Scope, Scopes, ScopedVar};

use share::Ctx;
use lang::ast::{CExp, Arg, CSig, CBody};
use lang::id::{Vid, Tid, Fid};
use lang::typ::{CTyp, Nothing, Kind};
use lang::typ::infer::{Typeable, TypeError};

use thiserror::Error;
use petgraph::{dot::Dot, graph::NodeIndex, Direction, Graph};
use std::process::Command;
use std::fmt;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
pub struct DagBuilder<A> {
    g: Graph<Node<A>, Edge>,
    transcr: NodeIndex,
    it: NodeIndex,
    scope: Scopes,
    vctx: Ctx<Vid, CTyp>,
    vars: Ctx<ScopedVar, NodeIndex>
}


#[derive(Error, PartialEq, Debug)]
pub enum GraphError {
    #[error("Variable not found {0}")]
    VarNotFound(Vid),
    #[error("GraphError: Internal error, could not bind value {0} to node {1}")]
    BindValue(Value, UNode),
    #[error("{0}\n\n{1}")]
    Next(Box<GraphError>, Box<GraphError>),
    #[error(transparent)]
    Type(#[from] TypeError)
}

impl GraphError {
    pub fn next(e1: GraphError, e2: GraphError) -> Self {
        GraphError::Next(Box::new(e1), Box::new(e2))
    }
    pub fn var_not_found(vid: &Vid) -> Self {
        GraphError::VarNotFound(vid.clone())
    }
    pub fn bind_value(val: &Value, node: &UNode) -> Self {
        GraphError::BindValue(val.clone(), node.clone())
    }
}

/// Unannotated graph
pub type UDagBuilder = DagBuilder<Nothing>;

/// Create a graph
pub trait ToGraph {
    fn to_graph(&self, g: &mut UDagBuilder, kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>) -> Result<(), GraphError>;
}

impl UDagBuilder {
    /// Create a new graph
    pub fn new(sig: CSig) -> Self {
        // New graph
        let mut g = Graph::new();
        // New variable context
        let mut vars = Ctx::new();
        let mut vctx = Ctx::new();
        // Initial node is the function signature
        let it = g.add_node(Node::inp(sig));
        // Add arguments to [vctx]
        for Arg { qualifier, id, typ } in sig.args {
            vars.insert(&ScopedVar::singleton(sig, id), &it);
            vctx.insert(&id, &typ);
        }
        // New scope
        let scope = Scopes::from([Scope::Sig(sig)]);
        // Add empty transcript
        let transcr = g.add_node(Node::empty_transcript());
        DagBuilder { g, transcr, it, scope, vars, vctx }
    }
}

impl<A> DagBuilder<A> {
    /// Get the number of nodes in the graph
    pub fn node_count(&self) -> usize {
        self.g.node_count()
    }

    /// Edge deduplication
    fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Edge) {
        self.g.update_edge(source, sink, edge);
    }

    /// Write graph to PDF
    pub fn write_pdf<'a>(&self, filename: &str) -> std::io::Result<()>
    where
        A: Clone + fmt::Display
    {
        // Write graphviz file
        let fdot: String = format!("{}.dot", filename.to_string());
        // Create graphviz object
        let graphviz =  Dot::with_attr_getters(
                &self.g,
                &[],
                &|_, e|
                        match e.weight().dep {
                            Dependency::Data => "[color = \"black\"]",
                            Dependency::Transcript => "[color = \"red\"]",
                            Dependency::Implicit => "[color = \"blue\"]"
                        }.to_string(),
                &|_, _| String::new()
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
            .spawn()
            .expect("[dot] CLI failed to convert DAG to [pdf] file")
            .wait()?;

        // Remove DOT file
        std::fs::remove_file(fdot)?;

        // Print success
        println!("Wrote {}.pdf", filename);
        Ok(())
    }

    pub fn get_it(&mut self) -> &mut Node<A> {
        &mut self.g[self.it]
    }

    pub fn add_exp(&mut self, exp: CExp, kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>) -> Result<(), GraphError> {
        // Type inference for [self]
        let typ = self.infer(kctx, &fctx.keys(), &mut self.vctx)?;
        match exp.clone() {
            // Literals get appended to the last node [it]
            CExp::Lit(n) => {
                let node = self.get_it();
                if node.bind_value(Value::Lit(n)) {
                    Ok(())
                } else {
                    Err(GraphError::bind_value(&Value::Lit(n), &node))
                }
            },

            // Variables are edges, no new nodes are added
            CExp::Var(id) =>
                if let Some(nvar) = self.vars.get(&self.scope.var(&id)) {
                    self.add_edge(*nvar, self.it, Edge::data());
                    Ok(())
                } else {
                    Err(GraphError::var_not_found(&id))
                },
            // Create a new [coef] node
            CExp::Coef(box v) => {
                // Add new node
                let ncoef = self.g.add_node(Node::coef(Value::Underscore, typ));
                // Add edge from [it] to [ncoef]
                self.g.add_edge(self.it, ncoef, Edge::data());
                self.g.it = ncoef;
                self.add_exp(*v, kctx, fctx)
            },

            // Create a new [mle] Node
            CExp::Mle(box v) => {
                // Add new node
                let nmle = self.g.add_node(Node::mle(Value::Underscore, typ));
                // Add edge from [it] to [nmle]
                self.g.add_edge(self.it, nmle, Edge::data());
                self.g.it = nmle;
                self.add_exp(*v, kctx, fctx)
            },

            // Create a new [vec] node
            CExp::Vec(box vs) => {
                // Add new node
                let nvec = self.g.add_node(Node::vec(vs.iter().map(|v| Value::Underscore).collect(), typ));
                // Add edge from [it] to [nvec]
                self.g.add_edge(self.it, nvec, Edge::data());
                self.g.it = nvec;
                for v in vs {
                    self.add_exp(v, kctx, fctx)?
                }
                Ok(())
            },

            // Create a new [bin] node
            CExp::Bin(op, box a, box b) => {
                // Add new node
                let nbin = self.g.add_node(Node::bin(op, Value::Underscore, Value::Underscore, typ));
                // Add edge from [it] to [nbin]
                self.g.add_edge(self.it, nbin, Edge::data());
                self.g.it = nbin;
                self.add_exp(*a, kctx, fctx)?;
                self.add_exp(*b, kctx, fctx)?;
            }

            // Create a new [range] node, no new nodes added
            CExp::Range(r) => {
                let node = self.get_it();
                if node.bind_value(Value::Range(r)) {
                    Ok(())
                } else {
                    Err(GraphError::bind_value(&Value::Range(r), &node))
                }
            }

            // Create a new [map] node, with a vector of values
            CExp::Map(box l, x, box CExp::Vec(box vs)) => {
                // Need smart constructors here, to simplify a[r1][r2] etc.

            }
        }
    }
}

