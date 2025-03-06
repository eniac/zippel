#![feature(box_patterns)]
mod node;
mod scope;
mod edge;
mod value;
mod principal;

pub use value::Value;
pub use node::{Op, Node, UNode};
pub use edge::{Dependency, Edge};
pub use scope::{Scope, ScopedVar};

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
    scope: Scope,
    vctx: Ctx<Vid, CTyp>,
    vars: Ctx<ScopedVar, NodeIndex>
}


#[derive(Error, PartialEq, Debug)]
pub enum GraphError {
    #[error("Variable not found {0}")]
    VarNotFound(Vid),
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
            vars.insert(&ScopedVar::singleton(sig, &id), &it);
            vctx.insert(&id, &typ);
        }
        // New scope
        let scope = Scope::singleton(sig);
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
            // Literals get appended to the last node [self.it]
            CExp::Lit(n) => {
                let node_it = self.get_it();
                node_it.push_value(Value::Lit(n));
                Ok(())
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
                let ncoef = self.g.add_node(Node::coef(typ));
                // Add edge from [it] to [ncoef]
                self.g.add_edge(self.it, ncoef, Edge::Data);
                self.g.it = ncoef;
                self.add_exp(*v, kctx, fctx)
            },

            // Create a new [mle] Node
            CExp::Mle(box v) => {
                // Add new node
                let nmle = self.g.add_node(Node::mle(typ));
                // Add edge from [it] to [nmle]
                self.g.add_edge(self.it, nmle, Edge::Data);
                self.g.it = nmle;
                self.add_exp(*v, kctx, fctx)
            },

            // Create a new [vec] node, unless its all literals
            CExp::Vec(box vs) => {
                // Look at the type to get the size of the vector
                if let CTyp::Vec(inner, size) = typ {
                    // Is it all literals? Then its a vector value
                    let mut vals = Vec::new();
                    for v in vs {
                        if let CExp::Lit(n) = v {
                            vals.push(n);
                        }
                    }
                    // If all values are literals
                    if vals.len() == vs.len() {
                        let node_it = selt.get_it();
                        node_it.push_value(Value::Vec(vals));
                        Ok(())
                    } else {
                        // Otherwise add new node
                        let nvec = self.g.add_node(Node::vec(inner, size));
                        // Add edge from [it] to [nvec]
                        self.g.add_edge(self.it, nvec, Edge::Data);
                        self.g.it = nvec;
                        for v in vs {
                            self.add_exp(v, kctx, fctx)?
                        }
                        Ok(())
                    }
                } else {
                    panic!("Expected vector type for {}, got {}", self, typ)
                }
            },

            // Create a new [bin] node
            CExp::Bin(op, box a, box b) => {
                // Add new node
                let nbin = self.g.add_node(Node::bin(op, typ));
                // Add edge from [it] to [nbin]
                self.g.add_edge(self.it, nbin, Edge::data());
                self.g.it = nbin;
                self.add_exp(*a, kctx, fctx)?;
                self.add_exp(*b, kctx, fctx)
            },

            // Create a new [range] node, no new nodes added
            CExp::Range(r) => {
                let node_it = self.get_it();
                node_it.push_value(Value::Range(r));
                Ok(())
            }

            // Create a new [map] node, with a vector of values
            CExp::Map(box l, x, box CExp::Vec(box vs)) => {
                let vars = self.vctx.keys();
                let mut substituted = Vec::new();
                for v in vs {
                    substituted.push(l.clone().vid_subst(&x, v, &vars));
                }
                self.add_exp(CExp::Vec(substituted), kctx, fctx)
            },
            // [Range(r) = [r.start, r.start + r.step, ...., r.end - r.step]
            CExp::Map(box l, x, box CExp::Range(r)) =>
                self.add_exp(CExp::map(l, x, CExp::vec(r.into_iter().collect()))),

            // [x for x in (a + b)] = [(a + b)[0], (a + b)[1], ...]
            CExp::Map(box l, x, box r) => {
                let vars = self.vctx.keys();
                let mut substituted = Vec::new();
                // Get the size from the type
                let tr = r.infer(kctx, &fctx.keys(), &mut self.vctx)?;
                if let CTyp(_, size) = tr {
                    for v in 0..size {
                        substituted.push(l.clone().vid_subst(&x, CExp::ram(r, CExp::Lit(v)), &vars));
                    }
                    self.add_exp(CExp::Vec(substituted), kctx, fctx)
                } else {
                    panic!("Expected vector type for {}, got {}", r, tr)
                }
            }

            // [a_0, ..., a_n][i] = a_i
            CExp::Ram(box CExp::Vec(vs), box CExp::Lit(i)) =>
                self.add_exp(vs[i], kctx, fctx),
            // [a + b][i] = a[i] + b[i]
            CExp::Ram(box CExp::Bin(BinOp::Add, box a, box b), box i) =>
                self.add_exp(CExp::add(CExp::ram(a, i), CExp::ram(b, i)), kctx, fctx),
            // [a - b][i] = a[i] - b[i]
            CExp::Ram(box CExp::Bin(BinOp::Sub, box a, box b), box i) =>
                self.add_exp(CExp::sub(CExp::ram(a, i), CExp::ram(b, i)), kctx, fctx),
            // [a * b][i] = a[i] * b[i]
            CExp::Ram(box CExp::Bin(BinOp::Mul, box a, box b), box i) =>
                self.add_exp(CExp::mul(CExp::ram(a, i), CExp::ram(b, i)), kctx, fctx),
            // [a / b][i] = a[i] / b[i]
            CExp::Ram(box CExp::Bin(BinOp::Div, box a, box b), box i) =>
                self.add_exp(CExp::div(CExp::ram(a, i), CExp::ram(b, i)), kctx, fctx),
            // [a ^ b][i] = a[i] ^ b[i]
            CExp::Ram(box CExp::Bin(BinOp::Pow, box a, box b), box i) =>
                self.add_exp(CExp::pow(CExp::ram(a, i), CExp::ram(b, i)), kctx, fctx),
            CExp::Ram(box CExp::Var(v), box i) =>





                let node_it = self.get_it();
                node_it.push_value(Value::Ram(a, b));
                Ok(())
            }
            CExp::Map(box l, x, box v) => {

                // Need smart constructors here, to simplify a[r1][r2] etc.

            }
        }
    }
}

