#![feature(box_patterns)]
mod node;
mod edge;
mod value;
mod principal;

pub use value::Value;
pub use node::{Op, Node, PNode};
pub use edge::{Dependency, Edge};
pub use principal::Principal;

use share::Ctx;
use lang::ast::{CExp, ExpSubst, Arg, CSig, CBody};
use lang::id::{Vid, Tid};
use lang::typ::{CTyp, CTyps, Kind};
use lang::typ::infer::{Typeable, TypeError};

use thiserror::Error;
use petgraph::{dot::Dot, graph::NodeIndex, Direction, Graph};
use std::process::Command;
use std::fmt;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
#[derive(Clone)]
pub struct Dag<A>(Graph<Node<A>, Edge>);

/// Dag with no annotations
pub type PDag = Dag<Principal>;

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
}

impl<A> Dag<A> {
    /// Get the number of nodes in the graph
    pub fn node_count(&self) -> usize {
        self.0.node_count()
    }

    /// Edge deduplication
    fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Edge) {
        self.0.update_edge(source, sink, edge);
    }

    /// Add a node to the graph (no deduplication)
    fn add_node(&mut self, node: Node<A>) -> NodeIndex {
        self.0.add_node(node)
    }

    pub fn get_node(&mut self, it: NodeIndex) -> &mut Node<A> {
        &mut self.0[it]
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
                &self.0,
                &[],
                &|_, e|
                        match e.weight().dep {
                            Dependency::Data => "[color = \"black\"]",
                            Dependency::Transcript => "[color = \"red\"]",
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
}

/// Constructors for graphs
impl PDag {
    fn new(sig: CSig, exp: CExp, fctx: Ctx<CSig, CBody>) -> Self {
        let mut g = Dag(Graph::new());
        // New variable context
        let mut vars = Ctx::new();
        let mut vctx = Ctx::new();
        // Initial node is the function signature
        let it = g.add_node(Node::inp(sig.clone()));
        // Add arguments to [vctx]
        for Arg { id, typ, .. } in sig.args {
            vars.insert(&id, &it);
            vctx.insert(&id, &typ);
        }
        // Add empty transcript node
        let transcr = g.add_node(Node::empty_transcript());
        // Kind context from typevars
        let kctx = sig.typevars.to_ctx();
        g.add_exp(exp, transcr, it, &kctx, &fctx, &vctx, &vars).unwrap();
        g
    }

    /// Overwrite the principal in node [it]
    pub fn set_principal(&mut self, it: NodeIndex, ann: Principal) {
        self.0[it].set_principal(ann);
    }
    /// Add a body [body] to the graph
    pub fn add_body(&mut self,
        body: CBody, transcr: NodeIndex, it: NodeIndex,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, NodeIndex>) -> Result<NodeIndex, GraphError> {
        match body {
            CBody::Proto { relation, body } => {
                self.add_exp(relation, transcr, it, kctx, fctx, vctx, vars)?;
                self.add_exp(body, transcr, it, kctx, fctx, vctx, vars)
            },
            CBody::Func { body } =>
                self.add_exp(body, transcr, it, kctx, fctx, vctx, vars)
        }
    }

    /// Add an expression [exp] to the graph
    pub fn add_exp(&mut self,
        exp: CExp,
        transcr: NodeIndex, it: NodeIndex,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, NodeIndex>) -> Result<NodeIndex, GraphError> {
        // Type inference for [self]
        let typ = exp.infer(kctx, &fctx.keys(), vctx)?;
        match exp.clone() {
            // Literals get appended to the last node [self.it]
            CExp::Lit(n) => {
                let node_it = self.get_node(it);
                node_it.push_value(Value::Lit(n));
                Ok(it)
            },

            // Variables are edges, no new nodes are added
            CExp::Var(id) =>
                if let Some(nvar) = vars.get(&id) {
                    self.add_edge(*nvar, it, Edge::data_var(&id));
                    Ok(it)
                } else {
                    Err(GraphError::var_not_found(&id))
                },
            // Create a new [coef] node
            CExp::Coef(box v) => {
                // Add new node
                let ncoef = self.add_node(Node::coef(typ));
                // Add edge from [it] to [ncoef]
                self.add_edge(it, ncoef, Edge::data());
                self.add_exp(v, transcr, ncoef, kctx, fctx, vctx, vars)
            },

            // Create a new [mle] Node
            CExp::Mle(box v) => {
                // Add new node
                let nmle = self.add_node(Node::mle(typ));
                // Add edge from [it] to [nmle]
                self.add_edge(it, nmle, Edge::data());
                self.add_exp(v, transcr, nmle, kctx, fctx, vctx, vars)
            },

            // Create a new [vec] node
            CExp::Vec(vs) => {
                // Look at the type to get the size of the vector
                if let CTyp::Vec(box inner, size) = typ {
                    // Add new node
                    let nvec = self.add_node(Node::vec(inner, size));
                    // Add edge from [it] to [nvec]
                    self.add_edge(it, nvec, Edge::data());
                    for v in vs {
                        self.add_exp(v, transcr, nvec, kctx, fctx, vctx, vars)?;
                    }
                    Ok(nvec)
                } else {
                    panic!("Expected vector type for {}, got {}", exp, typ)
                }
            },

            // Create a new [bin] node
            CExp::Bin(op, box a, box b) => {
                // Add new node
                let nbin = self.add_node(Node::bin(op, typ));
                // Add edge from [it] to [nbin]
                self.add_edge(it, nbin, Edge::data());
                self.add_exp(a, transcr, nbin, kctx, fctx, vctx, vars)?;
                self.add_exp(b, transcr, nbin, kctx, fctx, vctx, vars)?;
                Ok(nbin)
            },

            // Create a new interpolation node
            CExp::Interpolate(box a, box b) => {
                // Add new node
                let ninterp = self.add_node(Node::interpolate(typ));
                // Add edge from [it] to [ninterp]
                self.add_edge(it, ninterp, Edge::data());
                self.add_exp(a, transcr, ninterp, kctx, fctx, vctx, vars)?;
                self.add_exp(b, transcr, ninterp, kctx, fctx, vctx, vars)?;
                Ok(ninterp)
            },

            CExp::Contains(box a, box b) => {
                // Add new node
                let ncontains = self.add_node(Node::contains(typ));
                // Add edge from [it] to [ncontains]
                self.add_edge(it, ncontains, Edge::data());
                self.add_exp(a, transcr, ncontains, kctx, fctx, vctx, vars)?;
                self.add_exp(b, transcr, ncontains, kctx, fctx, vctx, vars)?;
                Ok(ncontains)
            },

            CExp::Equ(box a, box b) => {
                // Add new node
                let nequ = self.add_node(Node::equ(typ));
                // Add edge from [it] to [nequ]
                self.add_edge(it, nequ, Edge::data());
                self.add_exp(a, transcr, nequ, kctx, fctx, vctx, vars)?;
                self.add_exp(b, transcr, nequ, kctx, fctx, vctx, vars)?;
                Ok(nequ)
            }

            CExp::And(box a, box b) => {
                // Add new node
                let nand = self.add_node(Node::and(typ));
                // Add edge from [it] to [nand]
                self.add_edge(it, nand, Edge::data());
                self.add_exp(a, transcr, nand, kctx, fctx, vctx, vars)?;
                self.add_exp(b, transcr, nand, kctx, fctx, vctx, vars)?;
                Ok(nand)
            },

            CExp::Or(box a, box b) => {
                // Add new node
                let nor = self.add_node(Node::or(typ));
                // Add edge from [it] to [nor]
                self.add_edge(it, nor, Edge::data());
                self.add_exp(a, transcr, nor, kctx, fctx, vctx, vars)?;
                self.add_exp(b, transcr, nor, kctx, fctx, vctx, vars)?;
                Ok(nor)
            },

            CExp::Not(box a) => {
                // Add new node
                let nnot = self.add_node(Node::not(typ));
                // Add edge from [it] to [nnot]
                self.add_edge(it, nnot, Edge::data());
                self.add_exp(a, transcr, nnot, kctx, fctx, vctx, vars)?;
                Ok(nnot)
            },

            // Create a new [range] node, no new nodes added
            CExp::Range(r) => {
                let node_it = self.get_node(it);
                node_it.push_value(Value::Range(r));
                Ok(it)
            }

            // Create a new [map] node, with a vector of values
            CExp::Map(box l, x, box CExp::Vec(vs)) => {
                let mut vids = vctx.keys();
                let mut substituted = Vec::new();
                for v in vs {
                    let mut e = l.clone();
                    e.subst(&x, &v, &mut vids);
                    substituted.push(e);
                }
                self.add_exp(CExp::vec(substituted), transcr, it, kctx, fctx, vctx, vars)
            },
            // [Range(r) = [r.start, r.start + r.step, ...., r.end - r.step]
            CExp::Map(box l, x, box CExp::Range(r)) =>
                self.add_exp(CExp::map(l, x, CExp::vec(r.into_iter().map(|i| CExp::lit(i)).collect())),
                    transcr, it, kctx, fctx, vctx, vars),

            // [p for x in e] = [p[x->0], [1], ...]
            CExp::Map(box l, x, box r) => {
                // Get the size from the type
                let tr = r.infer(kctx, &fctx.keys(), vctx)?;
                if let CTyp::Vec(_, size) = tr {
                    // Generate r[i] for i in [0, size]
                    let expanded = (0..size).into_iter().map(|i| CExp::ram(r.clone(), CExp::lit(i))).collect();
                    // Recurse on [p for x in [e[0]...[e[size]]]]
                    self.add_exp(CExp::map(l, x, CExp::Vec(expanded)), transcr, it, kctx, fctx, vctx, vars)
                } else {
                    panic!("Expected vector type for {}, got {}", r, tr)
                }
            }

            // [a_0, ..., a_n][i] = a_i
            CExp::Ram(box CExp::Vec(vs), box CExp::Lit(i)) =>
                self.add_exp(vs.0[i].clone(), transcr, it, kctx, fctx, vctx, vars),
            // [a + b][i] = a[i] + b[i]
            CExp::Ram(box CExp::Bin(op, box a, box b), box i) =>
                self.add_exp(CExp::bin(op, CExp::ram(a, i.clone()),
                    CExp::ram(b, i)), transcr, it, kctx, fctx, vctx, vars),
            CExp::Ram(box a, box i) => {
                let nram = self.add_node(Node::ram(typ));
                // Add edge from [it] to [nram]
                self.add_edge(it, nram, Edge::data());
                self.add_exp(a, transcr, nram, kctx, fctx, vctx, vars)?;
                self.add_exp(i, transcr, nram, kctx, fctx, vctx, vars)?;
                Ok(nram)
            },
            CExp::Challenge(tid) => {
                let nchallenge = self.add_node(Node::challenge(tid, typ));
                // Add dependency edge from [it] to [nchallenge]
                self.add_edge(it, nchallenge, Edge::data());
                // Add transcript edge to [nchallenge]
                self.add_edge(transcr, nchallenge, Edge::transcript());
                Ok(nchallenge)
            }
            CExp::Gen(tid) => {
                let ngen = self.add_node(Node::generator(tid, typ));
                // Add dependency edge from [it] to [ngen]
                self.add_edge(it, ngen, Edge::data());
                Ok(ngen)
            },
            CExp::Random(tid) => {
                let nrand = self.add_node(Node::random(tid, typ));
                // Add dependency edge from [it] to [nrand]
                self.add_edge(it, nrand, Edge::data());
                Ok(nrand)
            },
            CExp::App(fid, params) => {
                // type inference for each parameter
                let param_types: CTyps = params.iter()
                        .map(|p| p.infer(kctx, &fctx.keys(), vctx)).collect::<Result<_, _>>()?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|(sig, body)| {
                    // If the function name matches
                    if sig.name == fid {
                        // The argument types must match the parameter types
                        let (sig, subs) = sig.clone()
                            .unify(&param_types, &kctx)
                            .ok()?;
                        Some((sig, body, subs))
                    } else {
                        None
                    }
                }).collect::<Vec<_>>();

                // Only one function shoud match (enforced by the type system)
                assert_eq!(matching_sigs.len(), 1);
                let triple = &matching_sigs[0];
                let sig = triple.0.clone();
                let mut body = triple.1.clone();
                let subs = triple.2.clone();
                // Types should match
                assert_eq!(typ, sig.ret);

                // Substitute type variables in the body
                subs.tid_subst(&mut body);

                // Shift captured variables in the body
                let mut vctx_keys = vctx.keys();
                for id in vctx.keys() {
                    body.shift(&id, &mut vctx_keys);
                }
                // Substitute parameters in the body
                for (param, arg) in sig.args.iter().zip(params) {
                    body.subst(&param.id, &arg, &mut vctx_keys);
                }
                // Add the body to the graph
                self.add_body(body, transcr, it, kctx, fctx, vctx, vars)
        },
        CExp::Let(Some(id), box l, box r) => {
            // Infer the type of [l]
            let tl = l.infer(kctx, &fctx.keys(), vctx)?;
            // Add left-hand side as node
            let nl = self.add_exp(l, transcr, it, kctx, fctx, vctx, vars)?;
            // Add [id] to the variable context
            let mut vctx = vctx.clone();
            vctx.insert(&id, &tl);
            let mut vars = vars.clone();
            vars.insert(&id, &nl);
            // Add right-hand side as Node
            self.add_exp(r, transcr, it, kctx, fctx, &vctx, &vars)
        },
        CExp::Let(None, box l, box r) => {
            self.add_exp(l, transcr, it, kctx, fctx, vctx, vars)?;
            self.add_exp(r, transcr, it, kctx, fctx, vctx, vars)
        },
        CExp::Log(id, box l, box r) => {
            // Infer the type of [l]
            let tl = l.infer(kctx, &fctx.keys(), vctx)?;
            // Add left-hand side as node
            let nl = self.add_exp(l, transcr, it, kctx, fctx, vctx, vars)?;
            // Verifier sees the log statement in [nl]
            self.set_principal(nl, Principal::Verifier);
            // Add [id] to the variable context
            let mut vctx = vctx.clone();
            vctx.insert(&id, &tl);
            let mut vars = vars.clone();
            vars.insert(&id, &nl);
            // Add right-hand side as Node
            let nr = self.add_exp(r, nl, it, kctx, fctx, &vctx, &vars)?;
            // Add transcript edge to [nr]
            self.add_edge(transcr, nr, Edge::transcript());
            // Return the right-hand side
            Ok(nr)
        },
        CExp::Assert(box a) => {
            // Add new node
            let nassert = self.add_node(Node::check(typ));
            // Add edge from [it] to [nassert]
            self.add_edge(it, nassert, Edge::data());
            let ni = self.add_exp(a, transcr, nassert, kctx, fctx, vctx, vars)?;
            self.set_principal(ni, Principal::Prover);
            Ok(ni)
        },
        CExp::Verify(box a) => {
            // Add new node
            let nverify = self.add_node(Node::check(typ));
            // Add edge from [it] to [nverify]
            self.add_edge(it, nverify, Edge::data());
            let ni = self.add_exp(a, transcr, nverify, kctx, fctx, vctx, vars)?;
            self.set_principal(ni, Principal::Verifier);
            Ok(ni)
        },
    }
}
}

