mod node;
mod edge;
mod op;
mod principal;

pub use crate::graph::op::{Operand, Op};
pub use crate::graph::node::Node;
pub use crate::graph::edge::Edge;
pub use crate::graph::principal::Principal;
pub use crate::arkworks::{ArkConfig, Value, ATyp};

use share::{traversal::ToTraversal1, Ctx};
use lang::ast::{CModule, BinOp, CExp, Arg, CSig, CBody};
use lang::id::{Vid, Tid};
use lang::typ::{Nothing, CTyp, CTyps, Kind};
use lang::typ::infer::{Typeable, TypeError};

use thiserror::Error;
use std::ops::{Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr};
use petgraph::{dot::Dot, graph::NodeIndex, Direction, Graph};
use std::process::Command;
use std::fmt;
use std::path::PathBuf;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
#[derive(Clone)]
pub struct Dag<C: ArkConfig, A>(Graph<Node<C, A>, Edge>);

/// Dag with no annotations
pub type PDag<C> = Dag<C, Nothing>;

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

impl<C: ArkConfig, A> Dag<C, A> {
    /// Get the number of nodes in the graph
    pub fn node_count(&self) -> usize {
        self.0.node_count()
    }

    /// Edge deduplication
    fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Edge) {
        self.0.add_edge(source, sink, edge);
    }

    fn add_edges(&mut self, sink: NodeIndex, source: Operand<C>) {
        source.edges().into_iter().for_each(|(n, e)| {
            self.add_edge(n, sink, e);
        });
    }

    fn add_implicit_edges(&mut self, sink: NodeIndex, source: Operand<C>) {
        source.edges().into_iter().for_each(|(n, e)| {
            self.add_edge(n, sink, e.into_implicit());
        });
    }

    /// Add a node to the graph (no deduplication)
    fn add_node(&mut self, node: Node<C, A>) -> NodeIndex {
        self.0.add_node(node)
    }

    pub fn get_node(&mut self, it: NodeIndex) -> &mut Node<C, A> {
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
                        match e.weight() {
                            Edge::Data(_) => "color = \"black\"",
                            Edge::Transcript => "color = \"red\"",
                            Edge::Implicit(_) => "color = \"blue\"",
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
            .spawn()?
            .wait()?;

        // Remove DOT file
        // std::fs::remove_file(fdot)?;

        // Print success
        println!("Wrote {:?}", std::fs::canonicalize(PathBuf::from(fpdf.clone())));
        Ok(())
    }
}

/// Constructors for graphs
impl<C: ArkConfig> PDag<C> {
    fn from_module(m: CModule) -> Result<Self, GraphError> {
        let mut g = Dag(Graph::new());
        // Build [fctx] from module
        let fctx =
            m.iter().map(|(sig, body)|
                (sig.clone(), body.clone())).collect::<Ctx<CSig, CBody>>();
        for (sig, body) in m.into_iter() {
            // Initial node is the function signature
            let mut start = g.add_node(Node::inp(sig.clone()));
            // Kind context
            let kctx = sig.typevars.to_ctx();
            // Add arguments to [vctx] and [vars]
            let mut vars = Ctx::new();
            let mut vctx = Ctx::new();
            for Arg { id, typ, .. } in sig.args.iter() {
                let at = ATyp::from_ctyp(typ, &kctx).ok_or_else(|| {
                    TypeError::decl(&sig.name,
                        TypeError::ark(&kctx, &vctx, &CExp::var(id), typ))
                })?;
                vars.insert(id, &Operand::var(id, &start, at));
                vctx.insert(id, typ);
            }
            // Typecheck the body with the type signature
            body.typecheck(sig, &fctx.keys())?;
            // Take cases on the type of declaration
            match body {
                CBody::Proto { relation, body } => {
                    // Add the relation to the graph
                    let orel = g.add_exp(relation, &mut start, &kctx, &fctx, &vctx, &vars)?;
                    // g.add_implicit_edges(start, orel);

                    // Add the body to the Graph
                    let op = g.add_exp(body, &mut start, &kctx, &fctx, &vctx, &vars)?;
                    let nr = g.add_node(Node::ret(&op));
                    g.add_edges(nr, op);
                },
                CBody::Func { body } => {
                    let op = g.add_exp(body, &mut start, &kctx, &fctx, &vctx, &vars)?;
                    let nr = g.add_node(Node::ret(&op));
                    g.add_edges(nr, op);
                }
            };
        }
        Ok(g)
    }

    /// Add an expression [exp] to the graph
    pub fn add_exp(&mut self,
        exp: CExp,
        transcr: &mut NodeIndex,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, Operand<C>>) -> Result<Operand<C>, GraphError> {
        let typ = exp.infer(kctx, &fctx.keys(), vctx)?;
        // Type inference for [self]
        match exp.clone() {
            // Literals get appended to the last node [self.it]
            CExp::Lit(n) => {
                Ok(Operand::Value(Value::Index(n as u64)))
            },

            CExp::Bool(b) => {
                Ok(Operand::Value(Value::Bool(b)))
            },
            // Variables are edges, no new nodes are added
            CExp::Var(id) => vars.get(&id)
                .map(|v| v.clone())
                .ok_or_else(|| GraphError::var_not_found(&id)),

            // Create a new [coef], [eval] or [mle] node
            CExp::Coef(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, kctx, fctx, vctx, vars)?;
                // Add new node
                let ncoef = self.add_node(Node::coef(&child));

                // Add edge from [ncoef] to [child]
                self.add_edges(ncoef, child);

                Ok(Operand::Underscore(ncoef, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },
            CExp::Eval(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, kctx, fctx, vctx, vars)?;
                // Add new node
                let neval = self.add_node(Node::eval(&child));

                // Add edge from [ncoef] to [child]
                self.add_edges(neval, child);

                Ok(Operand::Underscore(neval, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },

            // Create a new [vec] value
            CExp::Vec(vs) =>
                Ok(Operand::vec(vs.0.traverse1(&mut |v|
                            self.add_exp(v, transcr, kctx, fctx, vctx, vars))?)),

            // MLE is a noop?
            CExp::Mle(box inner) => self.add_exp(inner, transcr, kctx, fctx, vctx, vars),

            // Create a new [bin] node
            CExp::Bin(op, box a, box b) => {
                let ta = a.infer(kctx, &fctx.keys(), vctx)?;
                let tb = b.infer(kctx, &fctx.keys(), vctx)?;

                // Convert polynomials to vectors
                match (ta, tb, op) {
                    (CTyp::Uni(_, _), CTyp::Uni(_, _), BinOp::Mul) => {
                        return self.add_exp(CExp::coef(CExp::eval(a) * CExp::eval(b)),
                            transcr, kctx, fctx, vctx, vars);
                    }
                    (CTyp::Uni(_, _), CTyp::Uni(_, _), BinOp::Div) => {
                        return self.add_exp(CExp::coef(CExp::eval(a) / CExp::eval(b)),
                            transcr, kctx, fctx, vctx, vars);
                    }
                    (CTyp::Uni(_, _), CTyp::Uni(_, _), BinOp::Rem) => {
                        return self.add_exp(CExp::coef(CExp::eval(a) % CExp::eval(b)),
                            transcr, kctx, fctx, vctx, vars);
                    }
                    _ => ()
                };

                // Add children first
                let vl = self.add_exp(a, transcr, kctx, fctx, vctx, vars)?;
                let vr = self.add_exp(b, transcr, kctx, fctx, vctx, vars)?;

                // Convert type [typ] to [ATyp]
                let atyp = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;

                // Maybe there will be no node
                if let Some(op) = Operand::bin(op, &vl, &vr, &atyp) {
                    Ok(op)
                } else {
                    // Add new node
                    let nbin = self.add_node(Node::bin(op, &vl, &vr));

                    // Add edges from [nbin] to [vl] and [vr]
                    self.add_edges(nbin, vl);
                    self.add_edges(nbin, vr);
                    Ok(Operand::Underscore(nbin, atyp))
                }
            },

            CExp::Not(box a) =>
                Ok(Operand::not(self.add_exp(a, transcr, kctx, fctx, vctx, vars)?)),

            // Create a [range] value, no new nodes added
            CExp::Range(r) => Ok(Operand::range(r)),


            CExp::Map(box l, x, box e) => {
                // Type of [e]
                let te = e.infer(kctx, &fctx.keys(), vctx)?;
                // Operand for [e]
                let oe = self.add_exp(e, transcr, kctx, fctx, vctx, vars)?;
                let ate = ATyp::from_ctyp(&te, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &te))
                })?;

                // Get the size [n] from type [te]
                let (_, n) = ate.into_vec().unwrap();
                // Operands are saved here
                let mut res = Vec::with_capacity(n);
                // Create operands
                for i in 0..n {
                    // Add oe[i] to vars and vctx
                    let mut vars = vars.clone();
                    let mut vctx = vctx.clone();
                    vars.insert(&x, &Operand::ram(oe.clone(), Operand::index(i)));
                    vctx.insert(&x, &te);
                    // Add subexpression
                    let ol = self.add_exp(l.clone(), transcr, kctx, fctx, &vctx, &vars)?;
                    res.push(ol);
                }
                Ok(Operand::vec(res))
            },

            CExp::Ram(box a, box b) => {
                // Add children
                let oa = self.add_exp(a, transcr, kctx, fctx, vctx, vars)?;
                let ob = self.add_exp(b, transcr, kctx, fctx, vctx, vars)?;
                Ok(Operand::ram(oa, ob))
            },
            CExp::Challenge(_) => {
                let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;
                let nchallenge = self.add_node(Node::challenge(&at));
                // Add transcript edge to [nchallenge]
                self.add_edge(*transcr, nchallenge, Edge::Transcript);
                // Update transcript node
                *transcr = nchallenge;
                Ok(Operand::Underscore(nchallenge, at))
            },
            CExp::Gen(_) =>
                Ok(Operand::Gen(
                        ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, vctx, &exp),
                                TypeError::ark(kctx, vctx, &exp, &typ))
                        })?)),
            CExp::Random(_) => {
                let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;
                let nrand = self.add_node(Node::random(&at));
                Ok(Operand::Underscore(nrand, at))
            },
            CExp::App(fid, params) => {
                // type inference for each parameter
                let param_types: CTyps = params.iter()
                        .map(|p| p.infer(kctx, &fctx.keys(), vctx)).collect::<Result<_, _>>()?;

                // Find all matching functions in function context [fctx]
                let matching_sigs =
                    fctx.iter().filter_map(|(sig, body)| {
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
                let triple = matching_sigs[0].clone();
                let sig = triple.0;
                let mut body = triple.1.clone();
                let subs = triple.2;

                // Substitute type variables in the body
                subs.tid_subst(&mut body);

                // First add the arguments to the graph
                let oparams: Vec<Operand<C>> = params.into_iter()
                    .map(|p| self.add_exp(p, transcr, kctx, fctx, vctx, vars))
                    .collect::<Result<_, _>>()?;

                // Create a new context
                let vctx = sig.args.to_ctx();
                let vars =
                    sig.args.iter().zip(oparams.iter())
                    .map(|(arg, op)| (arg.id.clone(), op.clone())).collect::<Ctx<Vid, Operand<C>>>();

                // Add the body to the graph
                self.add_exp(body.body(), transcr, kctx, fctx, &vctx, &vars)
            },
            CExp::Let(Some(id), box l, box r) => {
                // Infer the type of [l]
                let tl = l.infer(kctx, &fctx.keys(), vctx)?;
                // Add left-hand side as node
                let nl = self.add_exp(l, transcr, kctx, fctx, vctx, vars)?;
                // Add [id] to the variable context
                let mut vctx = vctx.clone();
                vctx.insert(&id, &tl);
                let mut vars = vars.clone();
                vars.insert(&id, &nl);
                // Add right-hand side as Node
                self.add_exp(r, transcr, kctx, fctx, &vctx, &vars)
            },
            CExp::Let(None, box l, box r) => {
                self.add_exp(l, transcr, kctx, fctx, vctx, vars)?;
                self.add_exp(r, transcr, kctx, fctx, vctx, vars)
            },
            CExp::Log(id, box l, box r) => {
                // Infer the type of [l]
                let tl = l.infer(kctx, &fctx.keys(), vctx)?;
                // Add left-hand side as node
                let ol = self.add_exp(l, transcr, kctx, fctx, vctx, vars)?;
                // Add hash node
                let nl = self.add_node(Node::hash(&ol));
                // Add transcript edge to [nl]
                self.add_edge(*transcr, nl, Edge::Transcript);
                // Update transcript node
                *transcr = nl;
                // Add [id] to the variable context
                let mut vctx = vctx.clone();
                vctx.insert(&id, &tl);
                let mut vars = vars.clone();
                vars.insert(&id, &ol);

                // Add edge to hash
                self.add_edges(nl, ol);
                // Add right-hand side as Node
                self.add_exp(r, transcr, kctx, fctx, &vctx, &vars)
            },
            CExp::Assert(box a) => {
                let oa = self.add_exp(a, transcr, kctx, fctx, vctx, vars)?;
                // Add new node
                let nassert = self.add_node(Node::assert(&oa));
                // Add edges
                self.add_edges(nassert, oa);
                Ok(Operand::Underscore(nassert, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?))
            },
            CExp::Verify(box a) => {
                let oa = self.add_exp(a, transcr, kctx, fctx, vctx, vars)?;
                // Add new node
                let nverify = self.add_node(Node::verify(&oa));
                self.add_edges(nverify, oa);
                Ok(Operand::Underscore(nverify, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?))
            },
        }
    }
}

#[cfg(test)]
struct PrettyResult<A, E: fmt::Display>(Result<A, E>);

#[cfg(test)]
impl<A, E: fmt::Display> From<Result<A, E>> for PrettyResult<A, E> {
    fn from(r: Result<A, E>) -> Self {
        PrettyResult(r)
    }
}

#[cfg(test)]
impl<A, E: fmt::Display> PrettyResult<A, E> {
    pub fn pretty_unwrap(self) -> A {
        match self.0 {
            Ok(a) => a,
            Err(e) => panic!("Error: {}", e)
        }
    }
}

#[cfg(test)] use lang::ast::module::UModule;
#[cfg(test)] use crate::arkworks::ArkBls12_381;
#[test]
fn graph_from_module_sum() {
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
    let g = PrettyResult(PDag::<ArkBls12_381>::from_module(m)).pretty_unwrap();
    g.write_pdf("graph_sum").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn graph_from_module_foo() {
    let ex = r#"
        proto foo<F: Field>(private s: F) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r + c + s;
            assert(true);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let g = PrettyResult(PDag::<ArkBls12_381>::from_module(m)).pretty_unwrap();
    g.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn graph_from_module_poly() {
    let ex = r#"
        fn poly_add<F: Field>(public a: Uni<F, 16>, public b: Uni<F, 16>) -> Uni<F, 32> {
            a * b
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let g = PrettyResult(PDag::<ArkBls12_381>::from_module(m)).pretty_unwrap();
    g.write_pdf("graph_poly").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
