#![feature(box_patterns)]
mod node;
mod dep;
mod op;
mod analyses;

pub use op::Op;
pub use node::Node;
pub use dep::{DepType, Dep};

use backend::{ArkConfig, Value, ATyp};
use share::{traversal::ToTraversal1, Ctx};
use lang::ast::{CModule, BinOp, CExp, Arg, CSig, CBody};
use lang::id::{Vid, Tid};
use lang::typ::{Qualifier, Nothing, CTyp, CTyps, Kind};
use lang::typ::infer::{Typeable, TypeError};

use thiserror::Error;
use petgraph::{dot::Dot, graph::{EdgeReference, NodeIndex}, Direction, Graph};
use std::process::Command;
use std::fmt;
use std::path::PathBuf;

/// Represents graphs in the Zippel language
/// graph intermediate representation (Graph IR)
/// It is parameterized by types `A` representing a
/// node annotation like costs, schedules etc.
#[derive(Clone)]
pub struct Dag<C: ArkConfig, A>(Graph<Node<C, A>, Dep>);

/// Dag with no annotations
pub type UDag<C> = Dag<C, Nothing>;

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

    /// Dep deduplication
    fn add_edge(&mut self, source: NodeIndex, sink: NodeIndex, edge: Dep) {
        /*
        if let Some(e) = self.0.find_edge(source, sink) {
            // If the old edge exists, check its type
            if self.0[e].edge_type() != edge.edge_type() {
                // If the edges have different types, add new edge
                self.0.add_edge(source, sink, edge);
            }
            return;
        }
        // If the edge does not exist, add it
        */
        self.0.add_edge(source, sink, edge);
    }

    fn add_edges(&mut self, edge_type: DepType, sink: NodeIndex, source: Op<C>) {
        source.dependencies().into_iter().for_each(|(n, opt)| {
            self.add_edge(n, sink, Dep::new(edge_type.clone(), opt));
        });
    }

    /// Add a node to the graph (no deduplication)
    fn add_node(&mut self, node: Node<C, A>) -> NodeIndex {
        self.0.add_node(node)
    }

    pub fn get_node(&mut self, it: NodeIndex) -> &mut Node<C, A> {
        &mut self.0[it]
    }

    pub fn max_node(&self) -> NodeIndex {
        self.0.node_indices().last().unwrap()
    }

    pub fn transcript_edge<'a>(&'a self, n: NodeIndex, dir: Direction) -> Option<EdgeReference<'a, Dep>> {
        self.0.edges_directed(n, dir)
            .find(|edge| edge.weight().is_transcript())
    }

    /// Write graph to PDF
    pub fn write_pdf<'a>(&self, filename: &str) -> std::io::Result<()>
    where
        A: Clone + fmt::Display
    {
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

/// Constructors for graphs
impl<C: ArkConfig> UDag<C> {
    fn from_module(m: CModule) -> Result<Self, GraphError> {
        let mut g = Dag(Graph::new());
        // Build [fctx] from module
        let fctx =
            m.iter().map(|(sig, body)|
                (sig.clone(), body.clone())).collect::<Ctx<CSig, CBody>>();
        for (sig, body) in m.into_iter() {
            // Kind context
            let kctx = sig.typevars.to_ctx();
            // Add arguments to [vctx] and [vars]
            let mut vars = Ctx::new();
            let mut vctx = Ctx::new();

            // Cast the signature to a arguments and insert to [start] node
            let mut asig: Ctx<Vid, (Qualifier, ATyp)> = Ctx::new();
            for arg in sig.args.iter() {
                let atyp =
                    ATyp::from_ctyp(&arg.typ, &kctx).ok_or_else(|| {
                        TypeError::decl(&sig.name,
                             TypeError::ark(&kctx, &vctx, &CExp::var(&arg.id), &arg.typ))
                        })?;
                // Add argument to [asig]
                asig.insert(&arg.id, &(arg.qualifier.clone(), atyp));
            }
            // Start node
            let mut start = g.add_node(Node::inp(sig.name.clone(), asig));


            // Initial node is the function signature
            for Arg { id, typ, .. } in sig.args.iter() {
                let at = ATyp::from_ctyp(typ, &kctx).ok_or_else(|| {
                    TypeError::decl(&sig.name,
                        TypeError::ark(&kctx, &vctx, &CExp::var(id), typ))
                })?;
                vars.insert(id, &Op::var(id, &start, at));
                vctx.insert(id, typ);
            }
            // Typecheck the body with the type signature
            body.typecheck(sig, &fctx.keys())?;

            // Add the body to the Graph
            let op = g.add_exp(body.body(), &mut start, DepType::Data, &kctx, &fctx, &vctx, &vars)?;
            if !matches!(op, Op::Underscore(_, _)) {
                let nr = g.add_node(Node::ret(&op));
                g.add_edges(DepType::Data, nr, op);
            };
        }
        Ok(g)
    }

    /// Add an expression [exp] to the graph
    pub fn add_exp(&mut self,
        exp: CExp,
        transcr: &mut NodeIndex,
        edge_type: DepType,
        kctx: &Ctx<Tid, Kind>, fctx: &Ctx<CSig, CBody>,
        vctx: &Ctx<Vid, CTyp>, vars: &Ctx<Vid, Op<C>>) -> Result<Op<C>, GraphError> {
        // Type inference for [self]
        let typ = exp.infer(kctx, &fctx.keys(), vctx)?;
        // Convert [CExp] to [Op] while creating the graph
        match exp.clone() {
            // Literals get appended to the last node [self.it]
            CExp::Lit(n) =>
                Ok(Op::Value(Value::Index(n as u64))),

            CExp::Bool(b) =>
                Ok(Op::Value(Value::Bool(b))),

            // Variables are edges, no new nodes are added
            CExp::Var(id) => vars.get(&id)
                .map(|v| v.clone())
                .ok_or_else(|| GraphError::var_not_found(&id)),

            // Create a new [coef], [eval] or [mle] node
            CExp::Coef(box v) => {
                // Add child first
                let child = self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let ncoef = self.add_node(Node::coef(&child));

                // Add edge from [ncoef] to [child]
                self.add_edges(edge_type, ncoef, child);

                Ok(Op::Underscore(ncoef, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
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

                Ok(Op::Underscore(neval, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ)
                    )
                })?))
            },

            // Create a new [vec] value
            CExp::Vec(vs) =>
                Ok(Op::vec(vs.0.traverse1(&mut |v|
                            self.add_exp(v, transcr, edge_type, kctx, fctx, vctx, vars))?)),

            // MLE is a noop?
            CExp::Mle(box inner) => self.add_exp(inner, transcr, edge_type, kctx, fctx, vctx, vars),

            // Create a new [bin] node
            CExp::Bin(op, box a, box b) => {
                let ta = a.infer(kctx, &fctx.keys(), vctx)?;
                let tb = b.infer(kctx, &fctx.keys(), vctx)?;

                // Convert polynomials to vectors
                match (&typ, ta, tb, op) {
                    // Polynomial multiplication and division
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), CTyp::Uni(_, r),
                        op @(BinOp::Mul | BinOp::Div)) =>
                        if &l < n && &r < n {
                            // Pad with zeroes
                            let ex_a = CExp::eval(CExp::concat(a, CExp::zeroes(*n - l)));
                            let ex_b = CExp::eval(CExp::concat(b, CExp::zeroes(*n - r)));
                            return self.add_exp(CExp::coef(CExp::bin(op, ex_a, ex_b)),
                                transcr, edge_type, kctx, fctx, vctx, vars);
                        } else {
                            return self.add_exp(CExp::coef(CExp::bin(op, CExp::eval(a), CExp::eval(b))),
                                transcr, edge_type, kctx, fctx, vctx, vars);
                        },
                    // Polynomial remainder
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), CTyp::Uni(_, r), BinOp::Rem) =>
                        unimplemented!("Polynomial remainder"),
                    // Polynomial exponentiation
                    (CTyp::Uni(_, n), CTyp::Uni(_, l), _, BinOp::Pow) => {
                        // Pad with zeroes
                        let ex = CExp::eval(CExp::concat(a, CExp::zeroes(*n - l)));
                        return self.add_exp(CExp::coef(CExp::pow(ex, b)),
                            transcr, edge_type, kctx, fctx, vctx, vars);
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

                let bop = Op::bin(op, vl.clone(), vr.clone(), atyp.clone());

                // Maybe there will be no node
                if let Op::Bin(op, box vl, box vr, atyp) = bop {
                    // Add new node
                    let nbin = self.add_node(Node::bin(op, &vl, &vr, &atyp));

                    // Add edges from [nbin] to [vl] and [vr]
                    self.add_edges(edge_type, nbin, vl);
                    self.add_edges(edge_type, nbin, vr);
                    Ok(Op::Underscore(nbin, atyp))
                } else {
                    Ok(bop)
                }
            },

            CExp::Not(box a) =>
                Ok(Op::not(self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?)),

            // Create a [range] value, no new nodes added
            CExp::Range(r) => Ok(Op::range(r)),

            CExp::Map(box l, x, box e) => {
                // Type of [e]
                let te = e.infer(kctx, &fctx.keys(), vctx)?;
                // Op for [e]
                let oe = self.add_exp(e, transcr, edge_type, kctx, fctx, vctx, vars)?;
                let ate = ATyp::from_ctyp(&te, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &te))
                })?;

                // Get the size [n] from type [te]
                let (_, n) = ate.into_vec();
                // Ops are saved here
                let mut res = Vec::with_capacity(n);
                // Create operations
                for i in 0..n {
                    // Add oe[i] to vars and vctx
                    let mut vars = vars.clone();
                    let mut vctx = vctx.clone();
                    vars.insert(&x, &Op::ram(oe.clone(), Op::index(i)));
                    vctx.insert(&x, &te);
                    // Add subexpression
                    let ol = self.add_exp(l.clone(), transcr, edge_type, kctx, fctx, &vctx, &vars)?;
                    res.push(ol);
                }
                Ok(Op::vec(res))
            },

            CExp::Ram(box a, box b) => {
                // Add children
                let oa = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                let ob = self.add_exp(b, transcr, edge_type, kctx, fctx, vctx, vars)?;
                Ok(Op::ram(oa, ob))
            },
            CExp::Challenge(_) => {
                let at = ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?;
                let nchallenge = self.add_node(Node::challenge(&at));
                // Add transcript edge to [nchallenge]
                self.add_edge(*transcr, nchallenge, Dep::transcript());
                // Update transcript node
                *transcr = nchallenge;
                Ok(Op::Underscore(nchallenge, at))
            },
            CExp::Gen(_) =>
                Ok(Op::Gen(
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
                Ok(Op::Underscore(nrand, at))
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
                let oparams: Vec<Op<C>> = params.into_iter()
                    .map(|p| self.add_exp(p, transcr, edge_type, kctx, fctx, vctx, vars))
                    .collect::<Result<_, _>>()?;

                // Create a new context
                let vctx = sig.args.to_ctx();
                let vars =
                    sig.args.iter().zip(oparams.iter())
                    .map(|(arg, op)| (arg.id.clone(), op.clone())).collect::<Ctx<Vid, Op<C>>>();

                // Add the body to the graph
                self.add_exp(body.body(), transcr, edge_type, kctx, fctx, &vctx, &vars)
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
                    Op::Underscore(n, _) => {
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
                let nassert = self.add_node(Node::assert(&oa));
                // Add edges
                self.add_edges(edge_type, nassert, oa);
                Ok(Op::Underscore(nassert, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?))
            },
            CExp::Verify(box a) => {
                let oa = self.add_exp(a, transcr, edge_type, kctx, fctx, vctx, vars)?;
                // Add new node
                let nverify = self.add_node(Node::verify(&oa));
                self.add_edges(edge_type, nverify, oa);
                self.add_edge(*transcr, nverify, Dep::transcript());
                Ok(Op::Underscore(nverify, ATyp::from_ctyp(&typ, kctx).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, &exp),
                        TypeError::ark(kctx, vctx, &exp, &typ))
                })?))
            },
        }
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
    println!("{}", m);
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));
    g.write_pdf("graph_sum").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}

#[test]
fn graph_foo() {
    use analyses::TransClos;
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
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Output graph
    g.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    // Test transitive closure
    let tc = TransClos::new(g);
    println!("Transitive closure = \n{}", tc.closure());
}

#[test]
fn graph_poly() {
    let ex = r#"
        fn poly_mul<F: Field>(public a: Uni<F, 16>, public b: Uni<F, 16>) -> Uni<F, 32> {
            a * b
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));
    g.write_pdf("graph_poly").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
