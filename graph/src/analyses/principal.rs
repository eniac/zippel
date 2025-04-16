use crate::{Op, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::Vid;
use lang::ast::{BinOp, CArg};
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::ArkConfig;
use std::fmt;

/// Assign a principal to graph nodes
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Principal {
    Verifier,
    Prover,
    Any
}

/// A greater than zero constraint on an operand
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct GtZ<C: ArkConfig>(pub Op<C>);

impl<C: ArkConfig> GtZ<C> {
    pub fn new(op: Op<C>) -> Self {
        GtZ(op)
    }

    pub fn from_edge<'a>(dag: &'a PrincipalDag<C>, e: EdgeReference<'a, Dep>) -> Self {
        match &dag.0.0[e.source()] {
            Node::Op(op, _) => GtZ(op.clone()),
            Node::Transcr(op, _) => GtZ(op.clone()),
            Node::Inp(_, sig) =>
                if let Some(v) = e.weight().get_var() {
                    let (_, typ) = sig.get(&v).unwrap();
                    return GtZ(Op::Var(v, e.source(), typ.clone()));
                }
                else {
                    panic!("Cannot create GtZ from input node without a variable");
                }
            }
    }
}

/// Graph with principals
#[derive(Clone)]
pub struct PrincipalDag<C: ArkConfig>(Dag<C, Principal>);

impl<C: ArkConfig> PrincipalDag<C> {
    pub fn new(dag: &UDag<C>) -> Self where C: Clone {
        PrincipalDag(Dag(dag.0.map(|_, n|
                match n {
                    Node::Op(op, _) => Node::Op(op.clone(), Principal::Any),
                    Node::Transcr(op, _) => Node::Transcr(op.clone(), Principal::Verifier),
                    Node::Inp(fid, sig) => Node::Inp(fid.clone(), sig.clone())
                },
                |_, e| e.clone())))
    }

    pub fn invert(&mut self) {
        let mut leaks = Vec::new();
        let mut ctrs = Vec::new();

        while let Some(n) = self.0.0.node_indices().find_map(|n| self.inversion(n, &mut leaks, &mut ctrs)) {
            println!("Inverting node {}", n.index());
        }
    }

    /// Check if an edge leads to a verifier state or public argument
    pub fn is_public<'a>(&'a self, e: &EdgeReference<'a, Dep>) -> bool {
        match &self.0.0[e.source()] {
            Node::Op(_, Principal::Verifier) => true,
            Node::Transcr(_, Principal::Verifier) => true,
            Node::Inp(_, sig) => {
                sig.get(&e.weight().get_var().unwrap())
                    .map(|(q, _)| q.is_public())
                    .unwrap()
            }
            _ => false
        }
    }

    /// Check if an edge leads to a prover state or private argument
    pub fn is_private<'a>(&'a self, e: &EdgeReference<'a, Dep>) -> bool {
        !self.is_public(e)
    }

    pub fn publicize(&mut self, node: NodeIndex, var: Option<Vid>, leaks: &mut Vec<Vid>) {
        match self.0.0.node_weight_mut(node).unwrap() {
            Node::Op(_, ann)
            | Node::Transcr(_, ann) =>
                *ann = Principal::Verifier,
            // Let's see if there is a leak
            Node::Inp(_, sig) => {
                if let Some((v, q)) = var.and_then(|v| Some((v.clone(), sig.get(&v)?.0))) {
                    if q.is_private() {
                        // Leak!
                        leaks.push(v)
                    }
                }
            }
        }
    }

    /// Invert an operation
    pub fn inversion(&mut self, n: NodeIndex, leaks: &mut Vec<Vid>, ctrs: &mut Vec<GtZ<C>>) -> Option<NodeIndex> {
        let immself = self.0.0.clone();
        match &immself[n] {
            Node::Op(op, Principal::Verifier) | Node::Transcr(op, _) =>
                match op {
                    Op::Underscore(n, _) => {
                        self.publicize(*n, None, leaks);
                        self.inversion(*n, leaks, ctrs)
                    },
                    Op::Var(v, n, _) => {
                        self.publicize(*n, Some(v.clone()), leaks);
                        self.inversion(*n, leaks, ctrs)
                    },
                    Op::Bin(op, box a, box b, typ) => {
                        let epub =
                            immself
                            .edges_directed(n, Direction::Incoming)
                            .find(|e| self.is_public(e))?;

                        let epriv =
                            immself
                            .edges_directed(n, Direction::Incoming)
                            .find(|e| self.is_private(e))?;

                        match op {
                            BinOp::Add | BinOp::Sub => {
                                self.publicize(epriv.source(), epub.weight().get_var(), leaks);
                                self.inversion(epub.source(), leaks, ctrs)
                            },
                            BinOp::Mul => {
                                // TODO: Add exceptions for group * scalar multiplication which is
                                // computationally hard to invert
                                // Add a constraint that pub * priv is invertible if only pub > 0
                                ctrs.push(GtZ::from_edge(self, epub));
                                self.publicize(epriv.source(), epub.weight().get_var(), leaks);
                                self.inversion(epub.source(), leaks, ctrs)
                            },
                            _ => None
                        }
                    },
                    Op::Ram(box a, box b) => None,
                    Op::Value(v) => None,
                    Op::Range(r) => None,
                    Op::Not(box op) => None,
                    Op::Vec(vs) => None,
                    Op::Check(box op) => None,
                    Op::Coef(box v) => None,
                    Op::Eval(box v) => None,
                    Op::Random(typ) => None,
                    Op::Challenge(typ) => None,
                    Op::Gen(typ) => None,
                },
            Node::Op(_, Principal::Prover | Principal::Any) => None,
            Node::Inp(_, _) => None
        }
    }

    pub fn dag(&self) -> &Dag<C, Principal> {
        &self.0
    }
}

/// Principal basic trait implementations
impl Default for Principal {
    fn default() -> Self {
        Principal::Any
    }
}

impl<'a, D, A> Pretty<'a, D, A> for Principal
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Principal::Prover => allocator.text("Prover"),
            Principal::Verifier => allocator.text("Verifier"),
            Principal::Any => allocator.text("Any"),
        }
    }
    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a> fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Principal as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}

#[cfg(test)] use share::unwrap;
#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn principal_foo() {
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

    // Test zk closure....
    let mut pdag = PrincipalDag::new(&g);
    pdag.invert();

    // Output graph
    pdag.0.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
}
