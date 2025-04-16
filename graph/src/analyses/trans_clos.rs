use crate::{Op, Node, Dag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph
};
use lang::id::Vid;
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::ArkConfig;
use std::fmt;

/// Transitive closure on a DAG
pub struct TransClos<C: ArkConfig, A> (Dag<C, A>);

/// Reconstruct a straight-line program from a DAG
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransOp<C: ArkConfig> {
    Op(Op<C>),
    Transcr(Op<C>),
}

/// Pretty-printer
impl<'a, D, C, A> Pretty<'a, D, A> for TransOp<C>
where
    D: DocAllocator<'a, A>,
    C: ArkConfig,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            TransOp::Op(op) => op.pretty(allocator),
            TransOp::Transcr(op) =>
                allocator.concat([
                    allocator.text("(log "),
                    op.pretty(allocator),
                    allocator.text(")")
                ]),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, C: ArkConfig> fmt::Display for TransOp<C>{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TransOp<C> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<C: ArkConfig, A> TransClos<C, A> {
    pub fn new(dag: &Dag<C, A>) -> Self where A: Clone {
        TransClos(dag.clone())
    }
    pub fn clos(&self) -> (Ctx<usize, TransOp<C>>, Op<C>) {
        let mut clos = Ctx::new();
        let last = self.0.0.node_indices().last().unwrap();
        let op = self.trans_clos_node(last, &mut clos);
        (clos, op)
    }
    pub fn trans_clos_op(&self, op: Op<C>, clos: &mut Ctx<usize, TransOp<C>>) -> Op<C> {
        match op {
            Op::Underscore(n, _) => self.trans_clos_node(n, clos),
            Op::Var(v, n, typ) =>
                if v.0[1..].parse() == Ok(n.index()) {
                    Op::var(&v, &n, typ)
                } else {
                    match self.0.0[n] {
                        Node::Inp(_, _) => Op::Var(v, n, typ),
                        _ => self.trans_clos_node(n, clos),
                    }
                },
            Op::Bin(op, box a, box b, typ) => {
                let oa = self.trans_clos_op(a, clos);
                let ob = self.trans_clos_op(b, clos);
                Op::Bin(op, Box::new(oa), Box::new(ob), typ)
            },
            Op::Ram(box a, box b) => {
                let oa = self.trans_clos_op(a, clos);
                let ob = self.trans_clos_op(b, clos);
                Op::Ram(Box::new(oa), Box::new(ob))
            },
            Op::Value(v) => Op::Value(v),
            Op::Range(r) => Op::Range(r),
            Op::Not(box op) => Op::Not(Box::new(self.trans_clos_op(op, clos))),
            Op::Vec(vs) =>
                Op::Vec(vs.into_iter().map(|v| self.trans_clos_op(v, clos))
                    .collect::<Vec<_>>()),
            Op::Check(box op) => Op::Check(Box::new(self.trans_clos_op(op, clos))),
            Op::Coef(box v) => Op::Coef(Box::new(self.trans_clos_op(v, clos))),
            Op::Eval(box v) => Op::Eval(Box::new(self.trans_clos_op(v, clos))),
            op => op
        }
    }

    pub fn trans_clos_node(&self, node: NodeIndex, clos: &mut Ctx<usize, TransOp<C>>) -> Op<C> {
        match &self.0.0[node] {
            Node::Op(op @ (Op::Challenge(_) | Op::Gen(_) | Op::Random(_)), _) => {
                clos.insert(&node.index(), &TransOp::Op(op.clone()));
                Op::var(&Vid::from(format!("#{}", node.index())), &node, op.typ())
            },
            Node::Op(op, _) => self.trans_clos_op(op.clone(), clos),
            Node::Transcr(op, _) => {
                // Add the node to the context
                let op = self.trans_clos_op(op.clone(), clos);
                clos.insert(&node.index(), &TransOp::Transcr(op.clone()));
                // Add the transcript parent to the context if it does not exist
                let tr_edge = self.incoming_transcript_edge(node).unwrap();
                if !clos.contains(&tr_edge.source().index()) {
                    self.trans_clos_node(tr_edge.source(), clos);
                }
                // Return the variable
                Op::var(&Vid::from(format!("#{}", node.index())), &node, op.typ())
            },
            Node::Inp(_, _) => unreachable!()
        }
    }

    fn incoming_transcript_edge<'a>(&'a self, node: NodeIndex) -> Option<EdgeReference<'a, Dep>> {
        let mut incoming = self.0.0.edges_directed(node, petgraph::Direction::Incoming);
        while let Some(edge) = incoming.next() {
            if edge.weight().is_transcript() {
                return Some(edge);
            }
        }
        None
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use crate::UDag;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn trans_clos_foo() {
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
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Compute transitive closure
    let (clos, op) = TransClos::new(&g).clos();

    // There are 5 log operations (including the last verification check) + 1 random operation = 6
    assert_eq!(clos.len(), 6);

    // The last operation is the verification check
    assert!(matches!(op, Op::Var(_, _, _)));
}
