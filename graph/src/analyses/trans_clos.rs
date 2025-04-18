use crate::{Op, Node, Dag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::Vid;
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::ArkConfig;
use std::fmt;

/// Transitive closure on a DAG
pub struct TransClos<C: ArkConfig, A> (Dag<C, A>);

impl<C: ArkConfig, A> TransClos<C, A> {
    pub fn new(dag: Dag<C, A>) -> Self where A: Clone {
        TransClos(dag)
    }
    pub fn clos(&self) -> Ctx<usize, Op<C>> {
        let mut clos = Ctx::new();
        let last = self.0.0.node_indices().last().unwrap();
        let op = self.trans_clos_node(last, &mut clos);
        if !op.is_underscore() {
            clos.insert(&last.index(), &op);
        }
        clos
    }
    pub fn trans_clos_op(&self, op: Op<C>, clos: &mut Ctx<usize, Op<C>>) -> Op<C> {
        match op {
            Op::Underscore(n, _) => self.trans_clos_node(n, clos),
            Op::Var(v, n, typ) =>
                match self.0.0[n] {
                    Node::Inp(_, _) => Op::Var(v, n, typ),
                    _ => self.trans_clos_node(n, clos),
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

    pub fn trans_clos_node(&self, node: NodeIndex, clos: &mut Ctx<usize, Op<C>>) -> Op<C> {
        match &self.0.0[node] {
            Node::Op(op @ (Op::Challenge(_) | Op::Gen(_) | Op::Random(_)), _) => {
                clos.insert(&node.index(), &op.clone());
                Op::underscore(&node, op.typ())
            },
            Node::Op(op, _) => self.trans_clos_op(op.clone(), clos),
            Node::Transcr(op, _) => {
                // Add the node to the context
                let op = self.trans_clos_op(op.clone(), clos);
                clos.insert(&node.index(), &op.clone());

                // Add the transcript parent to the context if it does not exist
                let tr_edge =
                    self.0.transcript_edge(node, Direction::Incoming).unwrap();

                if !clos.contains(&tr_edge.source().index()) {
                    self.trans_clos_node(tr_edge.source(), clos);
                }
                // Return the variable
                Op::underscore(&node, op.typ())
            },
            Node::Inp(_, _) => unreachable!()
        }
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
    let clos = TransClos::new(g).clos();

    println!("Transitive closure: {}", clos);

    // There are 5 log operations (including the last verification check) + 1 random operation = 6
    assert_eq!(clos.len(), 6);
}
