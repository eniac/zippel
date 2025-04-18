use crate::{Op, Node, Dag};
use petgraph::{
    graph::NodeIndex,
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::Vid;
use share::Ctx;
use backend::ArkConfig;

/// Transitive closure on a DAG
pub struct TransClos<C: ArkConfig, A> {
    dag: Dag<C, A>,
    clos: Ctx<usize, Op<C>>
}

impl<C: ArkConfig, A> TransClos<C, A> {
    pub fn new(dag: Dag<C, A>) -> Self where A: Clone {
        let mut clos = Ctx::new();
        // Maximum node
        let last = dag.max_node();
        // Empty transitive closure
        let mut s = Self { dag, clos };
        // Compute transitive closure
        let op = s.trans_clos_node(last);
        if !op.is_underscore() {
            s.clos.insert(&last.index(), &op);
        }
        s
    }

    pub fn closure(self) -> Ctx<usize, Op<C>> {
        self.clos
    }

    pub fn max_node(&self) -> usize {
        self.dag.max_node().index().max(*self.clos.keys().iter().max().unwrap_or(&0))
    }

    fn trans_clos_op(&mut self, op: Op<C>) -> Op<C> {
        match op {
            Op::Underscore(n, _) => self.trans_clos_node(n),
            Op::Var(v, n, typ) =>
                match self.dag.0[n] {
                    Node::Inp(_, _) => Op::Var(v, n, typ),
                    _ => self.trans_clos_node(n),
                },
            Op::Bin(op, box a, box b, typ) => {
                let oa = self.trans_clos_op(a);
                let ob = self.trans_clos_op(b);
                let obin = Op::bin(op, oa, ob, typ.clone());
                // Look for the binary operation in the context
                if let Some((n, _)) = self.clos.iter().find(|(_, op)| op == &&obin) {
                    return Op::underscore(&NodeIndex::new(*n), typ);
                } else {
                    let mut m = self.max_node();
                    m += 1;
                    self.clos.insert(&m, &obin);
                    return Op::underscore(&NodeIndex::new(m), typ);
                }
            },
            Op::Ram(box a, box b) => {
                let oa = self.trans_clos_op(a);
                let ob = self.trans_clos_op(b);
                Op::Ram(Box::new(oa), Box::new(ob))
            },
            Op::Value(v) => Op::Value(v),
            Op::Range(r) => Op::Range(r),
            Op::Not(box op) => Op::Not(Box::new(self.trans_clos_op(op))),
            Op::Vec(vs) =>
                Op::Vec(vs.into_iter().map(|v| self.trans_clos_op(v))
                    .collect::<Vec<_>>()),
            Op::Check(box op) => Op::Check(Box::new(self.trans_clos_op(op))),
            Op::Coef(box v) => Op::Coef(Box::new(self.trans_clos_op(v))),
            Op::Eval(box v) => Op::Eval(Box::new(self.trans_clos_op(v))),
            op => op
        }
    }

    fn trans_clos_node(&mut self, node: NodeIndex) -> Op<C> {
        match &self.dag.0[node] {
            Node::Op(op @ (Op::Challenge(_) | Op::Gen(_) | Op::Random(_)), _) => {
                self.clos.insert(&node.index(), &op.clone());
                Op::underscore(&node, op.typ())
            },
            Node::Op(op, _) => self.trans_clos_op(op.clone()),
            Node::Transcr(op, _) => {
                // Add the node to the context
                let op = self.trans_clos_op(op.clone());
                self.clos.insert(&node.index(), &op.clone());

                // Add the transcript parent to the context if it does not exist
                let tr_edge =
                    self.dag.transcript_edge(node, Direction::Incoming).unwrap();

                if !self.clos.contains(&tr_edge.source().index()) {
                    self.trans_clos_node(tr_edge.source());
                }
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
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc.clos);
    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }
}
