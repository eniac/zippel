use crate::{Op, Node, Dag};
use lang::typ::Qualifier;
use petgraph::{
    graph::NodeIndex,
    visit::EdgeRef,
    Graph,
    Direction,
};
use share::{Set, Ctx};
use backend::ArkConfig;

/// Transitive closure on a DAG
pub struct TransClos<C: ArkConfig, A> {
    dag: Dag<C, A>,
    pub clos: Ctx<usize, Op<C>>,
    pub public: Set<String>,
    pub private: Set<String>,
}

impl<C: ArkConfig, A> TransClos<C, A> {
    pub fn new(dag: Dag<C, A>) -> Self where A: Clone {
        // Maximum node
        let last = dag.max_node();

        let node_indices = dag.0.node_indices()
            .filter(|n| dag.0[*n].is_op())
            .collect::<Vec<_>>();

        // Empty transitive closure
        let mut s = Self {
            dag,
            clos: Ctx::new(),
            public: Set::new(),
            private: Set::new(),
        };
        // Compute transitive closure
        for node in node_indices {
            let op = s.trans_clos_node(node);
            if !op.is_underscore() {
                s.clos.insert(&last.index(), &op);
            }
        }
        s
    }

    pub fn closure(&self) -> &Ctx<usize, Op<C>> {
        &self.clos
    }

    pub fn public(&self) -> &Set<String> {
        &self.public
    }

    pub fn max_node(&self) -> usize {
        self.dag.max_node().index().max(*self.clos.keys().iter().max().unwrap_or(&0))
    }

    fn trans_clos_op(&mut self, op: Op<C>) -> Op<C> {
        match op {
            Op::Underscore(n, _) => self.trans_clos_node(n),
            Op::Var(v, n, typ) =>
                match self.dag.0[n] {
                    Node::Inp(_, ref args) => {
                        match args.get(&v) {
                            Some((Qualifier::Public, _)) => self.public.insert(v.0.clone()),
                            Some((Qualifier::Private, _)) => self.private.insert(v.0.clone()),
                            _ => false
                        };
                        Op::Var(v, n, typ)
                    },
                    _ => self.trans_clos_node(n),
                },
            Op::Bin(op, box a, box b, typ) => {
                let oa = self.trans_clos_op(a);
                let ob = self.trans_clos_op(b);
                Op::bin(op, oa, ob, typ.clone())
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
            Op::Check(box op) => self.trans_clos_op(op),
            Op::Coef(box v) => Op::Coef(Box::new(self.trans_clos_op(v))),
            Op::Eval(box v) => Op::Eval(Box::new(self.trans_clos_op(v))),
            op => op
        }
    }

    fn find_or_insert(&mut self, n: NodeIndex, op: Op<C>) -> Op<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&n.index()) {
            return Op::underscore(&n, op.typ());
        }
        // Otherwise add it
        self.clos.insert(&n.index(), &op);
        Op::underscore(&n, op.typ())
    }

    fn trans_clos_node(&mut self, node: NodeIndex) -> Op<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&node.index()) {
            return Op::underscore(&node, op.typ());
        }
        // Otherwise add it
        match &self.dag.0[node] {
            Node::Op(op @ (Op::Challenge(_) | Op::Gen(_) | Op::Random(_)), _) => {
                self.clos.insert(&node.index(), &op.clone());
                Op::underscore(&node, op.typ())
            },
            Node::Op(op, _) => {
                let obin = self.trans_clos_op(op.clone());
                self.find_or_insert(node, obin.clone())
            },
            Node::Transcr(op, _) => {
                // Add the node to the context
                let op = self.trans_clos_op(op.clone());
                let op = self.find_or_insert(node, op.clone());

                // Add it to public nodes
                self.public.insert(format!("#{}", node.index()));

                // Add the transcript parent to the context if it does not exist
                let tr_edge =
                    self.dag.transcript_edge(node, Direction::Incoming).unwrap();

                // Input nodes are already in the transitive closure
                if !self.dag.0[tr_edge.source()].is_input() {
                    self.trans_clos_node(tr_edge.source());
                }
                op
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
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            a <- r * s;
            b <- r * s';
            verify(a == b);
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
    println!("Public nodes: {}", tc.public);
}
