use crate::{GOp, Op, Ref, Node, Dag};
use lang::typ::Qualifier;
use petgraph::{
    graph::NodeIndex,
    visit::EdgeRef,
    Direction,
};
use std::fmt;
use share::Ctx;
use backend::{ArkConfig, ATyp};

/// Transitive closure on a DAG
pub struct TransClos<C: ArkConfig, A> {
    dag: Dag<C, A>,
    pub clos: Ctx<NodeIndex, GOp<C>>,
    pub public: Ctx<Ref, ATyp>,
    pub private: Ctx<Ref, ATyp>,
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
            public: Ctx::new(),
            private: Ctx::new(),
        };
        // Compute transitive closure
        for node in node_indices {
            let op = s.trans_clos_node(node);
            if matches!(op, Op::Ref(Ref::Node(_), _)) {
                s.clos.insert(&last, &op);
            }
        }
        s
    }

    pub fn public(&self) -> &Ctx<Ref, ATyp> {
        &self.public
    }

    fn trans_clos_op(&mut self, op: GOp<C>) -> GOp<C> {
        match op {
            Op::Ref(Ref::Node(n), _) => self.trans_clos_node(n),
            Op::Ref(Ref::Var(v, n), typ) =>
                match self.dag.0[n] {
                    Node::Inp(_, ref args) => {
                        match args.get(&v) {
                            Some((Qualifier::Public, typ)) => self.public.insert(&(&v).into(), typ),
                            Some((Qualifier::Private, typ)) => self.private.insert(&(&v).into(), typ),
                            _ => None
                        };
                        Op::var(&v, n, typ)
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
            Op::Vec(vs) =>
                Op::Vec(vs.into_iter().map(|v| self.trans_clos_op(v))
                    .collect::<Vec<_>>()),
            Op::Check(box op) => self.trans_clos_op(op),
            Op::Coef(box v) => Op::Coef(Box::new(self.trans_clos_op(v))),
            Op::Eval(box v) => Op::Eval(Box::new(self.trans_clos_op(v))),
            op => op
        }
    }

    fn find_or_insert_public(&mut self, n: NodeIndex, op: GOp<C>) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&n) {
            return Op::underscore(n, op.typ());
        }
        // Otherwise add it
        self.clos.insert(&n, &op);
        self.public.insert(&Ref::Node(n), &op.typ());
        Op::underscore(n, op.typ())
    }

    fn find_or_insert_private(&mut self, n: NodeIndex, op: GOp<C>) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&n) {
            return Op::underscore(n, op.typ());
        }
        // Otherwise add it
        self.clos.insert(&n, &op);
        self.private.insert(&Ref::Node(n), &op.typ());
        Op::underscore(n, op.typ())
    }
    fn trans_clos_node(&mut self, node: NodeIndex) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&node) {
            return Op::underscore(node, op.typ());
        }
        // Otherwise add it
        match &self.dag.0[node] {
            Node::Op(op @ (Op::Challenge(_) | Op::Gen(_) | Op::Random(_)), _) => {
                self.clos.insert(&node, &op);
                self.private.insert(&Ref::Node(node), &op.typ());
                Op::underscore(node, op.typ())
            },
            Node::Op(op, _) => {
                let obin = self.trans_clos_op(op.clone());
                self.find_or_insert_private(node, obin.clone())
            },
            Node::Transcr(op, _) => {
                // Add the node to the context
                let op = self.trans_clos_op(op.clone());
                let op = self.find_or_insert_public(node, op.clone());

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

impl<C: ArkConfig, A: fmt::Display> fmt::Display for TransClos<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\n")?;
        self.clos.iter().map(|(n, op)|
            write!(f, "\t{}: {}\n", n.index(), op))
            .collect::<fmt::Result>()
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use crate::UDag;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn trans_clos_foo() {
    let ex = r#"
        proto foo<F: Field>(private s: [F; 10], private s': F, public i: Fin<5>) where s == s {
            let r = random<F>;
            a <- r * s[i + 2];
            b <- r * s';
            verify(a == b);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc);
    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }
    println!("Public nodes: {}", tc.public);
}
