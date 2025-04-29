use crate::{GOp, Op, Ref, Node, Dag};
use petgraph::{
    graph::NodeIndex,
    visit::EdgeRef,
    Direction,
};
use std::fmt;
use share::{Set, Ctx};
use lang::typ::Qualifier;
use backend::{ATyp, ArkConfig};

/// Transitive closure on a DAG
#[derive(Clone)]
pub struct TransClos<C: ArkConfig, A> {
    dag: Dag<C, A>,
    pub clos: Ctx<NodeIndex, GOp<C>>,
    pub visibility: Ctx<Ref, Qualifier>,
    pub types: Ctx<Ref, ATyp>,
}

impl<C: ArkConfig, A> TransClos<C, A> {
    pub fn new(dag: Dag<C, A>) -> Self where A: Clone {
        let node_indices = dag.0.node_indices()
            .filter(|n| dag.0[*n].is_op())
            .collect::<Vec<_>>();

        // Empty transitive closure
        let mut s = Self {
            dag,
            clos: Ctx::new(),
            visibility: Ctx::new(),
            types: Ctx::new(),
        };
        // Compute transitive closure
        for node in node_indices {
            s.trans_clos_node(node);
        }
        s
    }

    /// Iterate over the transitive closure
    pub fn iter(&self) -> impl Iterator<Item = (&NodeIndex, &GOp<C>)> {
        self.clos.iter()
    }

    /// Get the public references
    pub fn public(&self) -> Set<Ref> {
        self.visibility.iter()
            .filter(|(_, q)| **q == Qualifier::Public)
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Get the private references
    pub fn private(&self) -> Set<Ref> {
        self.visibility.iter()
            .filter(|(_, q)| **q == Qualifier::Private)
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Get the input variables
    pub fn vars(&self) -> Set<Ref> {
        self.visibility.iter()
            .filter(|(r, _)| matches!(r, Ref::Var(_, _)))
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// Rebuild the transcript operations (public nodes)
    pub fn transcript(&self) -> Vec<(Ref, GOp<C>)> {
        self.clos.iter()
            .filter_map(|(node, op)| {
                let rf = Ref::Node(*node);
                if self.visibility.get(&rf) == Some(&Qualifier::Public) {
                    Some((rf, op.clone()))
                } else {
                    None
                }
            }).collect()
    }

    /// Inline an operation using the transitive closure, except for the nodes specified
    /// which remain as node identifiers.
    pub fn inline<F: Fn(NodeIndex, &GOp<C>)->bool> (&self, op: &GOp<C>, except: &F) -> GOp<C> {
        match op {
            Op::Ref(Ref::Node(n), _) =>
                if let Some(next) = self.clos.get(&n) {
                    if except(*n, next) {
                        return op.clone();
                    }
                    self.inline(next, except)
                } else {
                    op.clone()
                },
            Op::Bin(op, box a, box b, typ) => {
                let oa = self.inline(a, except);
                let ob = self.inline(b, except);
                Op::bin(*op, oa, ob, typ.clone())
            },
            Op::Ram(box a, box b) => {
                let oa = self.inline(a, except);
                let ob = self.inline(b, except);
                Op::Ram(Box::new(oa), Box::new(ob))
            },
            Op::Vec(vs) =>
                Op::Vec(vs.into_iter().map(|v| self.inline(v, except))
                    .collect::<Vec<_>>()),
            Op::Check(box op) => self.inline(op, except),
            Op::Coef(box v) => Op::Coef(Box::new(self.inline(v, except))),
            Op::Eval(box v) => Op::Eval(Box::new(self.inline(v, except))),
            op => op.clone()
        }
    }

    fn trans_clos_op(&mut self, op: GOp<C>) -> GOp<C> {
        match op {
            Op::Ref(Ref::Node(n), _) => self.trans_clos_node(n),
            Op::Ref(Ref::Var(v, n), typ) =>
                match self.dag.0[n] {
                    Node::Inp(_, ref args) => {
                        // Add input variable's visibility
                        if let Some((q, typ)) = args.get(&v) {
                            self.visibility.insert(&(&v).into(), q);
                            self.types.insert(&(&v).into(), typ);
                        }
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

    fn find_or_insert(&mut self, n: NodeIndex, op: GOp<C>, q: Option<Qualifier>) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&n) {
            return Op::underscore(n, op.typ());
        }
        // Otherwise add it
        self.clos.insert(&n, &op);
        let refer = Ref::Node(n);

        // Record its type
        self.types.insert(&refer, &op.typ());
        // Record its visibility if given
        if let Some(q) = q {
            self.visibility.insert(&refer, &q);
        }
        // Return it
        Op::Ref(refer, op.typ())
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
                self.types.insert(&Ref::Node(node), &op.typ());
                Op::underscore(node, op.typ())
            },
            Node::Op(op, _) => {
                let obin = self.trans_clos_op(op.clone());
                self.find_or_insert(node, obin.clone(), None)
            },
            Node::Transcr(op, _) => {
                // Add the node to the context
                let op = self.trans_clos_op(op.clone());
                let op = self.find_or_insert(node, op.clone(), Some(Qualifier::Public));

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
        write!(f, "TC: \n")?;
        self.clos.iter().map(|(n, op)|
            write!(f, "\t{}: {}\n", n.index(), op))
            .collect::<fmt::Result>()?;
        write!(f, "\nTypes: \n")?;
        self.types.iter().map(|(n, typ)|
            write!(f, "\t{}: {}\n", n, typ))
            .collect::<fmt::Result>()?;
        write!(f, "\nVisibility: \n")?;
        self.visibility.iter().map(|(n, q)|
            write!(f, "\t{}: {}\n", n, q))
            .collect::<fmt::Result>()
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use lang::typ::Range;
#[cfg(test)] use crate::UDag;
#[cfg(test)] use share::{assert_deq, unwrap};
#[cfg(test)] use backend::{Value, ArkBls12_381};
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

    println!("{}", tc);
    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }

    // Check that inlining works
    assert_deq!(
        tc.inline(tc.clos.last().unwrap().1, &|n, _| n == NodeIndex::new(1)),
        Op::equ(
            Op::mul(
                Op::underscore(NodeIndex::new(1), ATyp::Scalar),
                Op::ram(
                    Op::var(&"s".into(), NodeIndex::new(0), ATyp::vec(&ATyp::Scalar, 10)),
                    Op::add(
                        Op::var(&"i".into(), NodeIndex::new(0), ATyp::Fin(Range::new(0, 5))),
                        Op::Value(Value::Index(2)),
                        ATyp::Fin(Range::new(2, 7))
                    )
                ),
                ATyp::Scalar
            ),
            Op::mul(
                Op::underscore(NodeIndex::new(1), ATyp::Scalar),
                Op::var(&"s'".into(), NodeIndex::new(0), ATyp::Scalar),
                ATyp::Scalar
            )
        )
    )

}
