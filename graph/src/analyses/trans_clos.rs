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
    pub clos: Ctx<NodeIndex, GOp<C>>,
    pub visibility: Ctx<Ref, Qualifier>,
    pub types: Ctx<Ref, ATyp>,
    pub annotations: Ctx<Ref, A>,
}

impl<C: ArkConfig, A: Clone> TransClos<C, A> {
    pub fn new(dag: Dag<C, A>, subgraph: usize) -> Self {

        // Empty transitive closure
        let mut s = Self {
            clos: Ctx::new(),
            visibility: Ctx::new(),
            types: Ctx::new(),
            annotations: Ctx::new(),
        };

        // Find all input nodes to the graph, that is the number
        // of subgraphs.
        let input_nodes = dag.0.node_indices()
            .filter(|n| dag[*n].is_input())
            .collect::<Vec<_>>();

        if subgraph >= input_nodes.len() {
            panic!("Subgraph index out of bounds {} >= {}", subgraph, input_nodes.len());
        }

        // Add the input node to the transitive closure
        let mut worklist = vec![input_nodes[subgraph]];
        s.trans_clos_inp(&dag, input_nodes[subgraph]);

        println!("AFTER ADDING INPUT NODE: {}", input_nodes[subgraph].index());
        println!("{:?}", s.visibility);
        // Add all nodes reachable from the input node
        // (should be a DAG but adding this just in case to avoid spinning on bugs)
        let mut done = vec![];
        while let Some(node) = worklist.pop() {
            if !done.contains(&node) {
                worklist.extend(dag.nodes_from(node));
                done.push(node);
                if dag[node].is_op() {
                    s.trans_clos_node(&dag, node);
                }
            }
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

    fn trans_clos_inp(&mut self, dag: &Dag<C, A>, node: NodeIndex) {
        // Add variables to the context
        if let Node::Inp(_, ref args) = dag[node] {
            for (v, (q, typ)) in args.iter() {
                // Add the variable to the context
                self.visibility.insert(&Ref::Var(v.clone(), node), q);
                self.types.insert(&Ref::Var(v.clone(), node), typ);
            }
        }
    }

    fn trans_clos_op(&mut self, dag: &Dag<C, A>, op: GOp<C>) -> GOp<C> {
        match op {
            Op::Ref(Ref::Node(n), _) => self.trans_clos_node(dag, n),
            Op::Ref(Ref::Var(v, n), typ) => Op::var(&v, n, typ),
            Op::Bin(op, box a, box b, typ) => {
                let oa = self.trans_clos_op(dag, a);
                let ob = self.trans_clos_op(dag, b);
                Op::bin(op, oa, ob, typ.clone())
            },
            Op::Ram(box a, box b) => {
                let oa = self.trans_clos_op(dag, a);
                let ob = self.trans_clos_op(dag, b);
                Op::Ram(Box::new(oa), Box::new(ob))
            },
            Op::Value(v) => Op::Value(v),
            Op::Vec(vs) =>
                Op::Vec(vs.into_iter().map(|v| self.trans_clos_op(dag, v))
                    .collect::<Vec<_>>()),
            Op::Check(box op) => self.trans_clos_op(dag, op),
            Op::Coef(box v) => Op::Coef(Box::new(self.trans_clos_op(dag, v))),
            Op::Eval(box v) => Op::Eval(Box::new(self.trans_clos_op(dag, v))),
            op => op
        }
    }

    fn find_or_insert(&mut self, n: NodeIndex, op: GOp<C>) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&n) {
            return Op::underscore(n, op.typ());
        }
        // Otherwise add it
        self.clos.insert(&n, &op);

        // Return it
        Op::Ref(Ref::Node(n), op.typ())
    }

    fn trans_clos_node(&mut self, dag: &Dag<C, A>, node: NodeIndex) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.clos.get(&node) {
            return Op::underscore(node, op.typ());
        }
        // Otherwise add it
        match &dag[node] {
            Node::Op(op @ (Op::Challenge(_) | Op::Gen(_) | Op::Random(_)), ann) => {
                self.clos.insert(&node, &op);
                self.types.insert(&Ref::Node(node), &op.typ());
                self.annotations.insert(&Ref::Node(node), ann);
                Op::underscore(node, op.typ())
            },
            Node::Op(op, ann) => {
                let obin = self.trans_clos_op(dag, op.clone());
                let refer = Ref::Node(node);
                self.types.insert(&refer, &op.typ());
                self.annotations.insert(&refer, ann);
                self.find_or_insert(node, obin.clone())
            },
            Node::Transcr(op, ann) => {
                // Add the node to the context
                let op = self.trans_clos_op(dag, op.clone());
                let refer = Ref::Node(node);
                self.types.insert(&refer, &op.typ());
                self.annotations.insert(&refer, ann);
                self.visibility.insert(&refer, &Qualifier::Public);
                self.find_or_insert(node, op.clone())
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
fn trans_clos_simple() {
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
    let tc = TransClos::new(g, 0);

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

#[test]
fn trans_clos_many() {
    let ex = r#"
        proto foo<F: Field, N: 2..4>(private s: [F; N], private s': F, public i: Fin<2>) where s == s {
            let r = random<F>;
            a <- r * s[i];
            b <- r * s';
            verify(a == b);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Compute transitive closure
    let tc = TransClos::new(g, 1);

    println!("{}", tc);
    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }
}
