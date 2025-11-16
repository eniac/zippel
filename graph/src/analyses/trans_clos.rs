use crate::{Dag, GOp, Node, Op, PRef, DQDag, Ref, StaticAnalysis};
use petgraph::graph::NodeIndex;
use std::fmt;
use lang::typ::{Distribution, Qualifier};
use backend::ArkConfig;

#[cfg(test)] use backend::ATyp;

/// Transitive closure on a DAG
#[derive(Clone)]
pub struct TransClos<C: ArkConfig> {
    pub clos: Vec<(PRef, GOp<C>)>,
    pub args: Vec<PRef>,
}

impl<C: ArkConfig> TransClos<C> {
    pub fn from_input(dag: &DQDag<C>) -> Self {
        let start = dag.input_node();
        Self::new(&dag, start)
    }

    pub fn from_relation(dag: &DQDag<C>) -> Self {
        let start = dag.relation_node().unwrap();
        Self::new(&dag, start)
    }

    pub fn new(dag: &DQDag<C>, start: NodeIndex) -> Self {
        // Empty transitive closure
        let mut s = Self {
            clos: Vec::new(),
            args: Vec::new(),
        };

        // Add the input node to the transitive closure
        let mut worklist = vec![start];
        s.trans_clos_start(&dag, start);

        // Add all nodes reachable from the input node
        // (should be a DAG but adding this just in case to avoid spinning on bugs)
        let mut done = vec![];
        while let Some(node) = worklist.pop() {
            if !done.contains(&node) {
                worklist.extend(dag.nodes_from(node));
                done.push(node);
                if dag[node].is_op() {
                    s.trans_clos_ref(dag, dag.find_ref(node));
                }
            }
        }
        s
    }

    /// Iterate over the transitive closure
    pub fn iter<'a>(&'a self) -> std::slice::Iter<'a, (PRef, GOp<C>)> {
        self.clos.iter()
    }

    /// Rebuild the transcript operations (public nodes)
    pub fn transcript(&self) -> Vec<(PRef, GOp<C>)> {
        self.clos.iter()
            .filter_map(|(rf, op)|
                if rf.is_public() {
                    Some((rf.clone(), op.clone()))
                } else {
                    None
                })
            .collect()
    }

    fn trans_clos_start<A>(&mut self, dag: &Dag<C, A>, node: NodeIndex) {
        match &dag[node] {
            Node::Inp(_, args) => self.args = args.clone(),
            Node::Rel(_, args) => self.args = args.clone(),
            _ => unreachable!("Start node should be an input or relation node"),
        }
    }

    fn trans_clos_op(&mut self, dag: &DQDag<C>, op: GOp<C>) -> GOp<C> {
        match op {
            Op::Ref(r, _) => self.trans_clos_ref(dag, r),
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
            Op::Ifft(box v) => Op::Ifft(Box::new(self.trans_clos_op(dag, v))),
            Op::Fft(box v) => Op::Fft(Box::new(self.trans_clos_op(dag, v))),
            op => op
        }
    }

    pub fn find(&self, r: &Ref) -> Option<&GOp<C>> {
        self.clos.iter()
            .find(|(n, _)| &n.reference == r)
            .map(|(_, op)| op)
    }

    pub fn last(&self) -> Option<(PRef, GOp<C>)> {
        self.clos.last()
            .map(|(n, op)| (n.clone(), op.clone()))
    }

    /// Find a node and return it, or insert it if it doesn't exist
    fn insert(&mut self, r: PRef, op: GOp<C>) -> GOp<C> {
        // Look for the node, by node index
        if let Some(index) = self.clos.iter().position(|(r2, _)| r2.node() == r.node()) {
            if r.reference.is_var() {
                // Check if the node is a variable, then remove the old node and substitute it
                self.clos.swap_remove(index);
            }
        }
        self.clos.push((r.clone(), op.clone()));
        // Return it
        Op::Ref(r.reference, op.typ())
    }

    fn trans_clos_ref(&mut self, dag: &DQDag<C>, r: Ref) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.find(&r) {
            return Op::Ref(r, op.typ());
        }
        // Otherwise add it
        match &dag[r.node()] {
            Node::Op(op @ (Op::Challenge(_, _) | Op::Random(_, _)), (qualifier, distribution))
            | Node::Transcr(op @ (Op::Challenge(_, _) | Op::Random(_, _)), (qualifier, distribution)) => {
                let pref = PRef::from_ref(r.clone(), op.typ(), *qualifier, *distribution);
                self.insert(pref, op.clone());
                Op::Ref(r, op.typ())
            },
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution)) => {
                let obin = self.trans_clos_op(dag, op.clone());
                self.insert(PRef::from_ref(r, op.typ(), *qualifier, *distribution), obin.clone())
            },
            Node::Inp(_, args) | Node::Rel(_, args) =>
                if let Some(ref v) = r.var() {
                    let pref = args.iter().find(|pr| pr.has_var(v)).unwrap();
                    Op::Ref(r, pref.typ.clone())
                } else {
                    unreachable!("Input and relation node should only have variable dependencies")
                },
        }
    }
}

impl<C: ArkConfig> fmt::Display for TransClos<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Args: {}\n", self.args.iter().map(|n| n.verbose()).collect::<Vec<_>>().join(", "))?;
        write!(f, "\nTC: \n")?;
        self.clos.iter().map(|(n, op)|
            write!(f, "\t{}   |   {} \n", n.verbose(), op))
            .collect::<fmt::Result>()
    }
}

impl<C: ArkConfig> StaticAnalysis<C, (Qualifier, Distribution)> for TransClos<C> {
    type Args = ();
    type Output = Self;

    fn new(g: &DQDag<C>) -> Self {
        Self::from_input(g)
    }

    fn run(&mut self, _: ()) -> Self {
        self.clone()
    }
}


#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use lang::typ::Range;
#[cfg(test)] use crate::{analyses::{QualifierPropagation, UniformityPropagation}, UDags};
#[cfg(test)] use share::{Ctx, assert_deq, unwrap};
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
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    // Compute transitive closure
    let tc = TransClos::from_input(&g);

    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }

    // Check that inlining works
    let last_op = tc.last().unwrap().1;
    let ref_vars = 
        tc.clos.into_iter().map(|(r, op)| (r.reference, op)).collect::<Ctx<_, _>>();
    assert_deq!(
        last_op.inline(&ref_vars, &|r, _| matches!(r, Ref::Var(v, _) if v == &"r".into())),
        Op::equ(
            Op::mul(
                Op::var(&"r".into(), NodeIndex::new(1), ATyp::scalar()),
                Op::ram(
                    Op::var(&"s".into(), NodeIndex::new(0), ATyp::vec_scalar(10)),
                    Op::add(
                        Op::var(&"i".into(), NodeIndex::new(0), ATyp::fin(Range::new(0, 5))),
                        Op::Value(Value::Index(2)),
                        ATyp::fin(Range::new(2, 7))
                    )
                ),
                ATyp::scalar()
            ),
            Op::mul(
                Op::var(&"r".into(), NodeIndex::new(1), ATyp::scalar()),
                Op::var(&"s'".into(), NodeIndex::new(0), ATyp::scalar()),
                ATyp::scalar()
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
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    // Compute transitive closure
    let tc = TransClos::from_input(&g);

    println!("{}", tc);
    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }
}
