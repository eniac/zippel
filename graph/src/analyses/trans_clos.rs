use crate::{DQDag, Dag, GOp, Node, Op, PRef, Ref, StaticAnalysis, mk};
use backend::ArkConfig;
use backend::op::HasOpFactory;
use lang::typ::{Distribution, Qualifier};
#[cfg(test)]
use log::debug;
use petgraph::graph::NodeIndex;
use std::fmt;

/// Transitive closure on a DAG
#[derive(Clone)]
pub struct TransClos<C: ArkConfig> {
    pub clos: Vec<(PRef, GOp<C>)>,
    pub args: Vec<PRef>,
}

impl<C: ArkConfig + HasOpFactory> TransClos<C> {
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
        self.clos
            .iter()
            .filter_map(|(rf, op)| {
                if rf.is_public() {
                    Some((rf.clone(), op.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    fn trans_clos_start<A>(&mut self, dag: &Dag<C, A>, node: NodeIndex) {
        match &dag[node] {
            Node::Inp(_) | Node::Rel(_) => {
                // Phase B: collect Arg children of the marker node.
                let mut args: Vec<NodeIndex> =
                    dag.nodes_from(node).filter(|n| dag[*n].is_arg()).collect();
                args.sort();
                self.args = args
                    .into_iter()
                    .filter_map(|n| dag[n].arg_pref(n))
                    .collect();
            }
            _ => unreachable!("Start node should be an input or relation node"),
        }
    }

    fn trans_clos_op(&mut self, dag: &DQDag<C>, op: GOp<C>) -> GOp<C> {
        match op {
            Op::Ref(r, _) => self.trans_clos_ref(dag, r),
            Op::Bin(op, a, b, typ) => {
                let oa = self.trans_clos_op(dag, a.get().clone());
                let ob = self.trans_clos_op(dag, b.get().clone());
                Op::bin(op, oa, ob, typ.clone())
            }
            Op::Ram(a, b) => {
                let oa = self.trans_clos_op(dag, a.get().clone());
                let ob = self.trans_clos_op(dag, b.get().clone());
                Op::Ram(mk::<C>(oa), mk::<C>(ob))
            }
            Op::Value(v) => Op::Value(v),
            Op::Vec(vs) => Op::Vec(
                vs.into_iter()
                    .map(|v| mk::<C>(self.trans_clos_op(dag, v.get().clone())))
                    .collect::<Vec<_>>(),
            ),
            Op::Check(op) => self.trans_clos_op(dag, op.get().clone()),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(self.trans_clos_op(dag, points.get().clone())),
                mk::<C>(self.trans_clos_op(dag, evals.get().clone())),
            ),
            Op::Ifft(v) => Op::Ifft(mk::<C>(self.trans_clos_op(dag, v.get().clone()))),
            Op::Fft(v) => Op::Fft(mk::<C>(self.trans_clos_op(dag, v.get().clone()))),
            Op::Reduce(op, v) => Op::Reduce(op, mk::<C>(self.trans_clos_op(dag, v.get().clone()))),
            Op::Eval(p, xs) => Op::Eval(
                mk::<C>(self.trans_clos_op(dag, p.get().clone())),
                mk::<C>(self.trans_clos_op(dag, xs.get().clone())),
            ),
            Op::Poly(v) => Op::Poly(mk::<C>(self.trans_clos_op(dag, v.get().clone()))),
            Op::Mle(v) => Op::Mle(mk::<C>(self.trans_clos_op(dag, v.get().clone()))),
            Op::Coef(v) => Op::Coef(mk::<C>(self.trans_clos_op(dag, v.get().clone()))),
            op => op
        }
    }

    pub fn find(&self, r: &Ref) -> Option<&GOp<C>> {
        self.clos
            .iter()
            .find(|(n, _)| &n.reference == r)
            .map(|(_, op)| op)
    }

    pub fn last(&self) -> Option<(PRef, GOp<C>)> {
        self.clos.last().map(|(n, op)| (n.clone(), op.clone()))
    }

    /// Find a node and return it, or insert it if it doesn't exist
    fn insert(&mut self, r: PRef, op: GOp<C>) -> GOp<C> {
        // Phase B: refs are unique per NodeIndex; one entry per node.
        if !self.clos.iter().any(|(r2, _)| r2.node() == r.node()) {
            self.clos.push((r.clone(), op.clone()));
        }
        Op::Ref(r.reference, op.typ())
    }

    fn trans_clos_ref(&mut self, dag: &DQDag<C>, r: Ref) -> GOp<C> {
        // Check if the node is already in the context
        if let Some(op) = self.find(&r) {
            return Op::Ref(r, op.typ());
        }
        // Otherwise add it
        match &dag[r.node()] {
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution))
                if matches!(op.get(), Op::Challenge(_, _) | Op::Random(_, _)) =>
            {
                let inner = op.get();
                let pref = PRef::from_ref(r.clone(), inner.typ(), *qualifier, *distribution);
                self.insert(pref, inner.clone());
                Op::Ref(r, inner.typ())
            }
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution)) => {
                let obin = self.trans_clos_op(dag, op.get().clone());
                self.insert(
                    PRef::from_ref(r, op.typ(), *qualifier, *distribution),
                    obin.clone(),
                )
            }
            Node::Arg(_, t, _, _, _) => Op::Ref(r, t.clone()),
            Node::Inp(_) | Node::Rel(_) => {
                unreachable!("Input/relation marker should not be referenced directly")
            }
        }
    }
}

impl<C: ArkConfig> fmt::Display for TransClos<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Args: {}\n",
            self.args
                .iter()
                .map(|n| n.verbose())
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        write!(f, "\nTC: \n")?;
        self.clos
            .iter()
            .map(|(n, op)| write!(f, "\t{}   |   {} \n", n.verbose(), op))
            .collect::<fmt::Result>()
    }
}

impl<C: ArkConfig + HasOpFactory> StaticAnalysis<C, (Qualifier, Distribution)> for TransClos<C> {
    type Args = ();
    type Output = Self;

    fn new(g: &DQDag<C>) -> Self {
        Self::from_input(g)
    }

    fn run(&mut self, _: ()) -> Self {
        self.clone()
    }
}

#[cfg(test)]
use crate::{
    UDags,
    analyses::{QualifierPropagation, UniformityPropagation},
};
#[cfg(test)]
use backend::ArkBls12_381;
#[cfg(test)]
use lang::ast::UModule;
#[cfg(test)]
use share::{Ctx, unwrap};
#[test]
fn trans_clos_simple() {
    let ex = r#"
        proto foo<F: Field>(private s: [F; 10], private s': F, public i: Fin<5>) where s == s {
            let r = random<F>;
            a <- r * s[i + 2];
            b <- r * s';
            verify(a == b)
        }"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);

    let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

    // Compute transitive closure
    let tc = TransClos::from_input(&g);

    for (_, op) in tc.clos.iter() {
        assert!(!matches!(op, Op::Bin(_, a, _, _) if matches!(a.get(), Op::Bin(_, _, _, _))));
        assert!(!matches!(op, Op::Bin(_, _, b, _) if matches!(b.get(), Op::Bin(_, _, _, _))));
    }

    // Check that inlining works (Phase B: Refs no longer carry Vid).
    let _last_op = tc.last().unwrap().1;
    let _ref_vars = tc
        .clos
        .into_iter()
        .map(|(r, op)| (r.reference, op))
        .collect::<Ctx<_, _>>();
}

#[test]
fn trans_clos_many() {
    let ex = r#"
        proto foo<F: Field, N: 2..4>(private s: [F; N], private s': F, public i: Fin<2>) where s == s {
            let r = random<F>;
            a <- r * s[i];
            b <- r * s';
            verify(a == b)
        }"#;
    let m = UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);

    let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

    // Compute transitive closure
    let tc = TransClos::from_input(&g);

    debug!("{}", tc);
    for (_, op) in tc.clos.iter() {
        assert!(!matches!(op, Op::Bin(_, a, _, _) if matches!(a.get(), Op::Bin(_, _, _, _))));
        assert!(!matches!(op, Op::Bin(_, _, b, _) if matches!(b.get(), Op::Bin(_, _, _, _))));
    }
}
