use backend::ArkConfig;
use petgraph::graph::NodeIndex;
use share::Ctx;
use lang::typ::Qualifier;
use crate::{Dag, UDag, Node, Ref, QDag, GOp};

pub struct QualifierPropagation {
    pub quals: Ctx<NodeIndex, Qualifier>,
}

/// Propagate qualifiers [private, public] through the DAG
impl QualifierPropagation {
    pub fn new() -> Self {
        QualifierPropagation { quals: Ctx::new() }
    }
    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Qualifier {
        match op {
            GOp::Value(_) => Qualifier::Public,
            GOp::Check(_) => Qualifier::Public,
            GOp::Ref(r, _) => *self.quals.get(&r.node()).unwrap(),
            GOp::Ram(box a, _) => self.from_op(a),
            GOp::Coef(box a) => self.from_op(a),
            GOp::Eval(box a) => self.from_op(a),
            GOp::Bin(_, box a, box b, _) => {
                let qual_a = self.from_op(a);
                let qual_b = self.from_op(b);
                qual_a.join(&qual_b)
            }
            GOp::Vec(vs) =>
                vs.iter().fold(Qualifier::Public, |acc, op| acc.join(&self.from_op(op))),
            GOp::Random(_) => Qualifier::Private,
            GOp::Challenge(_) => Qualifier::Public,
        }
    }

    pub fn with_dag<C: ArkConfig>(&mut self, dag: &UDag<C>) -> QDag<C> {
        let inp = dag.input_node();
        let mut worklist = vec![inp];
        while let Some(node) = worklist.pop() {
            if self.quals.contains(&node) {
                continue;
            }
            match &dag[node] {
                Node::Inp(_, args) | Node::Rel(_, args) => {
                    for arg in args {
                        self.quals.insert(&arg.reference.node(), &arg.qualifier);
                    }
                },
                Node::Transcr(_, _) => {
                    self.quals.insert(&node, &Qualifier::Public);
                }
                Node::Op(op, _) => {
                    let qual = self.from_op(&op);
                    self.quals.insert(&node, &qual);
                },
            }
            for next in dag.nodes_from(node) {
                if !self.quals.contains(&next) {
                    worklist.push(next);
                }
            }
        }

        Dag(dag.0.map(
            |i, node|
                node.with_annotation(self.quals.get(&i).unwrap_or_else(|| &Qualifier::Private).clone()),
            |_, e| e.clone()))
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::UDags;
#[cfg(test)] use share::unwrap;
#[test]
fn qualifier_prop() {
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
    let mut qp = QualifierPropagation::new();
    let g = qp.with_dag(&gs[0]);

    g.write_pdf("qualifier.pdf").unwrap();
}
