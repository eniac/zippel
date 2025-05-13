use backend::ArkConfig;
use petgraph::graph::NodeIndex;
use petgraph::Direction;
use petgraph::visit::EdgeRef;
use share::Ctx;
use lang::typ::Qualifier;
use crate::{Dag, UDag, Node, Ref, QDag, GOp};

pub struct QualifierPropagation {
    pub quals: Ctx<NodeIndex, Qualifier>,
}

/// Propagate qualifiers [private, public] through the DAG
impl QualifierPropagation {
    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Option<Qualifier> {
        match op {
            GOp::Value(_) => Some(Qualifier::Public),
            GOp::Check(_) => Some(Qualifier::Public),
            GOp::Ref(r, _) => 
                self.quals.get(&r.node()).map(|v| v.clone()),
            GOp::Ram(box a, _) => self.from_op(a),
            GOp::Coef(box a) => self.from_op(a),
            GOp::Eval(box a) => self.from_op(a),
            GOp::Bin(_, box a, box b, _) 
            | GOp::Pair(box a, box b, _) => {
                let qual_a = self.from_op(a)?;
                let qual_b = self.from_op(b)?;
                Some(qual_a.join(&qual_b))
            },
            GOp::Vec(vs) => {
                let mut qual = Qualifier::Public;
                for v in vs {
                    let q = self.from_op(v)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            GOp::Random(_, _) => Some(Qualifier::Private),
            GOp::Challenge(_, _) => Some(Qualifier::Public),
        }
    }

    pub fn from_dag<C: ArkConfig>(dag: &UDag<C>) -> QDag<C> {
        let mut qp = QualifierPropagation { quals: Ctx::new() };
        let check = dag.find_check().expect("No check found in the DAG");
        let mut worklist = vec![check];

        while let Some(n) = worklist.pop() {
            if qp.quals.contains(&n) {
                continue;
            }

            match &dag[n] {
                Node::Inp(_, args) | Node::Rel(_, args) => {
                    for arg in args {
                        qp.quals.insert(&arg.reference.node(), &arg.qualifier);
                    }
                    continue;
                }
                Node::Transcr(_, _) => {
                    qp.quals.insert(&n, &Qualifier::Public);
                    continue;
                }
                Node::Op(op, _) => {
                    qp.from_op(&op).and_then(|q| qp.quals.insert(&n, &q));
                }
            }

            // Add parent neighbors to worklist
            for e in dag.0.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                if !qp.quals.contains(&e.source()) {
                    worklist.push(e.source());
                }
            }
        }

        Dag(dag.0.map(
            |i, node|
                node.with_annotation(qp.quals.get(&i).unwrap_or_else(|| &Qualifier::Private).clone()),
            |_, e| e.clone()))
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::{WritePdf, UDags};
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
    let g = QualifierPropagation::from_dag(&gs[0]);

    g.write_pdf("qualifier.pdf").unwrap();
}
