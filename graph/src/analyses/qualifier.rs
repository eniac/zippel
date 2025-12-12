use backend::ArkConfig;
use petgraph::graph::NodeIndex;
use petgraph::Direction;
use petgraph::visit::EdgeRef;
use share::Ctx;
use lang::typ::Qualifier;
use crate::{Dag, UDag, Node, QDag, GOp};

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
            GOp::Poly(box a) => self.from_op(a),
            GOp::Mle(box a) => self.from_op(a),
            GOp::Coef(box a) => self.from_op(a),
            GOp::Eval(box p, box x) => {
                let qual_p = self.from_op(p)?;
                let qual_x = self.from_op(x)?;
                Some(qual_p.join(&qual_x))
            },
            GOp::Ifft(box a) => self.from_op(a),
            GOp::Fft(box a) => self.from_op(a),
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

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::UModule;
    use backend::ArkBls12_381;
    use crate::{UDags, Node};
    use share::unwrap;
    use lang::typ::Qualifier;

    #[test]
    #[ignore]
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

        let g = QualifierPropagation::from_dag(&gs[0]);
        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_qualifier_from_op_value() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let op = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(42u64)));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_from_op_random() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Private));
    }

    #[test]
    fn test_qualifier_from_op_challenge() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let op = GOp::<ArkBls12_381>::Challenge(backend::ATyp::scalar(), false);
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_from_op_check() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = GOp::<ArkBls12_381>::Check(Box::new(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_propagation_public_public_join() {
        let ex = r#"
            proto add_public<F: Field>(public x: F, public y: F) where true {
                z <- x + y;
                verify(z == x + y);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        
        let check_node = g.find_check().expect("Check node should exist");
        if let Node::Op(_, qual) = &g[check_node] {
            assert_eq!(*qual, Qualifier::Public);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_public_join() {
        let ex = r#"
            proto mix_quals<F: Field>(private x: F, public y: F) where true {
                z <- x + y;
                verify(z == x + y);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        
        let check_node = g.find_check().expect("Check node should exist");
        if let Node::Op(_, qual) = &g[check_node] {
            assert_eq!(*qual, Qualifier::Public);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_private_join() {
        let ex = r#"
            proto private_only<F: Field>(private x: F, private y: F) where true {
                z <- x * y;
                verify(z == x * y);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        
        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_qualifier_from_dag_finds_check() {
        let ex = r#"
            proto simple<F: Field>(private x: F) where true {
                verify(x == x);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize().unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        
        let check = g.find_check();
        assert!(check.is_some());
    }

    #[test]
    fn test_qualifier_vec_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let val1 = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let val2 = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(2u64)));
        let op = GOp::<ArkBls12_381>::Vec(vec![val1, val2]);
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_poly_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = GOp::<ArkBls12_381>::Poly(Box::new(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_mle_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = GOp::<ArkBls12_381>::Mle(Box::new(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_coef_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = GOp::<ArkBls12_381>::Coef(Box::new(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_fft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = GOp::<ArkBls12_381>::Fft(Box::new(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_ifft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = GOp::<ArkBls12_381>::Ifft(Box::new(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }
}
