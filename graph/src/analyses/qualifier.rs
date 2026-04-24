use crate::{Dag, GOp, Node, Op, QDag, UDag};
use backend::ArkConfig;
use lang::typ::Qualifier;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use share::Ctx;

pub struct QualifierPropagation {
    pub quals: Ctx<NodeIndex, Qualifier>,
}

/// Propagate qualifiers [private, public] through the DAG
impl QualifierPropagation {
    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Option<Qualifier> {
        match op {
            Op::Value(_) => Some(Qualifier::Public),
            Op::Check(_) => Some(Qualifier::Public),
            Op::Ref(r, _) => self.quals.get(&r.node()).map(|v| v.clone()),
            Op::Ram(a, _) => self.from_op(a),
            Op::Poly(a) => self.from_op(a),
            Op::Mle(a) => self.from_op(a),
            Op::Coef(a) => self.from_op(a),
            Op::Reduce(_, v) => self.from_op(v),
            Op::Eval(p, x) => {
                let qual_p = self.from_op(p)?;
                let qual_x = self.from_op(x)?;
                Some(qual_p.join(&qual_x))
            }
            Op::Ifft(a) => self.from_op(a),
            Op::Fft(a) => self.from_op(a),
            Op::Bin(_, a, b, _) | Op::Pair(a, b, _) => {
                let qual_a = self.from_op(a)?;
                let qual_b = self.from_op(b)?;
                Some(qual_a.join(&qual_b))
            }
            Op::Vec(vs) => {
                let mut qual = Qualifier::Public;
                for v in vs {
                    let q = self.from_op(v)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            Op::Record(fields) => {
                let mut qual = Qualifier::Public;
                for (_, v) in fields.iter() {
                    let q = self.from_op(v)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            Op::Random(_, _) => Some(Qualifier::Private),
            Op::Challenge(_, _) => Some(Qualifier::Public),
        }
    }

    pub fn from_dag<C: ArkConfig>(dag: &UDag<C>) -> QDag<C> {
        let mut qp = QualifierPropagation { quals: Ctx::new() };
        let mut worklist = dag.find_check();
        assert!(!worklist.is_empty(), "No check found in the DAG");

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
            for e in dag.graph.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                if !qp.quals.contains(&e.source()) {
                    worklist.push(e.source());
                }
            }
        }

        Dag {
            graph: dag.graph.map(
                |i, node| {
                    node.with_annotation(if node.is_transcript() {
                        // Transcript nodes are always Public (verifier-observable)
                        Qualifier::Public
                    } else {
                        qp.quals
                            .get(&i)
                            .unwrap_or_else(|| &Qualifier::Local)
                            .clone()
                    })
                },
                |_, e| e.clone(),
            ),
            vctx: dag.vctx.clone(),
            transcript_vars: dag.transcript_vars.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Node, UDags};
    use backend::ArkBls12_381;
    use backend::op::mk;
    use lang::ast::UModule;
    use lang::typ::Qualifier;
    use share::unwrap;

    #[test]
    #[ignore]
    fn qualifier_prop() {
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
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Check(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_propagation_public_public_join() {
        let ex = r#"
            proto add_public<F: Field>(public x: F, public y: F) where true {
                z <- x + y;
                verify(z == x + y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check_nodes = g.find_check();
        assert!(!check_nodes.is_empty(), "Check node should exist");
        if let Node::Op(_, qual) = &g[check_nodes[0]] {
            assert_eq!(*qual, Qualifier::Public);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_public_join() {
        let ex = r#"
            proto mix_quals<F: Field>(private x: F, public y: F) where true {
                z <- x + y;
                verify(z == x + y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check_nodes = g.find_check();
        assert!(!check_nodes.is_empty(), "Check node should exist");
        if let Node::Op(_, qual) = &g[check_nodes[0]] {
            assert_eq!(*qual, Qualifier::Public);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_private_join() {
        let ex = r#"
            proto private_only<F: Field>(private x: F, private y: F) where true {
                z <- x * y;
                verify(z == x * y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_qualifier_from_dag_finds_check() {
        let ex = r#"
            proto simple<F: Field>(private x: F) where true {
                verify(x == x)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check = g.find_check();
        assert!(!check.is_empty());
    }

    #[test]
    fn test_qualifier_from_dag_finds_multiple_checks() {
        let ex = r#"
            proto two_checks<F: Field>(private x: F, private y: F) where true {
                verify(x == x);
                verify(y == y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let checks = g.find_check();
        assert_eq!(
            checks.len(),
            2,
            "Protocol with two verify statements should have two check nodes"
        );
    }

    #[test]
    fn test_qualifier_multiple_checks_all_public() {
        let ex = r#"
            proto two_checks<F: Field>(public x: F, public y: F) where true {
                verify(x == x);
                verify(y == y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let checks = g.find_check();
        assert_eq!(
            checks.len(),
            2,
            "Protocol with two verify statements should have two check nodes"
        );
        for (i, &check_node) in checks.iter().enumerate() {
            if let Node::Op(_, qual) = &g[check_node] {
                assert_eq!(
                    *qual,
                    Qualifier::Public,
                    "Check node {} should be Public",
                    i
                );
            }
        }
    }

    #[test]
    fn test_qualifier_three_checks() {
        let ex = r#"
            proto three_checks<F: Field>(private x: F, private y: F, private z: F) where true {
                verify(x == x);
                verify(y == y);
                verify(z == z)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let checks = g.find_check();
        assert_eq!(
            checks.len(),
            3,
            "Protocol with three verify statements should have three check nodes"
        );
    }

    #[test]
    fn test_qualifier_scattered_checks() {
        let ex = r#"
            proto scattered<F: Field>(private x: F, public y: F) where true {
                a <- x + y;
                verify(a == a);
                b <- a + y;
                verify(b == b)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let checks = g.find_check();
        assert_eq!(
            checks.len(),
            2,
            "Scattered verify statements should produce 2 check nodes"
        );
        for (i, &check_node) in checks.iter().enumerate() {
            if let Node::Op(_, qual) = &g[check_node] {
                assert_eq!(
                    *qual,
                    Qualifier::Public,
                    "Check node {} should be Public",
                    i
                );
            }
        }
    }

    #[test]
    fn test_qualifier_vec_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let val1 =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let val2 =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(2u64)));
        let op = Op::Vec(vec![mk::<ArkBls12_381>(val1), mk::<ArkBls12_381>(val2)]);
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_poly_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Poly(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_mle_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Mle(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_coef_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Coef(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_fft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Fft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_ifft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Ifft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }
}
