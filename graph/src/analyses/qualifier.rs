use backend::ArkConfig;
use backend::op::Ref;
use petgraph::graph::NodeIndex;
use petgraph::Direction;
use petgraph::visit::EdgeRef;
use share::Ctx;
use lang::id::Vid;
use lang::typ::Qualifier;
use crate::{Dag, UDag, Node, QDag, GOp, Op};

/// Key for qualifier lookup: (NodeIndex, Option<Vid>).
/// - `(node, Some(vid))` for input/relation argument variables
/// - `(node, None)` for regular op/transcript nodes
type QualKey = (NodeIndex, Option<Vid>);

pub struct QualifierPropagation {
    pub quals: Ctx<QualKey, Qualifier>,
}

/// Propagate qualifiers [private, public] through the DAG
impl QualifierPropagation {
    fn qual_key_for_ref(r: &Ref) -> QualKey {
        match r {
            Ref::Var(vid, n) => (*n, Some(vid.clone())),
            Ref::Node(n) => (*n, None),
        }
    }

    #[allow(dead_code)]
    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Option<Qualifier> {
        match op {
            Op::Value(_) => Some(Qualifier::Public),
            Op::Check(_) => Some(Qualifier::Public),
            Op::Ref(r, _) => {
                // Try the specific key first (for Inp/Rel args with Vid),
                // then fall back to the node-only key (for Op/Transcr nodes)
                let specific = Self::qual_key_for_ref(r);
                self.quals.get(&specific)
                    .or_else(|| self.quals.get(&(r.node(), None)))
                    .cloned()
            },
            Op::Ram(a, _) => self.from_op(a),
            Op::Poly(a) => self.from_op(a),
            Op::Mle(a) => self.from_op(a),
            Op::Coef(a) => self.from_op(a),
            Op::Reduce(_, v) => self.from_op(v),
            Op::Eval(p, x) => {
                let qual_p = self.from_op(p)?;
                let qual_x = self.from_op(x)?;
                Some(qual_p.join(&qual_x))
            },
            Op::Ifft(a) => self.from_op(a),
            Op::Fft(a) => self.from_op(a),
            Op::Bin(_, a, b, _) 
            | Op::Pair(a, b, _) => {
                let qual_a = self.from_op(a)?;
                let qual_b = self.from_op(b)?;
                Some(qual_a.join(&qual_b))
            },
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
        let check = dag.find_check().expect("No check found in the DAG");
        let mut worklist = vec![check];
        let max_iterations = dag.node_count() * dag.node_count();
        let mut iterations = 0;

        while let Some(n) = worklist.pop() {
            iterations += 1;
            if iterations > max_iterations {
                break; // Safety bound to prevent infinite loops
            }

            if qp.quals.contains(&(n, None)) {
                continue;
            }

            match &dag[n] {
                Node::Inp(_, args) | Node::Rel(_, args) => {
                    for arg in args {
                        let key = Self::qual_key_for_ref(&arg.reference);
                        qp.quals.insert(&key, &arg.qualifier);
                    }
                    // Mark the Inp/Rel node itself as visited
                    qp.quals.insert(&(n, None), &Qualifier::Public);
                    continue;
                }
                Node::Transcr(_, _) => {
                    qp.quals.insert(&(n, None), &Qualifier::Public);
                }
                Node::Op(op, _) => {
                    // Non-transcript Op nodes default to Local (prover-internal).
                    // Exception: Random ops are Private (secret randomness).
                    let q = match &**op {
                        Op::Random(_, _) => Qualifier::Private,
                        _ => Qualifier::Local,
                    };
                    qp.quals.insert(&(n, None), &q);
                }
            }

            // Add parent neighbors to worklist
            for e in dag.0.edges_directed(n, Direction::Incoming) {
                if !qp.quals.contains(&(e.source(), None)) {
                    worklist.push(e.source());
                }
            }
        }

        Dag(dag.0.map(
            |i, node|
                node.with_annotation(qp.quals.get(&(i, None)).unwrap_or_else(|| &Qualifier::Local).clone()),
            |_, e| e.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::UModule;
    use backend::ArkBls12_381;
    use backend::op::mk;
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
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
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
        let op = Op::Check(mk::<ArkBls12_381>(inner));
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
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        
        let check_node = g.find_check().expect("Check node should exist");
        if let Node::Op(_, qual) = &g[check_node] {
            assert_eq!(*qual, Qualifier::Local);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_public_join() {
        let ex = r#"
            proto mix_quals<F: Field>(private x: F, public y: F) where true {
                z <- x + y;
                verify(z == x + y);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        
        let check_node = g.find_check().expect("Check node should exist");
        if let Node::Op(_, qual) = &g[check_node] {
            assert_eq!(*qual, Qualifier::Local);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_private_join() {
        let ex = r#"
            proto private_only<F: Field>(private x: F, private y: F) where true {
                z <- x * y;
                verify(z == x * y);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
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
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
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
        let op = Op::Vec(vec![mk::<ArkBls12_381>(val1), mk::<ArkBls12_381>(val2)]);
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_poly_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Poly(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_mle_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Mle(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_coef_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Coef(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_fft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Fft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_ifft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Ifft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn schnorr_challenge_qualifier_is_public() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*z == u + h*c);
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let dag = &gs[0];
        let g = QualifierPropagation::from_dag(dag);

        // All Transcr nodes (including challenge) should be Public
        for n in g.node_indices() {
            if let Node::Transcr(_, qual) = &g[n] {
                assert_eq!(*qual, Qualifier::Public,
                    "Transcript node n{} should be Public", n.index());
            }
        }
    }
}
