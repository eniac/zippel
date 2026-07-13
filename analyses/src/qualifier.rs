use backend::ArkConfig;
use graph::{Dag, GOp, Node, Op, QDag, UDag};
use lang::typ::Qualifier;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use share::{Ctx, Set};

pub struct QualifierPropagation {
    pub quals: Ctx<NodeIndex, Qualifier>,
}

/// Propagate qualifiers [private, public] through the DAG
impl QualifierPropagation {
    #[allow(clippy::wrong_self_convention)]
    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Option<Qualifier> {
        self.from_op_loops(op, &[])
    }

    #[allow(clippy::wrong_self_convention)]
    fn from_op_loops<C: ArkConfig>(&self, op: &GOp<C>, loops: &[Qualifier]) -> Option<Qualifier> {
        match op {
            Op::Value(_) => Some(Qualifier::Public),
            Op::Assert(_, _) | Op::Verify(_, _) => Some(Qualifier::Public),
            Op::Ref(r, _) => self.quals.get(&r.node()).cloned(),
            Op::Ram(a, _) => self.from_op_loops(a, loops),
            Op::Poly(a) => self.from_op_loops(a, loops),
            Op::Mle(a) => self.from_op_loops(a, loops),
            Op::Coef(a) => self.from_op_loops(a, loops),
            Op::Reduce(_, v) => self.from_op_loops(v, loops),
            Op::LoopParam(i, _) => loops.get(*i).cloned(),
            Op::Map(d, b) => {
                let qd = self.from_op_loops(d, loops)?;
                let mut next = loops.to_vec();
                next.push(qd);
                self.from_op_loops(b, &next)
            }
            Op::ReduceMap(_, d, b) => {
                let qd = self.from_op_loops(d, loops)?;
                let mut next = loops.to_vec();
                next.push(qd);
                self.from_op_loops(b, &next)
            }
            Op::Evaluate(p, _, None) => self.from_op_loops(p, loops),
            Op::Evaluate(p, _, Some(x)) => {
                let qual_p = self.from_op_loops(p, loops)?;
                let qual_x = self.from_op_loops(x, loops)?;
                Some(qual_p.join(&qual_x))
            }
            Op::Interpolate(points, evals) => {
                let q_points = self.from_op_loops(points, loops)?;
                let q_evals = self.from_op_loops(evals, loops)?;
                Some(q_points.join(&q_evals))
            }
            Op::Ifft(a) => self.from_op_loops(a, loops),
            Op::Fft(a) => self.from_op_loops(a, loops),
            Op::Proj(a, _, _) => self.from_op_loops(a, loops),
            Op::Bin(_, a, b, _) | Op::Pair(a, b, _) => {
                let qual_a = self.from_op_loops(a, loops)?;
                let qual_b = self.from_op_loops(b, loops)?;
                Some(qual_a.join(&qual_b))
            }
            Op::Vec(vs) => {
                let mut qual = Qualifier::Public;
                for v in vs {
                    let q = self.from_op_loops(v, loops)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            Op::Record(fields) => {
                let mut qual = Qualifier::Public;
                for (_, v) in fields.iter() {
                    let q = self.from_op_loops(v, loops)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            Op::Random(_, _) => Some(Qualifier::Local),
            Op::Challenge(_, _) => Some(Qualifier::Public),
        }
    }

    pub fn from_dag<C: ArkConfig>(dag: &UDag<C>) -> QDag<C> {
        let mut qp = QualifierPropagation { quals: Ctx::new() };

        // Forward-reachable set from args (prover side), stopping at transcripts.
        // Transcript nodes are included (assigned Public) but not traversed past.
        let forward_set: Set<NodeIndex> = {
            let mut set = Set::new();
            let mut worklist: Vec<NodeIndex> = dag
                .input_args()
                .into_iter()
                .chain(dag.relation_args())
                .collect();
            while let Some(n) = worklist.pop() {
                if set.contains(&n) {
                    continue;
                }
                set.insert(n);
                if dag[n].is_transcript() {
                    continue;
                }
                for succ in dag.graph.neighbors_directed(n, Direction::Outgoing) {
                    worklist.push(succ);
                }
            }
            set
        };

        // Backward-reachable set from verify checks (verifier side), stopping at transcripts.
        let checks = dag.find_verify();
        assert!(!checks.is_empty(), "No verify check found in the DAG");
        let backward_set: Set<NodeIndex> = {
            let mut set = Set::new();
            let mut worklist = checks;
            while let Some(n) = worklist.pop() {
                if set.contains(&n) {
                    continue;
                }
                set.insert(n);
                if dag[n].is_transcript() {
                    continue;
                }
                for pred in dag.graph.neighbors_directed(n, Direction::Incoming) {
                    worklist.push(pred);
                }
            }
            set
        };

        // Fixpoint iteration: qualify nodes in both sets until no progress.
        // from_op looks up Op::Ref children in qp.quals, so a node can only be
        // qualified once all its dependencies (graph predecessors) are qualified.
        // Iterating in NodeIndex order (BTreeSet order) is not topological, so we
        // repeat until fixpoint.
        let mut changed = true;
        while changed {
            changed = false;
            for &n in forward_set.iter().chain(backward_set.iter()) {
                if qp.quals.contains(&n) {
                    continue;
                }
                match &dag[n] {
                    Node::Inp(_) | Node::Rel(_) => continue,
                    Node::Arg(_, _, qual, _, _) => {
                        qp.quals.insert(&n, qual);
                        changed = true;
                    }
                    Node::Transcr(_, _) => {
                        qp.quals.insert(&n, &Qualifier::Public);
                        changed = true;
                    }
                    Node::Op(op, _) => {
                        if let Some(q) = qp.from_op(op) {
                            qp.quals.insert(&n, &q);
                            changed = true;
                        }
                    }
                }
            }
        }

        Dag {
            graph: dag.graph.map(
                |i, node| {
                    node.with_annotation(if node.is_transcript() {
                        Qualifier::Public
                    } else {
                        *qp.quals.get(&i).unwrap_or(&Qualifier::Local)
                    })
                },
                |_, e| *e,
            ),
            vctx: dag.vctx.clone(),
            transcript_vars: dag.transcript_vars.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBls12_381;
    use backend::op::mk;
    use graph::{Node, UDags};
    use lang::ast::UModule;
    use lang::typ::Qualifier;
    use share::unwrap;

    #[test]
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
        assert_eq!(qual, Some(Qualifier::Local));
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
        let op = Op::Verify(mk::<ArkBls12_381>(inner.clone()), mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    #[test]
    fn test_qualifier_propagation_public_public_join() {
        let ex = r#"
            proto add_public<F: Field>(public x: F, public y: F) where 1 == 1 {
                z <- x + y;
                verify(z == x + y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check_nodes = g.find_verify();
        assert!(!check_nodes.is_empty(), "Check node should exist");
        if let Node::Op(_, qual) = &g[check_nodes[0]] {
            assert_eq!(*qual, Qualifier::Public);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_public_join() {
        let ex = r#"
            proto mix_quals<F: Field>(private x: F, public y: F) where 1 == 1 {
                z <- x + y;
                verify(z == x + y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check_nodes = g.find_verify();
        assert!(!check_nodes.is_empty(), "Check node should exist");
        if let Node::Op(_, qual) = &g[check_nodes[0]] {
            assert_eq!(*qual, Qualifier::Public);
        }
    }

    #[test]
    fn test_qualifier_propagation_private_private_join() {
        let ex = r#"
            proto private_only<F: Field>(private x: F, private y: F) where 1 == 1 {
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
            proto simple<F: Field>(private x: F) where 1 == 1 {
                verify(x == x)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check = g.find_verify();
        assert!(!check.is_empty());
    }

    #[test]
    fn test_qualifier_from_dag_finds_multiple_checks() {
        let ex = r#"
            proto two_checks<F: Field>(private x: F, private y: F) where 1 == 1 {
                verify(x == x);
                verify(y == y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let checks = g.find_verify();
        assert_eq!(
            checks.len(),
            2,
            "Protocol with two verify statements should have two check nodes"
        );
    }

    #[test]
    fn test_qualifier_multiple_checks_all_public() {
        let ex = r#"
            proto two_checks<F: Field>(public x: F, public y: F) where 1 == 1 {
                verify(x == x);
                verify(y == y)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let checks = g.find_verify();
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
            proto three_checks<F: Field>(private x: F, private y: F, private z: F) where 1 == 1 {
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

        let checks = g.find_verify();
        assert_eq!(
            checks.len(),
            3,
            "Protocol with three verify statements should have three check nodes"
        );
    }

    #[test]
    fn test_qualifier_scattered_checks() {
        let ex = r#"
            proto scattered<F: Field>(private x: F, public y: F) where 1 == 1 {
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

        let checks = g.find_verify();
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
    fn test_qualifier_interpolate_grid_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Ifft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Public));
    }

    // ----------------------------------------------------------------
    // Regression tests for bidirectional qualifier propagation
    // ----------------------------------------------------------------

    /// Helper: find a node by variable name in a QDag.
    fn find_node_by_name(g: &QDag<ArkBls12_381>, name: &str) -> Option<NodeIndex> {
        g.node_indices()
            .find(|&n| g.find_var(n).map(|v| v.0 == name).unwrap_or(false))
    }

    /// Helper: get the qualifier annotation of a node.
    fn node_qual(g: &QDag<ArkBls12_381>, n: NodeIndex) -> Qualifier {
        match &g[n] {
            Node::Op(_, q) | Node::Transcr(_, q) => *q,
            Node::Arg(_, _, q, _, _) => *q,
            _ => panic!("node {:?} has no qualifier", n),
        }
    }

    /// `let r = random<F>` should get `Local` (not `Private`).
    /// This is the Op::Random → Local fix (Step 2).
    #[test]
    fn regression_random_gets_local() {
        let ex = r#"
            proto foo<F: Field>(private s: F) where s == s {
                let r = random<F>;
                a <- r * s;
                verify(a == a)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let r_node = find_node_by_name(&g, "r").expect("r node should exist");
        assert_eq!(
            node_qual(&g, r_node),
            Qualifier::Local,
            "random<F> should get Local, not Private"
        );
    }

    /// Prover-side computation behind a transcript should be reached by the
    /// forward walk from args. `r * s` (where r is random, s is private)
    /// should get `Local` (join of Local and Private).
    #[test]
    fn regression_prover_side_computation_reached() {
        let ex = r#"
            proto foo<F: Field>(private s: F) where s == s {
                let r = random<F>;
                a <- r * s;
                verify(a == a)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        // Find the `a` transcript node, then walk back to the `r * s` op node.
        let a_node = find_node_by_name(&g, "a").expect("a transcript node should exist");
        // The op node feeding `a` is the predecessor (r * s computation).
        let preds: Vec<_> = g
            .graph
            .neighbors_directed(a_node, Direction::Incoming)
            .collect();
        let op_node = preds
            .iter()
            .find(|&&p| matches!(g[p], Node::Op(_, _)))
            .copied()
            .expect("should have an Op predecessor for transcript a");

        // r is Local, s is Private → join should be Local (Local absorbs).
        assert_eq!(
            node_qual(&g, op_node),
            Qualifier::Local,
            "r * s (Local * Private) should be Local"
        );
    }

    /// Transcript nodes are always `Public`, regardless of what feeds them.
    #[test]
    fn regression_transcript_always_public() {
        let ex = r#"
            proto foo<F: Field>(private s: F) where s == s {
                let r = random<F>;
                a <- r * s;
                verify(a == a)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        for n in g.node_indices() {
            if g[n].is_transcript() {
                assert_eq!(
                    node_qual(&g, n),
                    Qualifier::Public,
                    "transcript node {:?} should be Public",
                    n
                );
            }
        }
    }

    /// `let`-bound variables should have their names registered in `vctx`
    /// so `find_var()` returns the correct name instead of `__zippel::node::N`.
    #[test]
    fn regression_let_binding_name_registered() {
        let ex = r#"
            proto foo<F: Field>(private s: F) where s == s {
                let r = random<F>;
                let t = r * r;
                a <- t + s;
                verify(a == a)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let r_node = find_node_by_name(&g, "r");
        assert!(
            r_node.is_some(),
            "let-bound `r` should be findable by name, not __zippel::node::N"
        );

        let t_node = find_node_by_name(&g, "t");
        assert!(
            t_node.is_some(),
            "let-bound `t` should be findable by name, not __zippel::node::N"
        );
    }

    /// Relation-side computation nodes should be reached by the forward walk
    /// from relation args. In Schnorr, `g*x` in the relation should get
    /// `Private` (join of Public g and Private x).
    #[test]
    fn regression_relation_side_computation_reached() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        // The relation-side g*x computation should be Private.
        // Find any Op node with Private qualifier that is a Bin(Mul, ...)
        // referencing a Public arg and a Private arg.
        let has_private_mul = g.node_indices().any(|n| {
            if let Node::Op(op, qual) = &g[n] {
                if *qual != Qualifier::Private {
                    return false;
                }
                if let Op::Bin(_, a, b, _) = &**op {
                    // Get qualifiers of operands by looking up their target nodes
                    let qual_of = |op: &GOp<ArkBls12_381>| -> Option<Qualifier> {
                        match op {
                            Op::Ref(r, _) => Some(node_qual(&g, r.node())),
                            _ => None,
                        }
                    };
                    let qa = qual_of(a);
                    let qb = qual_of(b);
                    // g*x: one is Public (g), the other is Private (x)
                    matches!(qa, Some(Qualifier::Public)) && matches!(qb, Some(Qualifier::Private))
                        || matches!(qa, Some(Qualifier::Private))
                            && matches!(qb, Some(Qualifier::Public))
                } else {
                    false
                }
            } else {
                false
            }
        });
        assert!(
            has_private_mul,
            "relation-side g*x should be reached and get Private qualifier"
        );
    }

    /// Verifier-side computation (between check and transcript) should be
    /// reached by the backward walk. `g*z` in the check `g*z == u + h*c`
    /// should get `Public` (join of Public g and Public z).
    #[test]
    fn regression_verifier_side_computation_reached() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        // Find the check node, then walk to its predecessors to find g*z.
        let checks = g.find_verify();
        assert!(!checks.is_empty());
        let check = checks[0];
        // The check wraps an equality; its predecessors include g*z and u+h*c.
        let preds: Vec<_> = g
            .graph
            .neighbors_directed(check, Direction::Incoming)
            .collect();
        // At least one predecessor should be Public (the verifier-side computation)
        let has_public_op = preds.iter().any(
            |&p| matches!(&g[p], Node::Op(_, q) | Node::Transcr(_, q) if *q == Qualifier::Public),
        );
        assert!(
            has_public_op,
            "verifier-side computation should be reached and get Public"
        );
    }

    /// `r * r` (random squared) should get `Local` via the forward walk.
    /// This is the key case from the plan: non-uniform prover-side computation
    /// that should be eliminated, not flagged as a leak.
    #[test]
    fn regression_random_squared_gets_local() {
        let ex = r#"
            proto foo<F: Field>(public x: F, private s: F) where x == x {
                let r = random<F>;
                let t = r * r;
                a <- t + s;
                verify(a == x)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        // `t` is let-bound to `r * r`. Find the op node for `r * r`.
        let t_node = find_node_by_name(&g, "t").expect("t should be findable by name");
        // t_node is the node for the let binding; the op feeding it is r * r.
        // Actually, `let t = r * r` creates a node for `r * r` and registers
        // the name `t` on it. So t_node IS the r*r op node.
        assert_eq!(
            node_qual(&g, t_node),
            Qualifier::Local,
            "r * r (Local * Local) should be Local"
        );
    }
}
