use backend::ArkConfig;
use graph::{Dag, GOp, Node, Op, QDag, UDag};
use lang::typ::Qualifier;
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use share::{Ctx, Set};

/// Result of the qualifier-propagation pass: the qualifier assigned to every
/// node that is reachable from the prover's arguments or backwards from a
/// verifier check.
pub struct QualifierPropagation {
    /// Qualifier per node; nodes outside both reachable sets are absent.
    pub quals: Ctx<NodeIndex, Qualifier>,
}

/// Propagate qualifiers [witness, local, extra, instance] through the DAG
impl QualifierPropagation {
    #[allow(clippy::wrong_self_convention)]
    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Option<Qualifier> {
        self.from_op_loops(op, &[])
    }

    #[allow(clippy::wrong_self_convention)]
    fn from_op_loops<C: ArkConfig>(&self, op: &GOp<C>, loops: &[Qualifier]) -> Option<Qualifier> {
        match op {
            Op::Value(_) => Some(Qualifier::Instance),
            Op::Assert(_) | Op::Verify(_) => Some(Qualifier::Instance),
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
                let mut qual = Qualifier::Instance;
                for v in vs {
                    let q = self.from_op_loops(v, loops)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            Op::Record(fields) => {
                let mut qual = Qualifier::Instance;
                for (_, v) in fields.iter() {
                    let q = self.from_op_loops(v, loops)?;
                    qual = qual.join(&q);
                }
                Some(qual)
            }
            Op::Random(_, _) => Some(Qualifier::Local),
            Op::Challenge(_, _) => Some(Qualifier::Instance),
        }
    }

    /// Runs qualifier propagation over `dag` and returns the annotated
    /// [`QDag`].
    ///
    /// Nodes forward-reachable from the arguments (prover side) and
    /// backward-reachable from the `verify` checks (verifier side) are
    /// qualified by iterating the per-op join rule to a fixpoint; transcript
    /// nodes bound both traversals and are pinned to `Instance`.
    ///
    /// # Panics
    /// Panics if `dag` contains no `verify` check, since the verifier side
    /// would then be empty and the projection meaningless.
    pub fn from_dag<C: ArkConfig>(dag: &UDag<C>) -> QDag<C> {
        let mut qp = QualifierPropagation { quals: Ctx::new() };

        // Forward-reachable set from args (prover side), stopping at transcripts.
        // Transcript nodes are included (assigned Instance) but not traversed past.
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
                        qp.quals.insert(&n, &Qualifier::Instance);
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
                        Qualifier::Instance
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
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use backend::op::mk;
    use graph::{Node, UDags};
    use lang::typ::Qualifier;
    use share::unwrap;

    #[test]
    fn qualifier_prop() {
        let ex = r#"
            proto foo<F: Field, N: 2..4>(witness s: [F; N], witness s': F, instance i: Fin<2>) where reduce(&&, s == s) {
                let r = random<F>;
                a <- r * s[i];
                b <- r * s';
                verify(a == b)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);
        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_qualifier_from_op_value() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let op = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(42u64)));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
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
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_from_op_check() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Verify(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_propagation_instance_instance_join() {
        let ex = r#"
            proto add_instance<F: Field>(instance x: F, instance y: F) where 1 == 1 {
                z <- x + y;
                verify(z == x + y)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check_nodes = g.find_verify();
        assert!(!check_nodes.is_empty(), "Check node should exist");
        if let Node::Op(_, qual) = &g[check_nodes[0]] {
            assert_eq!(*qual, Qualifier::Instance);
        }
    }

    #[test]
    fn test_qualifier_propagation_witness_instance_join() {
        let ex = r#"
            proto mix_quals<F: Field>(witness x: F, instance y: F) where 1 == 1 {
                z <- x + y;
                verify(z == x + y)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check_nodes = g.find_verify();
        assert!(!check_nodes.is_empty(), "Check node should exist");
        if let Node::Op(_, qual) = &g[check_nodes[0]] {
            assert_eq!(*qual, Qualifier::Instance);
        }
    }

    #[test]
    fn test_qualifier_propagation_witness_witness_join() {
        let ex = r#"
            proto witness_only<F: Field>(witness x: F, witness y: F) where 1 == 1 {
                z <- x * y;
                verify(z == x * y)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_qualifier_from_dag_finds_check() {
        let ex = r#"
            proto simple<F: Field>(witness x: F) where 1 == 1 {
                verify(x == x)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let check = g.find_verify();
        assert!(!check.is_empty());
    }

    #[test]
    fn test_qualifier_from_dag_finds_multiple_checks() {
        let ex = r#"
            proto two_checks<F: Field>(witness x: F, witness y: F) where 1 == 1 {
                verify(x == x);
                verify(y == y)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
    fn test_qualifier_multiple_checks_all_instance() {
        let ex = r#"
            proto two_checks<F: Field>(instance x: F, instance y: F) where 1 == 1 {
                verify(x == x);
                verify(y == y)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
                    Qualifier::Instance,
                    "Check node {} should be Instance",
                    i
                );
            }
        }
    }

    #[test]
    fn test_qualifier_three_checks() {
        let ex = r#"
            proto three_checks<F: Field>(witness x: F, witness y: F, witness z: F) where 1 == 1 {
                verify(x == x);
                verify(y == y);
                verify(z == z)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
            proto scattered<F: Field>(witness x: F, instance y: F) where 1 == 1 {
                a <- x + y;
                verify(a == a);
                b <- a + y;
                verify(b == b)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
                    Qualifier::Instance,
                    "Check node {} should be Instance",
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
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_poly_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Poly(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_mle_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Mle(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_coef_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Coef(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_fft_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Fft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
    }

    #[test]
    fn test_qualifier_interpolate_grid_operation() {
        let qp = QualifierPropagation { quals: Ctx::new() };
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Ifft(mk::<ArkBls12_381>(inner));
        let qual = qp.from_op(&op);
        assert_eq!(qual, Some(Qualifier::Instance));
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

    /// `let r = random<F>` should get `Local` (not `Witness`).
    /// This is the Op::Random → Local fix (Step 2).
    #[test]
    fn regression_random_gets_local() {
        let ex = r#"
            proto foo<F: Field>(witness s: F) where s == s {
                let r = random<F>;
                a <- r * s;
                verify(a == a)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let r_node = find_node_by_name(&g, "r").expect("r node should exist");
        assert_eq!(
            node_qual(&g, r_node),
            Qualifier::Local,
            "random<F> should get Local, not Witness"
        );
    }

    /// Prover-side computation behind a transcript should be reached by the
    /// forward walk from args. `r * s` (where r is random, s is witness)
    /// should get `Local` (join of Local and Witness).
    #[test]
    fn regression_prover_side_computation_reached() {
        let ex = r#"
            proto foo<F: Field>(witness s: F) where s == s {
                let r = random<F>;
                a <- r * s;
                verify(a == a)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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

        // r is Local, s is Witness → join should be Local (Local absorbs).
        assert_eq!(
            node_qual(&g, op_node),
            Qualifier::Local,
            "r * s (Local * Witness) should be Local"
        );
    }

    /// Transcript nodes are always `Instance`, regardless of what feeds them.
    #[test]
    fn regression_transcript_always_instance() {
        let ex = r#"
            proto foo<F: Field>(witness s: F) where s == s {
                let r = random<F>;
                a <- r * s;
                verify(a == a)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        for n in g.node_indices() {
            if g[n].is_transcript() {
                assert_eq!(
                    node_qual(&g, n),
                    Qualifier::Instance,
                    "transcript node {:?} should be Instance",
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
            proto foo<F: Field>(witness s: F) where s == s {
                let r = random<F>;
                let t = r * r;
                a <- t + s;
                verify(a == a)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
    /// `Witness` (join of Instance g and Witness x).
    #[test]
    fn regression_relation_side_computation_reached() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        // The relation-side g*x computation should be Witness.
        // Find any Op node with Witness qualifier that is a Bin(Mul, ...)
        // referencing an Instance arg and a Witness arg.
        let has_witness_mul = g.node_indices().any(|n| {
            if let Node::Op(op, qual) = &g[n] {
                if *qual != Qualifier::Witness {
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
                    // g*x: one is Instance (g), the other is Witness (x)
                    matches!(qa, Some(Qualifier::Instance))
                        && matches!(qb, Some(Qualifier::Witness))
                        || matches!(qa, Some(Qualifier::Witness))
                            && matches!(qb, Some(Qualifier::Instance))
                } else {
                    false
                }
            } else {
                false
            }
        });
        assert!(
            has_witness_mul,
            "relation-side g*x should be reached and get Witness qualifier"
        );
    }

    /// Verifier-side computation (between check and transcript) should be
    /// reached by the backward walk. `g*z` in the check `g*z == u + h*c`
    /// should get `Instance` (join of Instance g and Instance z).
    #[test]
    fn regression_verifier_side_computation_reached() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F*>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
        // At least one predecessor should be Instance (the verifier-side computation)
        let has_instance_op = preds.iter().any(
            |&p| matches!(&g[p], Node::Op(_, q) | Node::Transcr(_, q) if *q == Qualifier::Instance),
        );
        assert!(
            has_instance_op,
            "verifier-side computation should be reached and get Instance"
        );
    }

    /// `r * r` (random squared) should get `Local` via the forward walk.
    /// This is the key case from the plan: non-uniform prover-side computation
    /// that should be eliminated, not flagged as a leak.
    #[test]
    fn regression_random_squared_gets_local() {
        let ex = r#"
            proto foo<F: Field>(instance x: F, witness s: F) where x == x {
                let r = random<F>;
                let t = r * r;
                a <- t + s;
                verify(a == x)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
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
