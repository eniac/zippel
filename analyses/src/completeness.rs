use backend::ArkConfig;
use backend::Value;
use backend::op::HasOpFactory;
use share::{Ctx, Set};

use crate::TransClos;
use crate::backend::{GbBackendKind, GbBasis};
use crate::error::AnalysisError;
use crate::extractor::extract_locals;
use crate::frontend::{MonoOrder, Polynomial};
use crate::ideal::IdealBuilder;
use graph::QDag;
use graph::Ref;

/// Perform a completeness analysis using Groebner bases.
/// This analysis checks if the relation is included in the implementation.
/// One shared namespace is used for prover, relation, and verifier.
pub struct CompletenessAnalysis<C: ArkConfig> {
    /// Gröbner basis of (prover ∪ relation ∪ verifier-locals) under grevlex.
    /// Computed in `from_input_with_backend`.
    pub basis: GbBasis<C::F>,
    /// Verifier polynomials to reduce against `basis` in `run()`.
    pub verifier: Vec<Polynomial<C::F>>,
}

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    pub fn from_input(dag: &QDag<C>) -> Self {
        Self::from_input_with_backend(dag, GbBackendKind::default())
    }

    /// Like [`from_input`](Self::from_input) but with a user-selected GB
    /// backend.
    pub fn from_input_with_backend(dag: &QDag<C>, backend: GbBackendKind) -> Self {
        Self::from_input_with_partial(dag, backend, &Ctx::new())
    }

    /// Like [`from_input_with_backend`](Self::from_input_with_backend) but
    /// concretizes args whose `Ref` appears in `partial_values` to constant
    /// polynomials. Use [`QDag::resolve_partial_values`] to build the
    /// `Ref`-keyed map from a name-based `Ctx<Vid, Value<C>>`.
    pub fn from_input_with_partial(
        dag: &QDag<C>,
        backend: GbBackendKind,
        partial_values: &Ctx<Ref, Value<C>>,
    ) -> Self {
        let mut builder = IdealBuilder::new();

        let prover_tc = TransClos::prover(dag);
        let mut prover_result = builder.build_with_partial(prover_tc, partial_values);

        let rel_result = builder.build_with_partial(TransClos::relation(dag), partial_values);
        prover_result.merge(&rel_result);

        let transcript_refs: Set<Ref> = dag.transcript_nodes().into_iter().map(Ref::new).collect();
        prover_result.inline(&transcript_refs);

        let verifier_tc = TransClos::verifier(dag);
        let mut verifier_locals = extract_locals(&builder, &verifier_tc);
        verifier_locals.inline(&Set::new());

        let mut verifier_result = builder.build_with_partial(verifier_tc, partial_values);
        verifier_result.inline(&Set::new());

        // Merge verifier_locals into prover, then compute the GB.
        for p in verifier_locals.generating_set.iter() {
            prover_result.generating_set.push(p.clone());
        }

        let gb = backend.build::<C::F>();
        let basis = gb
            .compute_gb(prover_result.generating_set, &MonoOrder::grevlex())
            .expect("GB backend should support grevlex");

        Self {
            basis,
            verifier: verifier_result.generating_set,
        }
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        if self.basis.is_unit() {
            return Err(AnalysisError::UnitIdeal {
                context: "completeness prover",
            });
        }

        // Use the shared reduce (no backend needed — reduction only needs
        // the basis + its ordering, both stored in self.basis).
        for p in self.verifier.iter() {
            if p.is_zero() {
                continue;
            }
            let remainder = crate::backend::reduce(p.clone(), &self.basis.polys, &self.basis.order);
            if !remainder.is_zero() {
                return Err(AnalysisError::Incomplete(remainder));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::CompletenessAnalysis;
    use crate::QualifierPropagation;
    use crate::Var;
    use crate::backend::GbBackend;
    use crate::error::AnalysisError;
    use crate::frontend::Polynomial;
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use graph::UDags;

    use share::Ctx;
    use share::unwrap;

    #[test]
    fn completeness_test() {
        let ex = r#"
            proto ex_complete<F: Field>(witness s: F, witness s': F) where s == s' {
                let r = random<F*>;
                a <- s * r;
                b <- s' * r;
                verify(a == b)
            }"#;

        log::debug!("Parsing example: {}", ex);
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        let result = ca.run();
        if let Err(ref e) = result {
            eprintln!("completeness_test error: {:?}", e);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn schnorr_completeness() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok(), "Schnorr protocol should be complete");
    }

    #[test]
    fn completeness_relation_namespace() {
        let ex = r#"
            proto eq_proof<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == y)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eq_proof should be complete (relation namespace must match)"
        );
    }

    #[test]
    fn completeness_multiple_verify() {
        let ex = r#"
            proto eq_proof<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == x);
                verify(x == y)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eq_proof with two verify statements should be complete"
        );
    }

    #[test]
    fn completeness_multiple_verify_independent() {
        let ex = r#"
            proto eq_proof<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                let s = random<F>;
                x <- a * r;
                y <- b * r;
                u <- a * s;
                v <- b * s;
                verify(x == y);
                verify(u == v)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eq_proof with two independent verify statements should be complete"
        );
    }

    #[test]
    fn completeness_multiple_verify_negative() {
        let ex = r#"
            proto incomplete<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == y);
                verify(x == 0)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "verify(x == 0) is not implied by a == b, so protocol should be incomplete"
        );
    }

    #[test]
    fn completeness_cross_function_verify() {
        let ex = r#"
            fn with_check<F: Field>(x: F) -> F {
                verify(x == x);
                x
            }
            proto caller<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                z <- with_check(y);
                verify(z == y)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let caller = gs.protocols()[0];
        assert_eq!(
            caller.find_verify().len(),
            2,
            "Full DAG should have 2 terminal checks: inlined verify from function, and protocol's own verify"
        );

        let g = QualifierPropagation::from_dag(caller);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "Both verifies are complete: inlined verify(x==x) is trivial, verify(z==y) follows from a==b"
        );
    }

    #[test]
    fn test_buchberger_completeness_schnorr_like() {
        use backend::ATyp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mk_var = |name: &str, idx: usize| -> Var {
            Var::from_var(
                name.to_string(),
                NodeIndex::new(idx),
                ATyp::scalar(),
                Qualifier::Instance,
            )
        };
        let g_var = mk_var("g", 0);
        let x_var = mk_var("x", 1);
        let h_var = mk_var("h", 2);
        let r_var = mk_var("r", 3);
        let u_var = mk_var("u", 4);

        type Poly = Polynomial<<ArkBls12_381 as backend::ArkConfig>::F>;
        let var_poly = |p: &Var| -> Poly { Polynomial::var(p) };

        let p1 = var_poly(&g_var) * var_poly(&x_var) - var_poly(&h_var);
        let p2 = var_poly(&g_var) * var_poly(&r_var) - var_poly(&u_var);

        use crate::backend::ark_gb::ArkGb;
        use crate::frontend::MonoOrder;

        let backend = ArkGb::with_width(8);
        let gb = backend
            .compute_gb(vec![p1, p2], &MonoOrder::grevlex())
            .expect("ark-gb grevlex should succeed for Schnorr-like input");

        let target = var_poly(&h_var) * var_poly(&r_var) - var_poly(&u_var) * var_poly(&x_var);
        let rem = backend.reduce(target, &gb);
        assert!(
            rem.is_zero(),
            "h*r - u*x should reduce to 0 given g*x = h and g*r = u"
        );
    }

    #[test]
    fn incomplete_wrong_verify() {
        let ex = r#"
            proto incomplete<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(r == 0)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "Protocol with verify(r == 0) should be incomplete when relation is a == b"
        );
    }

    #[test]
    fn incomplete_unused_instance_input() {
        let ex = r#"
            proto incomplete<F: Field>(witness a: F, witness b: F, instance c: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == y); verify(c == 0)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "Protocol with unused instance input c == 0 should be incomplete"
        );
    }

    #[test]
    fn mle_product_relation_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto mle_mul_rel<F: Field, N: Size>(
                instance a: Mle<F, N>,
                instance b: Mle<F, N>
            ) where a == b {
                let p = a * a;
                let q = a * b;
                verify(p == q)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "Mle × Mle equality under relation a==b should be complete"
        );
    }

    #[test]
    fn named_let_scalar_product_completeness() {
        let ex = r#"
            proto named_scalar<F: Field>(witness a: F) where a == a {
                c1 <- challenge<F>;
                c2 <- challenge<F>;
                let rr = c1 * c2;
                x <- c1 * c2;
                verify(x == rr)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let scalar product should be complete"
        );
    }

    #[test]
    fn named_let_single_eval_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto named_eval<F: Field, N: Size>(instance a: Mle<F, N>) where a == a {
                r1 <- challenge<F>;
                r2 <- challenge<F>;
                let l = eval(a, [r1, r2]);
                verify(l == l)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok(), "named-let single-eval should be complete");
    }

    #[test]
    fn named_let_partial_eval_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto named_partial<F: Field, N: Size>(instance a: Mle<F, N>) where a == a {
                r1 <- challenge<F>;
                let q = eval(a, [r1]);
                verify(q == q)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let partial-eval should be complete"
        );
    }

    #[test]
    fn materialized_partial_mle_eval_keeps_inferred_uni_shape() {
        let ex = r#"
            proto materialized_partial<F: Field>(instance vals: [F; 4]) where reduce(&&, vals == vals) {
                x <- challenge<F>;
                let q = eval(mle(vals), [x]);
                let z = q + poly([0, 0]);
                verify(z == z)
            }"#;

        let sizes = Ctx::new();
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "materialized partial MLE eval consumed as Uni(1) should be complete"
        );
    }

    #[test]
    fn trans_clos_partial_mle_eval_boundary_is_mle() {
        let ex = r#"
            proto trans_clos_eval_shape<F: Field>(instance vals: [F; 4]) where reduce(&&, vals == vals) {
                x <- challenge<F>;
                let q = eval(mle(vals), [x]);
                let z = q + poly([0, 0]);
                verify(z == z)
            }"#;

        let sizes = Ctx::new();
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let tc = crate::frontend::TransClos::verifier(&g);

        assert!(
            tc.clos
                .iter()
                .any(|(_var, op)| matches!(op, graph::Op::Evaluate(..))
                    && op.typ() == backend::ATyp::Mle(1)),
            "transitive closure should preserve materialized partial MLE eval as Mle(1)"
        );
        assert!(
            !tc.clos
                .iter()
                .any(|(_var, op)| matches!(op, graph::Op::Evaluate(..))
                    && op.typ() == backend::ATyp::Uni(1)),
            "transitive closure should not recompute the same eval as Uni(1)"
        );
    }

    #[test]
    fn named_let_univariate_eval_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto named_uni<F: Field, N: Size>(instance a: Uni<F, N>) where a == a {
                r1 <- challenge<F>;
                let l = a(r1);
                verify(l == l)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let univariate-eval should be complete"
        );
    }

    #[test]
    fn mle_eval_product_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto mle_eval_product<F: Field, N: Size>(
                instance a: Mle<F, N>,
                instance b: Mle<F, N>
            ) where a == a {
                let p = a * b;
                r1 <- challenge<F>;
                let l = p(r1);
                let rr = a(r1) * b(r1);
                verify(l == rr)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &1);
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eval-based Mle product identity should be complete"
        );
    }

    #[test]
    fn op_eval_typ_dispatch() {
        use backend::{ATyp, ArkBls12_381};
        use graph::{GOp, Op as BOp, Ref, mk};
        use petgraph::graph::NodeIndex;

        let mk_eval = |p_typ: ATyp, x_typ: ATyp| -> GOp<ArkBls12_381> {
            let p: GOp<ArkBls12_381> = BOp::Ref(Ref::new(NodeIndex::new(0)), p_typ);
            let x: GOp<ArkBls12_381> = BOp::Ref(Ref::new(NodeIndex::new(1)), x_typ);
            BOp::Evaluate(mk(p), None, Some(mk(x)))
        };

        let op = mk_eval(ATyp::Uni(3), ATyp::scalar());
        assert_eq!(
            op.typ(),
            ATyp::scalar(),
            "univariate eval at a scalar point should be scalar"
        );

        let op = mk_eval(ATyp::VPoly(1, 3), ATyp::scalar());
        assert_eq!(op.typ(), ATyp::scalar());

        let op = mk_eval(ATyp::VPoly(2, 2), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(
            op.typ(),
            ATyp::scalar(),
            "full multivariate VPoly eval should be scalar"
        );

        let op = mk_eval(ATyp::VPoly(3, 2), ATyp::Vec(Box::new(ATyp::scalar()), 1));
        assert_eq!(
            op.typ(),
            ATyp::VPoly(2, 2),
            "partial multivariate VPoly eval should drop k variables"
        );

        let op = mk_eval(ATyp::Mle(2), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(op.typ(), ATyp::scalar(), "full Mle eval should be scalar");

        let op = mk_eval(ATyp::Mle(3), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(
            op.typ(),
            ATyp::Mle(1),
            "partial Mle eval should drop k variables"
        );
    }

    #[test]
    fn ifft_roundtrip_completeness() {
        let ex = r#"
            proto ifft_roundtrip<F: Field>(instance v: [F; 2]) where reduce(&&, v == v) {
                let p = interpolate(v);
                let u = eval(p);
                verify(reduce(&&, u == v))
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "fft(ifft(v)) == v should be complete via DFT basis equations"
        );
    }

    #[test]
    fn fft_linearity_completeness() {
        let ex = r#"
            proto fft_linearity<F: Field>(
                instance a: Poly<F, 1, 3>,
                instance b: Poly<F, 1, 3>
            ) where a == a {
                let c = a + b;
                let va = eval(a);
                let vb = eval(b);
                let vc = eval(c);
                verify(reduce(&&, vc == va + vb))
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "fft(a + b) == fft(a) + fft(b) should be complete"
        );
    }

    #[test]
    fn ifft_linearity_completeness() {
        let ex = r#"
            proto ifft_linearity<F: Field>(
                instance u: [F; 2],
                instance v: [F; 2]
            ) where reduce(&&, u == u) {
                let w = u + v;
                let pu = interpolate(u);
                let pv = interpolate(v);
                let pw = interpolate(w);
                verify(pw == pu + pv)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "ifft(u + v) == ifft(u) + ifft(v) should be complete"
        );
    }

    #[test]
    fn reduce_add_completeness() {
        let ex = r#"
            proto reduce_add<F: Field>(instance a: F, instance b: F, instance c: F) where a == a {
                let v = [a, b, c];
                let s = reduce(+, v);
                verify(s == a + b + c)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "reduce(+, [a,b,c]) == a+b+c should be complete"
        );
    }

    #[test]
    fn reduce_mul_completeness() {
        let ex = r#"
            proto reduce_mul<F: Field>(instance a: F, instance b: F, instance c: F) where a == a {
                let v = [a, b, c];
                let p = reduce(*, v);
                verify(p == a * b * c)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "reduce(*, [a,b,c]) == a*b*c should be complete"
        );
    }

    #[test]
    fn reduce_sub_completeness() {
        let ex = r#"
            proto reduce_sub<F: Field>(instance a: F, instance b: F, instance c: F) where a == a {
                let v = [a, b, c];
                let s = reduce(-, v);
                verify(s == a - b - c)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "reduce(-, [a,b,c]) == a-b-c should be complete"
        );
    }

    #[test]
    fn literal_scalar_binding_completeness() {
        let ex = r#"
            proto literal_scalar<F: Field>(instance x: F) where x == x {
                let c = 7;
                verify(c == 7)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "literal scalar binding should fold through Gröbner basis"
        );
    }

    #[test]
    fn pair_bilinear_shift_completeness() {
        let ex = r#"
            proto pair_shift<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (instance p: G1, instance q: G2, instance a: F) where a == a {
                let lhs = pair(a * p, q);
                let rhs = pair(p, a * q);
                verify(lhs == rhs)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair(a*P, Q) == pair(P, a*Q) should be complete via bilinearity"
        );
    }

    #[test]
    fn pair_bilinear_additive_completeness() {
        let ex = r#"
            proto pair_additive<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (instance p1: G1, instance p2: G1, instance q: G2) where p1 == p1 {
                let lhs = pair(p1 + p2, q);
                let rhs = pair(p1, q) + pair(p2, q);
                verify(lhs == rhs)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair(P1+P2, Q) == pair(P1,Q) + pair(P2,Q) should be complete"
        );
    }

    #[test]
    fn pair_reflexive_completeness() {
        let ex = r#"
            proto pair_trivial<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (instance p: G1, instance q: G2) where p == p {
                let u = pair(p, q);
                verify(u == u)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair(P, Q) == pair(P, Q) (reflexive) should be complete"
        );
    }

    #[test]
    fn pair_bilinear_product_completeness() {
        let ex = r#"
            proto pair_product<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (instance p: G1, instance q: G2, instance a: F, instance b: F) where a == a {
                let lhs = pair((a * b) * p, q);
                let rhs = pair(a * p, b * q);
                verify(lhs == rhs)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair((a*b)*P, Q) == pair(a*P, b*Q) should be complete via bilinearity"
        );
    }

    #[test]
    fn poly_div_exact_completeness() {
        // Division constraints model defined program traces, so the degree
        // chain requires `d != 0`. The canonical identity and remainder bound
        // then uniquely determine the quotient as `p`.
        let ex = r#"
            proto poly_div_exact<F: Field>(
                instance p: Poly<F, 1, 1>,
                instance d: Poly<F, 1, 1>
            ) where p == p {
                let prod = p * d;
                let q = prod / d;
                verify(q == p)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "(p*d)/d == p should be complete over defined traces where d != 0"
        );
    }

    #[test]
    fn poly_divmod_identity_completeness() {
        let ex = r#"
            proto poly_divmod<F: Field>(
                instance p: Poly<F, 1, 2>,
                instance d: Poly<F, 1, 1>
            ) where p == p {
                let q = p / d;
                let r = p % d;
                verify(p == d * q + r)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "div/rem uniqueness should derive p == d*q + r from their separate identities"
        );
    }

    #[test]
    fn poly_div_degree_chain_forces_zero_remainder() {
        // Divisor has type Uni(2) but actual degree 0 (d[1] = d[2] = 0).
        // The degree chain forces s_2 = 0 (d[2] = 0 → c_2 = 0 → s_2 = 0),
        // which tightens r[1] = 0. Then s_1 = 0 (s_2 OR c_1 = 0 OR 0 = 0),
        // which tightens r[0] = 0. So r = 0 entirely.
        // Without the chain, r[0] and r[1] are unconstrained — you can pick
        // any r and adjust q to compensate.
        let ex = r#"
            proto poly_div_zero_lead<F: Field>(
                instance p: Poly<F, 1, 3>,
                instance d0: F
            ) where p == p {
                let d = poly([d0, 0, 0]);
                let r = p % d;
                verify(r == poly([0, 0]))
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "degree chain should force r = 0 when d[1] = d[2] = 0"
        );
    }

    #[test]
    fn poly_div_degree_chain_no_over_tightening() {
        // Divisor d = poly([b0, 0, b2]) has type Uni(2) with b[1] = 0
        // (known constant) but b[0] and b[2] free. The chain is emitted
        // since b[2] is not a known constant.
        //
        // With the correct cumulative s_d encoding:
        //   s_2 = c_2 (free, since b2 is free)
        //   s_1 = s_2 OR c_1 = s_2 OR 0 = s_2
        //   (1 - s_1) · r[0] = (1 - s_2) · r[0] = 0
        //   → r[0] = 0 only if b2 = 0. Since b2 is free, r[0] is NOT
        //   forced to 0. So verify(r[0] == 0) is INCOMPLETE.
        //
        // With the buggy independent c_d encoding:
        //   c_1 = 0 (b[1] = 0 is known)
        //   (1 - c_1) · r[0] = r[0] = 0 (always, regardless of b2)
        //   → r[0] = 0 is in the ideal. verify(r[0] == 0) is COMPLETE.
        //
        // The test asserts incompleteness, which holds only with the
        // correct cumulative encoding.
        let ex = r#"
            proto poly_div_mid_zero<F: Field>(
                instance p: Poly<F, 1, 3>,
                instance b0: F,
                instance b2: F
            ) where p == p {
                let d = poly([b0, 0, b2]);
                let r = p % d;
                let rc = coef(r);
                verify(rc[0] == b0 - b0)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "r[0] should NOT be forced to 0 when b2 is free (even though \
             b[1] = 0). The cumulative s_d must be used, not independent c_d."
        );
    }

    #[test]
    fn completeness_does_not_skip_verifier_equation_after_vars_refactor() {
        let ex = r#"
            proto challenge_visibility<F: Field>(witness x: F) where x == x {
                c <- challenge<F>;
                y <- x + c;
                verify(y == c)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "verifier equation must be reduced or rejected, not silently skipped"
        );
    }

    #[test]
    fn transcript_inline_completeness() {
        let ex = r#"
            proto simple<F: Field>(instance a: F, instance b: F) where a == a {
                c <- a * b;
                verify(c == a * b)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "c = a*b, verify c == a*b should be complete"
        );
    }

    #[test]
    fn unit_ideal_detection_smoke() {
        let ex = r#"
            proto contradiction<F: Field>(instance x: F) where x == x + 1 {
                t <- x;
                verify(t == t)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = CompletenessAnalysis::from_input(&g);
        let result = ca.run();
        // A self-contradictory relation (x == x+1) drives the prover ideal
        // to the unit ideal (contains -1, a nonzero constant). run() returns
        // Err(UnitIdeal) in this case.
        assert!(
            matches!(
                result,
                Err(AnalysisError::UnitIdeal {
                    context: "completeness prover"
                })
            ),
            "expected UnitIdeal error, got: {result:?}"
        );
        // The basis is the unit ideal (contains 1).
        assert!(ca.basis.is_unit(), "basis should be the unit ideal");
    }
}
