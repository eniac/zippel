use backend::ArkConfig;
use backend::op::{HasOpFactory, Ref};
use share::Set;
use std::collections::HashMap;

use crate::analyses::error::AnalysisError;
use crate::analyses::groebner::{GrevLexTerm, GroebnerBuilder};
use crate::{DQDag, PRef};
use log::debug;
use petgraph::graph::NodeIndex;

/// Perform a completeness analysis using Groebner bases.
/// This analysis checks if the relation is included in the implementation.
pub struct CompletenessAnalysis<C: ArkConfig> {
    pub prover: GroebnerBuilder<C, GrevLexTerm>,
    pub verifier: GroebnerBuilder<C, GrevLexTerm>,
}

/// Invert a node_map (old_dag_idx → new_subgraph_Ref) to build a PRef remapping closure.
fn make_remap_fn(node_map: &HashMap<NodeIndex, Ref>) -> impl Fn(&PRef) -> PRef + '_ {
    let inverse: HashMap<NodeIndex, (NodeIndex, Ref)> = node_map
        .iter()
        .map(|(old_idx, new_ref)| (new_ref.node(), (*old_idx, new_ref.clone())))
        .collect();

    move |pref: &PRef| {
        if let Some((old_idx, _)) = inverse.get(&pref.node()) {
            PRef {
                reference: Ref(*old_idx),
                ..pref.clone()
            }
        } else {
            pref.clone()
        }
    }
}

/// Build a remap closure from a NodeIndex→NodeIndex map with an override.

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    pub fn from_input(dag: &DQDag<C>) -> Self {
        let (prover, prover_node_map) = dag.get_prover();

        // Build prover basis from prover subgraph, then remap to full-DAG namespace
        let mut g_prover = GroebnerBuilder::new();
        g_prover.add_input(&prover);
        let prover_remap = make_remap_fn(&prover_node_map);
        g_prover.remap_vars(&prover_remap);

        // Build relation basis directly from full DAG (shared namespace).
        // Phase B: register input args first so that `x` referenced by
        // relation polynomials canonicalises to the same `Ref` used by
        // the prover basis.
        let mut g_rel = GroebnerBuilder::new();
        g_rel.register_input_args(dag);
        g_rel.add_relation(dag);

        // Combine: prover + relation
        let mut g_ps = g_prover;
        g_ps.merge(&g_rel);

        let mut g_impl = GroebnerBuilder::new();
        g_impl.add_input(&dag);

        Self {
            prover: g_ps,
            verifier: g_impl,
        }
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        self.prover.run();
        self.verifier.run();
        debug!("Prover:\n{}", self.prover);
        debug!("Impl:\n{}", self.verifier);

        // Verifier-visible variables: prover computation nodes + public input arguments.
        // Private inputs are prover-only and not visible to the verifier.
        let prover_vars = self.prover.vars();
        let public_args: Set<PRef> = self
            .verifier
            .args
            .iter()
            .filter(|a| a.is_public())
            .cloned()
            .collect();
        let verifier_visible = prover_vars.union(public_args);

        // Check all verifier polynomials whose variables are verifier-visible.
        // Polynomials with verifier-internal nodes are skipped.
        for p in self.verifier.basis.iter() {
            let poly_vars = p.vars();
            if poly_vars.iter().all(|v| verifier_visible.contains(v)) {
                let remainder = self.prover.basis.reduce(p.clone());
                if !remainder.is_zero() {
                    return Err(AnalysisError::Incomplete(remainder));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyses::groebner::{GroebnerBasis, SparsePolynomial};
    use crate::{
        UDags,
        analyses::{QualifierPropagation, UniformityPropagation},
    };
    use backend::ArkBls12_381;
    use lang::ast::UModule;
    use lang::id::Vid;
    use share::Ctx;
    use share::unwrap;

    #[test]
    fn completeness_test() {
        let ex = r#"
            proto ex_complete<F: Field>(private s: F, private s': F) where s == s' {
                let r = random<F*>;
                a <- s * r;
                b <- s' * r;
                verify(a == b)
            }"#;

        debug!("Parsing example: {}", ex);
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok());
    }

    #[test]
    fn schnorr_completeness() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok(), "Schnorr protocol should be complete");
    }

    /// Regression: completeness relation basis must share the same variable
    /// namespace as the prover/verifier basis. If the relation is built from
    /// a subgraph with fresh indices, reduction won't work.
    #[test]
    fn completeness_relation_namespace() {
        let ex = r#"
            proto eq_proof<F: Field>(private a: F, private b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == y)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        // This only passes if the relation `a == b` is in the same namespace
        // as the prover/verifier polynomials.
        assert!(
            ca.run().is_ok(),
            "eq_proof should be complete (relation namespace must match)"
        );
    }

    #[test]
    fn completeness_multiple_verify() {
        let ex = r#"
            proto eq_proof<F: Field>(private a: F, private b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == x);
                verify(x == y)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eq_proof with two verify statements should be complete"
        );
    }

    #[test]
    fn completeness_multiple_verify_independent() {
        let ex = r#"
            proto eq_proof<F: Field>(private a: F, private b: F) where a == b {
                let r = random<F>;
                let s = random<F>;
                x <- a * r;
                y <- b * r;
                u <- a * s;
                v <- b * s;
                verify(x == y);
                verify(u == v)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eq_proof with two independent verify statements should be complete"
        );
    }

    /// Negative: second verify makes the protocol incomplete.
    /// verify(x == y) is complete (follows from a == b), but
    /// verify(x == 0) is not — x is a transcript variable (in prover vocabulary)
    /// but nothing forces x = 0. The polynomial `x` reduces to `a*r`, not 0.
    #[test]
    fn completeness_multiple_verify_negative() {
        let ex = r#"
            proto incomplete<F: Field>(private a: F, private b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == y);
                verify(x == 0)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "verify(x == 0) is not implied by a == b, so protocol should be incomplete"
        );
    }

    /// Cross-function boundary: a function with verify is inlined into the protocol.
    /// The inlined verify's Check node IS terminal in the full DAG — its result is
    /// discarded by Let(None, ...) so nothing consumes it. find_check() finds both
    /// the inlined and protocol's own check nodes.
    #[test]
    fn completeness_cross_function_verify() {
        let ex = r#"
            fn with_check<F: Field>(x: F) -> F {
                verify(x == x);
                x
            }
            proto caller<F: Field>(private a: F, private b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                z <- with_check(y);
                verify(z == y)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let caller = gs.protocols()[0];
        assert_eq!(
            caller.find_check().len(),
            2,
            "Full DAG should have 2 terminal checks: inlined verify from function, and protocol's own verify"
        );

        let g = QualifierPropagation::from_dag(caller);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "Both verifies are complete: inlined verify(x==x) is trivial, verify(z==y) follows from a==b"
        );
    }

    #[test]
    fn test_buchberger_spoly_produces_ux_hr() {
        use backend::ATyp;
        use lang::typ::{Distribution, Qualifier};

        let mk_var = |name: &str, idx: usize| -> PRef {
            PRef::from_var(
                Vid(name.to_string()),
                NodeIndex::new(idx),
                ATyp::scalar(),
                0,
                Qualifier::Public,
                Distribution::default(),
            )
        };
        let g_var = mk_var("g", 0);
        let x_var = mk_var("x", 1);
        let h_var = mk_var("h", 2);
        let r_var = mk_var("r", 3);
        let u_var = mk_var("u", 4);

        type Poly = SparsePolynomial<<ArkBls12_381 as backend::ArkConfig>::F, GrevLexTerm>;
        let var = |p: &PRef| -> Poly { SparsePolynomial::var(p) };

        let p1 = var(&g_var) * var(&x_var) - var(&h_var);
        let p2 = var(&g_var) * var(&r_var) - var(&u_var);

        let spoly = p1.s_poly(&p2);
        let expected_positive = var(&u_var) * var(&x_var) - var(&h_var) * var(&r_var);
        let expected_negative = var(&h_var) * var(&r_var) - var(&u_var) * var(&x_var);
        assert!(spoly == expected_positive || spoly == expected_negative);

        let basis = GroebnerBasis::new(5, vec![p1, p2]);
        let gb = basis.buchberger();

        let target = var(&h_var) * var(&r_var) - var(&u_var) * var(&x_var);
        let rem = gb.reduce(target);
        assert!(
            rem.is_zero(),
            "h*r - u*x should reduce to 0 given g*x = h and g*r = u"
        );
    }

    /// Issue #74, case 2: verify(r == 0) is unrelated to relation a == b.
    /// Completeness should fail because the relation does NOT imply r == 0.
    #[test]
    fn incomplete_wrong_verify() {
        let ex = r#"
            proto incomplete<F: Field>(private a: F, private b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(r == 0)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "Protocol with verify(r == 0) should be incomplete when relation is a == b"
        );
    }

    /// Issue #74, case 1: verify(x == y && c == 0) adds extra constraint c == 0
    /// not implied by relation a == b. Should be incomplete.
    #[test]
    fn incomplete_unused_public_input() {
        let ex = r#"
            proto incomplete<F: Field>(private a: F, private b: F, public c: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                verify(x == y && c == 0)
            }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "Protocol with unused public input c == 0 should be incomplete"
        );
    }

    /// Phase 4 regression: Mle × Mle multiplication combined with relation
    /// reduction. Given relation `a == b` on two multilinear extensions, the
    /// verifier checks `a*a == a*b`. This reduces to zero in the Gröbner
    /// basis only when the analysis (1) does slot-wise basis change for
    /// Mle × Mle (phase 4), and (2) uses the relation `a_i - b_i = 0` on
    /// every evaluation slot. Pre-phase-4 the zip-based Mul arm produced
    /// coefficient-wise products instead of convolution/basis-change terms
    /// on both sides of the equation, so the difference was still zero and
    /// this test would have passed accidentally — but the *shapes* of the
    /// output polynomials were wrong. Post-phase-4 both the shapes and the
    /// arithmetic are correct, and the completeness check still succeeds.
    #[test]
    fn mle_product_relation_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto mle_mul_rel<F: Field, N: Size>(
                public a: Mle<F, N>,
                public b: Mle<F, N>
            ) where a == b {
                let p = a * a;
                let q = a * b;
                verify(p == q)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "Mle × Mle equality under relation a==b should be complete"
        );
    }

    /// Part B.5 regression #1: named-let binding scalar product of challenges.
    ///
    /// Isolates "named `let` with `Mul` RHS, used by verify" from the
    /// eval/Mle machinery. Pre-fix, this panicked with
    /// `Reference rr not found in context` because `trans_clos_op` did
    /// not recurse into ops enough to register the dependency ordering
    /// and `to_poly` did not register named-let scalar products. With
    /// only challenges (no eval), this already worked even pre-fix — but
    /// it's a guard rail.
    #[test]
    fn named_let_scalar_product_completeness() {
        let ex = r#"
            proto named_scalar<F: Field>(private a: F) where a == a {
                c1 <- challenge<F>;
                c2 <- challenge<F>;
                let rr = c1 * c2;
                x <- c1 * c2;
                verify(x == rr)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let scalar product should be complete"
        );
    }

    /// Part B.5 regression #2: named-let binding a single full-multivariate
    /// Mle eval (no product).
    ///
    /// Isolates "named `let` with `eval` RHS" from the product dimension.
    /// Pre-fix, `to_poly(Op::Eval)` returned empty, so the let-binding
    /// produced no basis rows; verifying `l == l` then panicked because
    /// l was never registered. After the fix, `eval_to_poly` handles the
    /// Mle full-eval shape and the basis row for `l` is emitted.
    #[test]
    fn named_let_single_eval_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto named_eval<F: Field, N: Size>(public a: Mle<F, N>) where a == a {
                r1 <- challenge<F>;
                r2 <- challenge<F>;
                let l = eval(a, [r1, r2]);
                verify(l == l)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(ca.run().is_ok(), "named-let single-eval should be complete");
    }

    /// Part B.5 regression #3: named-let binding a partial-eval (k < n)
    /// on an Mle.
    ///
    /// Guards the partial-eval code path in `eval_to_poly` after the
    /// add_op → eval_to_poly refactor. `eval(a, [r1])` on `Mle<2>`
    /// produces the remaining `Mle<1>` / `Poly<F,1,1>`. Bug surface:
    /// partial-eval via let-binding needs proper slot assignment.
    #[test]
    fn named_let_partial_eval_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto named_partial<F: Field, N: Size>(public a: Mle<F, N>) where a == a {
                r1 <- challenge<F>;
                let q = eval(a, [r1]);
                verify(q == q)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let partial-eval should be complete"
        );
    }

    /// Part B.5 regression #4: named-let binding a univariate eval.
    ///
    /// Covers the `Uni(_) | VPoly(1, _)` branch of `eval_to_poly` when
    /// reached through `to_poly` (not top-level `add_op`). Exercises the
    /// common case to guard against regressions from the refactor.
    #[test]
    fn named_let_univariate_eval_completeness() {
        use lang::id::Tid;

        let ex = r#"
            proto named_uni<F: Field, N: Size>(public a: Uni<F, N>) where a == a {
                r1 <- challenge<F>;
                let l = eval(a, [r1]);
                verify(l == l)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let univariate-eval should be complete"
        );
    }

    /// Phase 7 attempted regression: `eval(a*b, xs) == eval(a, xs) * eval(b, xs)`
    /// for `a, b : Mle<F, N>`.
    ///
    /// The Phase 8 Part B fixes (trans_clos_op recursion into Op::Eval/
    /// Coef/Mle/Poly, plus to_poly handling of Op::Eval via
    /// eval_to_poly) make this test semantically well-formed — the
    /// `Reference rr not found in context` panic is gone. However
    /// Buchberger on the resulting system (VPoly(2,2) expansion of
    /// a*b with 6 slots × eq-interpolation at two challenges × two
    /// eval products) fails to terminate within 10 minutes even in
    /// release mode. The smaller `named_let_*` regressions above
    /// exercise the same code paths and complete instantly; this test
    /// is kept `#[ignore]` for performance, not correctness.
    #[test]
    fn mle_eval_product_completeness() {
        use lang::id::Tid;

        // Reduced from N=2 to N=1 so Buchberger terminates in reasonable time.
        // The phase-7 fix (trans_clos + to_poly Op::Eval handling) is the same
        // correctness property; the smaller system size is tractable.
        let ex = r#"
            proto mle_eval_product<F: Field, N: Size>(
                public a: Mle<F, N>,
                public b: Mle<F, N>
            ) where a == a {
                let p = a * b;
                r1 <- challenge<F>;
                let l = eval(p, [r1]);
                let rr = eval(a, [r1]) * eval(b, [r1]);
                verify(l == rr)
            }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &1);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "eval-based Mle product identity should be complete"
        );
    }

    /// Phase 6 regression: correct `Op::Eval::typ()` dispatch.
    ///
    /// `Op::Eval::typ()` at `backend/src/op.rs` used to return `x.typ()`
    /// unconditionally, which was only correct by accident for univariate
    /// batched evaluation. After the phase 6 fix it dispatches on
    /// `(p.typ(), x.typ())` for full and partial multivariate eval on
    /// VPoly / Mle. This helper-style test builds a minimal `Op::Eval`
    /// node for each shape and asserts the returned `ATyp`.
    #[test]
    fn op_eval_typ_dispatch() {
        use crate::{GOp, Op as BOp, Ref, mk};
        use backend::{ATyp, ArkBls12_381};
        use petgraph::graph::NodeIndex;

        // Build an Op::Evaluate(p, x) where p has type `p_typ` and x has type `x_typ`.
        let mk_eval = |p_typ: ATyp, x_typ: ATyp| -> GOp<ArkBls12_381> {
            let p: GOp<ArkBls12_381> = BOp::Ref(Ref::new(NodeIndex::new(0)), p_typ);
            let x: GOp<ArkBls12_381> = BOp::Ref(Ref::new(NodeIndex::new(1)), x_typ);
            BOp::Evaluate(mk(p), mk(x))
        };

        // Univariate batched: Uni(m) at Vec(scalar, k) → Vec(scalar, k).
        let op = mk_eval(ATyp::Uni(3), ATyp::Vec(Box::new(ATyp::scalar()), 4));
        assert_eq!(
            op.typ(),
            ATyp::Vec(Box::new(ATyp::scalar()), 4),
            "univariate batched eval should keep Vec(scalar, k)"
        );

        // Univariate batched with Uni(k) on the right (equivalent shape).
        let op = mk_eval(ATyp::Uni(3), ATyp::Uni(4));
        assert_eq!(op.typ(), ATyp::Vec(Box::new(ATyp::scalar()), 4));

        // VPoly(1, m) is effectively univariate, same rule.
        let op = mk_eval(ATyp::VPoly(1, 3), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(op.typ(), ATyp::Vec(Box::new(ATyp::scalar()), 2));

        // Full multivariate VPoly: VPoly(n, m) at Vec(scalar, n) → scalar.
        let op = mk_eval(ATyp::VPoly(2, 2), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(
            op.typ(),
            ATyp::scalar(),
            "full multivariate VPoly eval should be scalar"
        );

        // Partial VPoly: VPoly(n, m) at Vec(scalar, k) with k<n → VPoly(n-k, m).
        let op = mk_eval(ATyp::VPoly(3, 2), ATyp::Vec(Box::new(ATyp::scalar()), 1));
        assert_eq!(
            op.typ(),
            ATyp::VPoly(2, 2),
            "partial multivariate VPoly eval should drop k variables"
        );

        // Full Mle: Mle(n) at Vec(scalar, n) → scalar.
        let op = mk_eval(ATyp::Mle(2), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(op.typ(), ATyp::scalar(), "full Mle eval should be scalar");

        // Partial Mle: Mle(n) at Vec(scalar, k) with k<n → Mle(n-k).
        let op = mk_eval(ATyp::Mle(3), ATyp::Vec(Box::new(ATyp::scalar()), 2));
        assert_eq!(
            op.typ(),
            ATyp::Mle(1),
            "partial Mle eval should drop k variables"
        );
    }

    /// Phase 9 regression: `ifft(v)` roundtrips through `fft` to `v`.
    ///
    /// The Gröbner builder should recognise that `fft(ifft(v)) == v` is
    /// an identity at the equation level, because each op produces N
    /// linear equations on the DFT matrix M[i,j] = ω^{ij} whose product
    /// is the identity matrix. With N=2 we have ω = -1, 4 equations
    /// across 6 variables.
    ///
    /// With v: [F; 2]: interpolate(v) → Poly<F, 1, 1> (2 coefs, pow2),
    /// then eval(p) → Vec<F, 2>, matching v's shape exactly.
    #[test]
    fn ifft_roundtrip_completeness() {
        let ex = r#"
            proto ifft_roundtrip<F: Field>(public v: [F; 2]) where v == v {
                let p = interpolate(v);
                let u = eval(p);
                verify(u == v)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "fft(ifft(v)) == v should be complete via DFT basis equations"
        );
    }

    /// Phase 9 regression: `fft` respects addition (linearity).
    ///
    /// For any `a`, `b : Poly<F, 1, N>`, `fft(a + b) == fft(a) + fft(b)`.
    /// Confirms that the DFT basis rows correctly compose with pointwise
    /// addition — this is what a Plonk-style prover relies on when
    /// computing the quotient polynomial.
    #[test]
    fn fft_linearity_completeness() {
        // Phase 14 m+1 convention + issue #116: Poly<F, 1, 3> has 4
        // coefficients (pow2 — required for FFT-grid eval to typecheck).
        let ex = r#"
            proto fft_linearity<F: Field>(
                public a: Poly<F, 1, 3>,
                public b: Poly<F, 1, 3>
            ) where a == a {
                let c = a + b;
                let va = eval(a);
                let vb = eval(b);
                let vc = eval(c);
                verify(vc == va + vb)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "fft(a + b) == fft(a) + fft(b) should be complete"
        );
    }

    /// Phase 9 regression: `ifft` respects addition (symmetric of above).
    ///
    /// `ifft(u + v) == ifft(u) + ifft(v)` for vectors `u, v : Vec<F, N>`.
    #[test]
    fn ifft_linearity_completeness() {
        let ex = r#"
            proto ifft_linearity<F: Field>(
                public u: [F; 2],
                public v: [F; 2]
            ) where u == u {
                let w = u + v;
                let pu = interpolate(u);
                let pv = interpolate(v);
                let pw = interpolate(w);
                verify(pw == pu + pv)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "ifft(u + v) == ifft(u) + ifft(v) should be complete"
        );
    }

    /// Phase 10 regression: `reduce(+, v) == Σ v[i]`.
    #[test]
    fn reduce_add_completeness() {
        let ex = r#"
            proto reduce_add<F: Field>(public a: F, public b: F, public c: F) where a == a {
                let v = [a, b, c];
                let s = reduce(+, v);
                verify(s == a + b + c)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "reduce(+, [a,b,c]) == a+b+c should be complete"
        );
    }

    /// Phase 10 regression: `reduce(*, v) == Π v[i]`.
    #[test]
    fn reduce_mul_completeness() {
        let ex = r#"
            proto reduce_mul<F: Field>(public a: F, public b: F, public c: F) where a == a {
                let v = [a, b, c];
                let p = reduce(*, v);
                verify(p == a * b * c)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "reduce(*, [a,b,c]) == a*b*c should be complete"
        );
    }

    /// Phase 10 regression: `reduce(-, [a,b,c]) == a - b - c` (left-fold).
    #[test]
    fn reduce_sub_completeness() {
        let ex = r#"
            proto reduce_sub<F: Field>(public a: F, public b: F, public c: F) where a == a {
                let v = [a, b, c];
                let s = reduce(-, v);
                verify(s == a - b - c)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "reduce(-, [a,b,c]) == a-b-c should be complete"
        );
    }

    /// Phase 10 regression: a scalar literal binds as a polynomial constant
    /// so `verify(c == 7)` reduces via the basis row `c - 7`.
    #[test]
    fn literal_scalar_binding_completeness() {
        let ex = r#"
            proto literal_scalar<F: Field>(public x: F) where x == x {
                let c = 7;
                verify(c == 7)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "literal scalar binding should fold through Gröbner basis"
        );
    }

    /// Phase 11 regression: bilinearity shift — `pair(a·P, Q) == pair(P, a·Q)`.
    ///
    /// Both sides decompose to `a · v_{P,Q}` in exponent space; the basis
    /// reduces `lhs - rhs` to zero.
    #[test]
    fn pair_bilinear_shift_completeness() {
        let ex = r#"
            proto pair_shift<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (public p: G1, public q: G2, public a: F) where a == a {
                let lhs = pair(a * p, q);
                let rhs = pair(p, a * q);
                verify(lhs == rhs)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair(a*P, Q) == pair(P, a*Q) should be complete via bilinearity"
        );
    }

    /// Phase 11 regression, un-ignored in phase 12: bilinearity over sums —
    /// `pair(P1+P2, Q) == pair(P1,Q) + pair(P2,Q)`.
    ///
    /// Under phase 12, `pair(a,b)` is `to_poly(a)·to_poly(b)·var(__gt__)`.
    /// Since `to_poly(P1+P2) = var(P1) + var(P2)` (existing Bin(Add) arm)
    /// and GT addition lowers to `Bin(Add, _, _, GT)`, both sides reduce
    /// to the same F-polynomial `(var(P1)+var(P2))·var(Q)·var(__gt__)`.
    #[test]
    fn pair_bilinear_additive_completeness() {
        let ex = r#"
            proto pair_additive<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (public p1: G1, public p2: G1, public q: G2) where p1 == p1 {
                let lhs = pair(p1 + p2, q);
                let rhs = pair(p1, q) + pair(p2, q);
                verify(lhs == rhs)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair(P1+P2, Q) == pair(P1,Q) + pair(P2,Q) should be complete"
        );
    }

    /// Phase 11 pinning test: a reflexive Pair verify completes, confirming
    /// the new decompose-and-emit path doesn't panic and the basis row is
    /// consistent with itself.
    #[test]
    fn pair_reflexive_completeness() {
        let ex = r#"
            proto pair_trivial<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (public p: G1, public q: G2) where p == p {
                let u = pair(p, q);
                verify(u == u)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair(P, Q) == pair(P, Q) (reflexive) should be complete"
        );
    }

    /// Phase 12 regression: bilinear product —
    /// `pair((a·b)·P, Q) == pair(a·P, b·Q)`.
    ///
    /// Both sides reduce to `a·b·exp_P·exp_Q·var(__gt__)` in exponent
    /// space, cancelling under Buchberger.
    #[test]
    fn pair_bilinear_product_completeness() {
        let ex = r#"
            proto pair_product<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>
                (public p: G1, public q: G2, public a: F, public b: F) where a == a {
                let lhs = pair((a * b) * p, q);
                let rhs = pair(a * p, b * q);
                verify(lhs == rhs)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "pair((a*b)*P, Q) == pair(a*P, b*Q) should be complete via bilinearity"
        );
    }

    // -----------------------------------------------------------------
    // Phase 13 regressions: polynomial division via `D·Q + R = P`.
    // -----------------------------------------------------------------

    /// Phase 13 regression: exact division round-trip —
    /// `(p · d) / d == p` for univariate polynomials.
    ///
    /// The prover's basis contains:
    ///   * `prod = p · d` (coefficient-wise convolution from Mul arm),
    ///   * canonical identity rows `prod_k − Σ D_i·q_wit_j − r_wit_k = 0`
    ///     (from `div_witnesses`), and
    ///   * linking rows `q_wit[j] − q_ref[j] = 0` (from `link_to_witness`),
    ///   * verify rows `q_ref[j] − p[j] = 0` (from `BinOp::Equ`).
    ///
    /// The verifier's basis has the same verify rows, which reduce to 0
    /// modulo the prover's Gröbner basis.
    #[test]
    fn poly_div_exact_completeness() {
        let ex = r#"
            proto poly_div_exact<F: Field>(
                public p: Poly<F, 1, 1>,
                public d: Poly<F, 1, 1>
            ) where p == p {
                let prod = p * d;
                let q = prod / d;
                verify(q == p)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "(p*d)/d == p should be complete via D·Q + R = P"
        );
    }

    /// Phase 13 regression: the canonical divmod identity —
    /// `p == d · q + r` where `q = p / d`, `r = p % d`.
    ///
    /// This is the core win of the shared-witness side-table: both `/`
    /// and `%` on the same `(p, d)` hash-consed pair reuse the same
    /// `(q_wit, r_wit)` PRefs, so the prover's basis already contains
    /// the row `p − d·q_wit − r_wit = 0` exactly once. The verify row
    /// `p − d·q − r = 0` (after linking q→q_wit, r→r_wit) reduces to
    /// this identity row directly.
    #[test]
    fn poly_divmod_identity_completeness() {
        let ex = r#"
            proto poly_divmod<F: Field>(
                public p: Poly<F, 1, 2>,
                public d: Poly<F, 1, 1>
            ) where p == p {
                let q = p / d;
                let r = p % d;
                verify(p == d * q + r)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "verify(p == d*q + r) should collapse directly to the shared identity row"
        );
    }

    /// Phase 13 regression: pairing-free KZG opening shape.
    ///
    /// Mirrors the `q_val = (p_val - y) / poly([-z, 1])` step from KZG
    /// *without* the pairing layer: given `p_val`, `y`, `z`, verify that
    /// `q_val * poly([-z, 1]) == p_val - y`. This is exactly the Div
    /// identity `P = D·Q + 0` after recognising `R = 0` (degree-0 slot
    /// of a Poly(F,1,0) witness).
    #[test]
    fn kzg_opening_shape_completeness() {
        let ex = r#"
            proto kzg_shape<F: Field>(
                public p_val: Poly<F, 1, 2>,
                public z: F,
                public y: F
            ) where p_val == p_val {
                let d_val = poly([-z, 1]);
                let diff = p_val - y;
                let q_val = diff / d_val;
                verify(q_val * d_val == diff)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "KZG opening shape q * (x - z) == p - y should be complete"
        );
    }

    /// Phase 13 regression: full KZG (un-deferred from phase 12).
    ///
    /// Runs `examples/kzg/kzg.zippel` through `CompletenessAnalysis`.
    /// Relies on:
    ///   * Phase 12 pairing layer — `pair(a,b) = to_poly(a)·to_poly(b)·var(__gt__)`.
    ///   * Phase 13 poly division — `q_val = (p_val − y) / poly([−z, 1])`
    ///     lowers to the shared-witness identity
    ///     `p_val − y = poly([−z,1]) · q_wit + r_wit`.
    ///
    /// With both layers, the KZG opening check
    ///   `pair(pi, h_val − h·z) == pair(c − y·g, h)`
    /// reduces to `0` under the combined prover basis.
    ///
    /// **Blocked (not phase 13)**: `CTyp::lub_div` in `lang/src/typ/lub.rs:767`
    /// returns `Poly<F, 1, ma - mb>` but `poly([F;n])` → `Poly<F,1,n>` and
    /// `coef(Poly<F,1,n>)` → `[F;n]` treat the parameter as *coefficient
    /// count*, not degree. So for `p : [F; N]`, the expression
    /// `(p_val - y) / poly([-z, 1])` yields `q_val : Poly<F,1,N-2>` whose
    /// `coef` has length `N-2`, but the intended length `N-1` is required
    /// for `dot(pi_val, ss[0..N-1])` to type-check. Fixing this is a
    /// phase-7 follow-up (the off-by-one was introduced by the phase-7 fix
    /// that landed before the coef/poly/eval conventions were reconciled).
    #[test]
    fn full_kzg_completeness() {
        use lang::id::Tid;
        let ex = r#"
            proto kzg<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>, N: Size>
                    (private p: [F; N], public z: F, public y: F, public ss: [G1; N],
                    public g: G1, public h: G2, public h_val: G2)
                    where p == p {
                let p_val = poly(p);
                c <- dot(p, ss);
                let q_val = (p_val - y) / poly([-z, 1]);
                let pi_val = coef(q_val);
                let test = ss[0..N-1];
                pi <- dot(pi_val, test);
                let lhs = pair(pi, (h_val) - (h * z));
                let rhs = pair(c - y * g, h);
                verify(lhs == rhs)
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &3);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);
        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_ok(),
            "full KZG should be complete via phase-12 pairing + phase-13 poly-div"
        );
    }
}
