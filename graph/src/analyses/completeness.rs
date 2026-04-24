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
        if let Some((old_idx, original_ref)) = inverse.get(&pref.node()) {
            let new_ref = match (original_ref, &pref.reference) {
                (Ref::Var(v, _), _) => Ref::Var(v.clone(), *old_idx),
                (Ref::Node(_), Ref::Var(v, _)) => Ref::Var(v.clone(), *old_idx),
                (Ref::Node(_), Ref::Node(_)) => Ref::Node(*old_idx),
            };
            PRef {
                reference: new_ref,
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

        // Build relation basis directly from full DAG (shared namespace)
        let mut g_rel = GroebnerBuilder::new();
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
    #[ignore]
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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let gb = basis.buchberger_and_reduce();

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

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
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        let mut ca = CompletenessAnalysis::from_input(&g);
        assert!(
            ca.run().is_err(),
            "Protocol with unused public input c == 0 should be incomplete"
        );
    }
}
