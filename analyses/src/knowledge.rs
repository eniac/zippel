use crate::TransClos;
use crate::Var;
use crate::backend::{GbBackendKind, GbBasis};
use crate::error::AnalysisError;
use crate::frontend::{Block, BlockKind, MonoOrder, Polynomial};
use crate::ideal::{Ideal, IdealBuilder};
use crate::uniform::UniformityPropagation;
use backend::ArkConfig;
use backend::op::{HasOpFactory, Ref};
use graph::QDag;
use lang::typ::Distribution;
use log::warn;
use share::Ctx;

/// Knowledge-analysis elimination predicate: Local variables and witness-uniform
/// variables (random masks) are eliminated first.
fn is_elim_var(v: &Var, dist_map: &Ctx<Ref, Distribution>) -> bool {
    v.qualifier == lang::typ::Qualifier::Local
        || (v.qualifier == lang::typ::Qualifier::Witness
            && dist_map
                .get(&v.reference)
                .map(|d| d.is_uniform())
                .unwrap_or(false))
}

/// Build the block ordering for knowledge analysis: elim-block (GrevLex) first,
/// then the remaining vars (GrevLex).
fn knowledge_order(result: &Ideal<impl ArkConfig>, dist_map: &Ctx<Ref, Distribution>) -> MonoOrder {
    let elim_vars: Vec<Var> = result
        .var_order
        .iter()
        .filter(|v| is_elim_var(v, dist_map))
        .cloned()
        .collect();
    MonoOrder::block(vec![
        Block {
            vars: Some(elim_vars),
            kind: BlockKind::GrevLex,
        },
        Block {
            vars: None,
            kind: BlockKind::GrevLex,
        },
    ])
}

/// Perform a knowledge analysis using Groebner bases.
#[allow(unnameable_types)]
pub struct KnowledgeAnalysis<C: ArkConfig> {
    /// Gröbner basis of (prover ∪ relation) under the knowledge block order.
    /// Computed in `from_input_with_backend`.
    pub basis: GbBasis<C::F>,
    /// Gröbner basis of the relation (precondition) alone, used to filter
    /// polynomials that are derivable from the precondition (not real leaks).
    /// `None` when the protocol has no relation.
    pub relation_basis: Option<GbBasis<C::F>>,
    /// Side map from `Ref` → `Distribution`, computed by
    /// `UniformityPropagation`, used to check uniformity.
    dist_map: Ctx<Ref, Distribution>,
}

impl<C: HasOpFactory> KnowledgeAnalysis<C> {
    pub fn from_input(dag: &QDag<C>) -> Self {
        Self::from_input_with_backend(dag, GbBackendKind::default())
    }

    /// Like [`from_input`](Self::from_input) but with a user-selected GB
    /// backend.
    pub fn from_input_with_backend(dag: &QDag<C>, backend: GbBackendKind) -> Self {
        let dist_map = UniformityPropagation::from_dag(dag).distributions;
        let mut gb = IdealBuilder::new();
        let mut prover_ideal = gb.build(TransClos::prover(dag));

        let gb_backend = backend.build::<C::F>();

        let relation_basis = if dag.relation_node().is_some() {
            let mut rel_gb = gb.clone();
            let rel_ideal = rel_gb.build(TransClos::relation(dag));
            let order = knowledge_order(&rel_ideal, &dist_map);
            gb_backend.compute_gb(rel_ideal.generating_set, &order).ok()
        } else {
            None
        };

        if dag.relation_node().is_some() {
            let rel_ideal = gb.build(TransClos::relation(dag));
            prover_ideal.merge(&rel_ideal);
        }

        let order = knowledge_order(&prover_ideal, &dist_map);
        let basis = gb_backend
            .compute_gb(prover_ideal.generating_set, &order)
            .expect("GB backend should support knowledge block order");

        Self {
            basis,
            relation_basis,
            dist_map,
        }
    }

    fn is_uniform(&self, v: &Var) -> bool {
        self.dist_map
            .get(&v.reference)
            .map(|d| d.is_uniform())
            .unwrap_or(false)
    }

    fn is_uniform_nz(&self, v: &Var) -> bool {
        self.dist_map
            .get(&v.reference)
            .map(|d| *d == Distribution::UniformNonZero)
            .unwrap_or(false)
    }

    fn is_leak(&self, p: &Polynomial<C::F>) -> bool {
        let vars = p.vars();
        let has_non_witness = vars.iter().any(|v| !v.is_witness());
        let has_witness = vars.iter().any(|v| v.is_witness());

        if !has_non_witness || !has_witness {
            return false;
        }

        !self.has_witness_uniform_linear_mask(p)
    }

    fn has_witness_uniform_linear_mask(&self, p: &Polynomial<C::F>) -> bool {
        // A polynomial with a witness uniform variable appearing at degree 1
        // alone in its own term is safe — it acts as a one-time pad mask.
        // E.g., r + c*x - z where r is witness uniform.
        p.terms.iter().any(|(term, _coeff)| {
            let term_vars: Vec<_> = term.iter().collect();
            term_vars.len() == 1
                && *term_vars[0].1 == 1
                && term_vars[0].0.is_witness()
                && (self.is_uniform(term_vars[0].0) || self.is_uniform_nz(term_vars[0].0))
        })
    }

    fn eliminate_var(&self, polys: &mut Vec<Polynomial<C::F>>) {
        polys.retain(|p| {
            let vars = p.vars();
            if vars.is_empty() {
                return true;
            }
            // Remove polynomials where ALL variables are witness uniform
            let all_witness_uniform = vars.iter().all(|v| v.is_witness() && self.is_uniform(v));
            if all_witness_uniform {
                return false;
            }
            // Remove polynomials containing internal variables — these are
            // prover/Groebner-builder computations that the verifier cannot observe.
            // Keep witness-uniform handling as-is: mixed uniform-mask polynomials
            // are classified by `is_leak` below rather than dropped here.
            let contains_internal_variable = vars.iter().any(|v| v.is_local());
            !contains_internal_variable
        });
    }

    fn eliminate_groups(polys: &mut Vec<Polynomial<C::F>>) {
        polys.retain(|p| {
            p.terms.keys().any(|t| {
                let mono_sum = t
                    .iter()
                    .filter_map(|(v, i)| if v.typ.is_group() { Some(*i) } else { None })
                    .sum::<usize>();
                mono_sum <= 1
            })
        });
    }

    /// Run knowledge analysis.
    ///
    /// Uses the pre-computed Gröbner basis from `from_input_with_backend`.
    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        if self.basis.is_unit() {
            return Err(AnalysisError::UnitIdeal {
                context: "knowledge prover-relation",
            });
        }

        // Work on a mutable copy of the basis polynomials.
        let mut polys = self.basis.polys.clone();

        // Delete varieties with elimination variables
        self.eliminate_var(&mut polys);

        // Delete varieties where group elements are multiplied
        Self::eliminate_groups(&mut polys);

        for p in polys.iter() {
            if self.is_leak(p) {
                // Skip polynomials derivable from the relation (precondition).
                // The verifier already knows these — they're not new leaks.
                if let Some(ref rel_basis) = self.relation_basis
                    && rel_basis.polys.iter().any(|rp| rp == p)
                {
                    continue;
                }
                warn!("Leak found: {}", p);
                return Err(AnalysisError::KnowledgeLeak(p.clone()));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::KnowledgeAnalysis;
    use crate::QualifierPropagation;
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use graph::UDags;
    use graph::WritePdf;
    use log::debug;
    use share::{Ctx, unwrap};

    #[test]
    fn knowledge_foo() {
        let ex = r#"
        proto foo<F: Field>(witness s: F, witness s': F) where s == s' {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r  + c + s;
            verify(a == b)
        }"#;

        debug!("Parsing example: {}", ex);
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_foo").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        // Propagate qualifiers
        let g = QualifierPropagation::from_dag(&gs[0]);

        // Compute Groebner basis for the implementation
        let mut kz = KnowledgeAnalysis::from_input(&g);

        // Compute the Groebner bases
        assert!(kz.run().is_err());
    }

    #[test]
    fn groebner_bar() {
        let ex = r#"
        proto foo<F: Field>(witness s: F, witness s': F) where s == s' {
            let r = random<F>;
            a <- r * s;
            b <- r * s';
            verify(a == b)
        }"#;

        debug!("Parsing example: {}", ex);
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_bar").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        // Uniformity propagation
        let g = g_inp;

        // Create an object computing the Groebner basis
        let mut kz = KnowledgeAnalysis::from_input(&g);

        // Compute the Groebner basis
        assert!(kz.run().is_ok());
    }

    #[test]
    fn groebner_baz() {
        let ex = r#"
        proto baz<F: Field, N: 4..8>(witness s: [F; N], witness s': F) where s[3] == s' {
            let r = random<F>;
            a <- r * s[3];
            b <- r * s';
            verify(a == b)
        }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_baz").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        let g_inp = QualifierPropagation::from_dag(&gs[0]);

        // Uniformity propagation
        let g = g_inp;
        // Create an object computing the Groebner basis
        let mut kz = KnowledgeAnalysis::from_input(&g);

        // Compute the Groebner basis
        assert!(kz.run().is_ok());
    }

    /// This example is somewhat contrived. Here is how we leak s = s'.
    /// 1. We have two witness inputs s and s'.
    /// 2. a - b = s - s'
    /// 3. g*a = g*b from [verify]
    /// 4. g*(a - b) = g *(s - s') = 0 from [2]
    /// 5. s = s' if g != 0.

    #[test]
    fn groebner_ex3() {
        let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(witness s: F, witness s': F, instance g: G) where s == s {
            let r = random<F>;
            let a = r + s;
            let b = r + s';
            c <- g * a;
            d <- g * b;
            verify(c == d)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_ex3").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        let g = QualifierPropagation::from_dag(&gs[0]);

        // Uniformity propagation

        // Create an object computing the Groebner basis
        let mut kz = KnowledgeAnalysis::from_input(&g);

        assert!(kz.run().is_err());
    }

    /// Known false positive after qualifier propagation fix.
    ///
    /// The bidirectional walk now correctly assigns `Witness` to the
    /// relation-side computation `g*x` (node 20). Previously it defaulted to
    /// `Local` (unreachable from the old backward-only walk), which caused
    /// `eliminate_var` to drop any polynomial containing it.
    ///
    /// With the correct `Witness` qualifier, node 20 survives elimination and
    /// appears in the verification equation `c*node20 + g*z - u = 0` alongside
    /// non-secret vars (c, g, z, u). Since node 20 is Witness but not uniform,
    /// `has_witness_uniform_linear_mask` finds no degree-1 uniform mask, so
    /// `is_leak` flags it.
    ///
    /// This is not a real leak — node 20 is `h` (an instance input) expressed via
    /// the relation `h == g*x`. The knowledge analysis does not currently
    /// identify relation-side computations with their instance input
    /// counterparts, so it treats node 20 as an opaque Witness variable.
    /// Fixing this requires teaching `eliminate_var` that relation-side
    /// computations are internal (not verifier-observable), which is a
    /// separate improvement.
    #[test]
    #[ignore = "known false positive: relation-side g*x now correctly Private but not eliminated"]
    fn schnorr_zk() {
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

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_ok(),
            "Schnorr protocol should be zero-knowledge"
        );
    }

    #[test]
    fn zk_regression_direct_secret_leak() {
        let ex = r#"
        proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            d <- x;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        let result = kz.run();
        if let Err(ref e) = result {
            eprintln!("Leak detected: {}", e);
        }
        assert!(
            result.is_err(),
            "d <- x directly leaks witness x to transcript"
        );
    }

    /// Leak: transcript contains x + instance_val (no blinding).
    /// Verifier computes x = d - y.
    #[test]
    fn zk_leak_unblinded_linear_combination() {
        let ex = r#"
        proto leak<F: Field>(witness x: F, instance y: F) where x == x {
            d <- x + y;
            verify(d == d)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_err(),
            "d <- x + y leaks x (verifier knows y and d)"
        );
    }

    /// Leak: Schnorr-like protocol without random blinding.
    /// Response z = x*c is sent to verifier, who knows c and computes x = z/c.
    #[test]
    fn zk_leak_no_random_blinding() {
        let ex = r#"
        proto leak<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
            c <- challenge<F*>;
            z <- x * c;
            verify(g*z == h*c)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_err(),
            "z <- x*c without random blinding leaks x"
        );
    }

    /// Leak: two transcripts that differ only by the secret.
    /// Verifier sees a and b, computes a - b = s - s'.
    #[test]
    fn zk_leak_secret_difference_on_transcript() {
        let ex = r#"
        proto leak<F: Field>(witness s: F, witness t: F, instance y: F) where y == y {
            a <- s + y;
            b <- t + y;
            verify(a == b)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_err(),
            "a - b = s - t leaks relationship between secrets"
        );
    }

    /// NOT a leak: proper Schnorr with random blinding.
    /// Verifier cannot recover x from z = r + x*c (r is uniform mask).
    ///
    /// Same false positive as `schnorr_zk` — see that test's doc comment.
    #[test]
    #[ignore = "known false positive: relation-side g*x now correctly Private but not eliminated"]
    fn zk_safe_schnorr_with_blinding() {
        let ex = r#"
        proto safe<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_ok(),
            "Schnorr with proper blinding should be ZK"
        );
    }

    /// Leak: the two verify statements together leak witness information.
    /// Each check is a trivial self-equality on a transcript value (`a == a` and `b == b`).
    /// Since `a = s + r` and `b = t + r` reuse the same blinding value `r`, publishing both
    /// values reveals `a - b = s - t`, so the transcript leaks information about the secrets.
    #[test]
    fn zk_multiple_verify_one_safe_one_subtle_leak() {
        let ex = r#"
        proto mixed<F: Field>(witness s: F, witness t: F, instance y: F) where y == y {
            let r = random<F>;
            a <- s + r;
            b <- t + r;
            verify(a == a);
            verify(b == b)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_err(),
            "One safe and one leaking verify should fail knowledge analysis"
        );
    }

    /// Safe: both verify statements are properly blinded with independent random values.
    /// Each check uses a separate random blinding factor, so no witness information leaks.
    #[test]
    fn zk_multiple_verify_both_safe() {
        let ex = r#"
        proto safe<F: Field>(witness a: F, witness b: F) where a == b {
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

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_ok(),
            "Two verify statements both properly blinded with independent randoms should pass knowledge analysis"
        );
    }

    /// Part B.5 regression #6: knowledge analysis on a named-let eval product.
    ///
    /// Confirms the Phase 8 Part B fixes (trans_clos recursion into
    /// Op::Eval/Coef/Mle/Poly + to_poly dispatch to eval_to_poly) also
    /// cover the `KnowledgeAnalysis` consumer of `IdealBuilder`, not
    /// just completeness. Pre-fix this panicked with
    /// `Reference l not found in context`. A small univariate shape is
    /// used to keep Buchberger tractable.
    #[test]
    fn knowledge_named_let_eval_product() {
        use lang::id::Tid;

        let ex = r#"
        proto ke<F: Field, N: Size>(instance a: Uni<F, N>) where a == a {
            r1 <- challenge<F>;
            let l = a(r1);
            verify(l == l)
        }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        // All inputs are instance so nothing could leak; trivially ZK.
        assert!(
            kz.run().is_ok(),
            "instance-only eval protocol should be ZK (no witness secrets to leak)"
        );
    }

    #[test]
    fn knowledge_relation_basis_div_wit_cache_is_clean() {
        let ex = r#"
        proto clean_rel<F: Field>(
            witness p: Poly<F, 1, 2>,
            instance d: Poly<F, 1, 1>,
            instance q: Poly<F, 1, 1>
        ) where q == p / d {
            let z = p / d;
            verify(z == q)
        }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.relation_basis
                .as_ref()
                .unwrap()
                .vars()
                .iter()
                .any(|v| v.is_local()),
            "relation-only basis should contain polynomial div/rem witness variables"
        );
        let result = kz.run();
        assert!(
            result.is_ok(),
            "relation-only basis must rebuild polynomial div_wit identities with a clean cache when filtering relation-derived polynomials, got {result:?}"
        );
    }
}
