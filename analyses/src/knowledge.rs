use crate::TransClos;
use crate::backend::{GbBackend, GbBasis, ark_gb::ArkGb};
use crate::error::AnalysisError;
use crate::frontend::{Block, BlockKind, MonoOrder, Polynomial};
use crate::ideal::{Ideal, IdealBuilder};
use backend::ArkConfig;
use backend::op::HasOpFactory;
use graph::{DQDag, PRef};
use log::warn;

/// Knowledge-analysis elimination predicate: Local variables and private-uniform
/// variables (random masks) are eliminated first.
fn is_elim_var(v: &PRef) -> bool {
    v.qualifier == lang::typ::Qualifier::Local
        || (v.qualifier == lang::typ::Qualifier::Private && v.distribution.is_uniform())
}

/// Build the block ordering for knowledge analysis: elim-block (GrevLex) first,
/// then the remaining vars (GrevLex).
fn knowledge_order(result: &Ideal<impl ArkConfig>) -> MonoOrder {
    let elim_vars: Vec<PRef> = result
        .var_order
        .iter()
        .filter(|v| is_elim_var(v))
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
    prover_rel_ideal: Ideal<C>,
    /// Gröbner basis of the relation (precondition) alone, used to filter
    /// polynomials that are derivable from the precondition (not real leaks).
    relation_basis: Option<GbBasis<C::F>>,
}

impl<C: ArkConfig + HasOpFactory> KnowledgeAnalysis<C> {
    pub fn new(gb: Ideal<C>) -> Self {
        Self {
            prover_rel_ideal: gb,
            relation_basis: None,
        }
    }

    pub fn from_input(dag: &DQDag<C>) -> Self {
        Self::from_input_with_w(dag)
    }

    pub fn from_input_with_w(dag: &DQDag<C>) -> Self {
        let mut gb = IdealBuilder::new();
        let mut prover_ideal = gb.build(TransClos::prover(dag));

        let backend = ArkGb::default();

        let relation_basis = if dag.relation_node().is_some() {
            let mut rel_gb = gb.fork_with_clean_div_witness_cache();
            let rel_ideal = rel_gb.build(TransClos::relation(dag));
            let order = knowledge_order(&rel_ideal);
            backend.compute_gb(rel_ideal.generating_set, &order).ok()
        } else {
            None
        };

        if dag.relation_node().is_some() {
            let rel_ideal = gb.build(TransClos::relation(dag));
            prover_ideal.merge(&rel_ideal);
        }

        Self {
            prover_rel_ideal: prover_ideal,
            relation_basis,
        }
    }

    #[cfg(test)]
    pub fn from_relation(dag: &DQDag<C>) -> Self {
        let mut gb = IdealBuilder::new();
        let prover_rel_ideal = gb.build(TransClos::relation(dag));
        Self {
            prover_rel_ideal,
            relation_basis: None,
        }
    }

    fn is_leak(p: &Polynomial<C::F>) -> bool {
        let vars = p.vars();
        let has_public = vars.iter().any(|v| v.is_public());
        let has_private = vars.iter().any(|v| v.is_private());

        if !has_public || !has_private {
            return false;
        }

        !Self::has_private_uniform_linear_mask(p)
    }

    fn has_private_uniform_linear_mask(p: &Polynomial<C::F>) -> bool {
        // A polynomial with a private uniform variable appearing at degree 1
        // alone in its own term is safe — it acts as a one-time pad mask.
        // E.g., r + c*x - z where r is private uniform.
        p.terms.iter().any(|(term, _coeff)| {
            let term_vars: Vec<_> = term.iter().collect();
            term_vars.len() == 1
                && *term_vars[0].1 == 1
                && term_vars[0].0.is_private()
                && (term_vars[0].0.is_uniform() || term_vars[0].0.is_uniform_nz())
        })
    }

    pub fn private(&self) -> Vec<PRef> {
        self.prover_rel_ideal
            .vars()
            .into_iter()
            .filter(|v| v.is_private())
            .collect()
    }

    pub fn public(&self) -> Vec<PRef> {
        self.prover_rel_ideal
            .vars()
            .into_iter()
            .filter(|v| v.is_public())
            .collect()
    }

    pub fn eliminate_var(&mut self) {
        self.prover_rel_ideal.generating_set.retain(|p| {
            let vars = p.vars();
            if vars.is_empty() {
                return true;
            }
            // Remove polynomials where ALL variables are private uniform
            let all_private_uniform = vars.iter().all(|v| v.is_private() && v.is_uniform());
            if all_private_uniform {
                return false;
            }
            // Remove polynomials containing internal variables — these are
            // prover/Groebner-builder computations that the verifier cannot observe.
            // Keep private-uniform handling as-is: mixed uniform-mask polynomials
            // are classified by `is_leak` below rather than dropped here.
            let contains_internal_variable = vars.iter().any(|v| v.is_local());
            !contains_internal_variable
        });
    }

    pub fn eliminate_groups(&mut self) {
        self.prover_rel_ideal.eliminate_monomial(&|t| {
            let mono_sum = t
                .iter()
                .filter_map(|(v, i)| if v.typ.is_group() { Some(*i) } else { None })
                .sum::<usize>();
            mono_sum > 1
        });
    }

    /// Run knowledge analysis.
    ///
    /// Uses the default packed monomial width (W=128, supports up to 1023
    /// variables). Use [`ArkGb::with_width`] to override for smaller problems.
    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        let backend = ArkGb::default();
        let order = knowledge_order(&self.prover_rel_ideal);

        // Compute the Groebner basis
        let gb = backend
            .compute_gb(
                std::mem::take(&mut self.prover_rel_ideal.generating_set),
                &order,
            )
            .expect("ark-gb backend should support knowledge block order");

        if gb.is_unit() {
            eprintln!(
                "WARNING: knowledge analysis: Groebner basis reduced to the unit ideal \
                 (contains 1). This indicates the protocol is self-contradictory or that \
                 something went wrong computing the basis. Please report this to the zippel \
                 developers."
            );
        }

        self.prover_rel_ideal.generating_set = gb.polys.clone();

        // Delete varieties with elimination variables
        self.eliminate_var();

        // Delete varieties where group elements are multiplied
        self.eliminate_groups();

        for p in self.prover_rel_ideal.generating_set.iter() {
            if Self::is_leak(p) {
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
    use crate::{QualifierPropagation, UniformityPropagation};
    use backend::ArkBls12_381;
    use graph::UDags;
    use graph::WritePdf;
    use lang::ast::UModule;
    use log::debug;
    use share::{Ctx, unwrap};

    #[test]
    fn knowledge_foo() {
        let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r  + c + s;
            verify(a == b)
        }"#;

        debug!("Parsing example: {}", ex);
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_foo").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        // Propagate qualifiers
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        // Compute Groebner basis for the implementation
        let mut kz = KnowledgeAnalysis::from_input(&g);

        // Compute the Groebner bases
        assert!(kz.run().is_err());
    }

    #[test]
    fn groebner_bar() {
        let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            a <- r * s;
            b <- r * s';
            verify(a == b)
        }"#;

        debug!("Parsing example: {}", ex);
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_bar").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        let g_inp = QualifierPropagation::from_dag(&gs[0]);
        // Uniformity propagation
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);

        // Create an object computing the Groebner basis
        let mut kz = KnowledgeAnalysis::from_input(&g);

        // Compute the Groebner basis
        assert!(kz.run().is_ok());
    }

    #[test]
    fn groebner_baz() {
        let ex = r#"
        proto baz<F: Field, N: 4..8>(private s: [F; N], private s': F) where s[3] == s' {
            let r = random<F>;
            a <- r * s[3];
            b <- r * s';
            verify(a == b)
        }"#;

        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_baz").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        let g_inp = QualifierPropagation::from_dag(&gs[0]);

        // Uniformity propagation
        let g = UniformityPropagation::from_dag(&g_inp).annotate_dag(&g_inp);
        // Create an object computing the Groebner basis
        let mut kz = KnowledgeAnalysis::from_input(&g);

        // Compute the Groebner basis
        assert!(kz.run().is_ok());
    }

    /// This example is somewhat contrived. Here is how we leak s = s'.
    /// 1. We have two private inputs s and s'.
    /// 2. a - b = s - s'
    /// 3. g*a = g*b from [verify]
    /// 4. g*(a - b) = g *(s - s') = 0 from [2]
    /// 5. s = s' if g != 0.

    #[test]
    fn groebner_ex3() {
        let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(private s: F, private s': F, public g: G) where s == s {
            let r = random<F>;
            let a = r + s;
            let b = r + s';
            c <- g * a;
            d <- g * b;
            verify(c == d)
        }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        gs.write_pdf("groebner_ex3").unwrap_or_else(|e| {
            debug!(
                "Error writing to PDF, maybe [dot] is not installed? \n\n {}",
                e
            );
        });

        let g = QualifierPropagation::from_dag(&gs[0]);

        // Uniformity propagation
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        // Create an object computing the Groebner basis
        let mut kz = KnowledgeAnalysis::from_input(&g);

        assert!(kz.run().is_err());
    }

    #[test]
    fn schnorr_zk() {
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
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_ok(),
            "Schnorr protocol should be zero-knowledge"
        );
    }

    #[test]
    fn zk_regression_direct_secret_leak() {
        let ex = r#"
        proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            d <- x;
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
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        let result = kz.run();
        if let Err(ref e) = result {
            eprintln!("Leak detected: {}", e);
        }
        assert!(
            result.is_err(),
            "d <- x directly leaks private x to transcript"
        );
    }

    /// Leak: transcript contains x + public_val (no blinding).
    /// Verifier computes x = d - y.
    #[test]
    fn zk_leak_unblinded_linear_combination() {
        let ex = r#"
        proto leak<F: Field>(private x: F, public y: F) where x == x {
            d <- x + y;
            verify(d == d)
        }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

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
        proto leak<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            c <- challenge<F*>;
            z <- x * c;
            verify(g*z == h*c)
        }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

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
        proto leak<F: Field>(private s: F, private t: F, public y: F) where y == y {
            a <- s + y;
            b <- t + y;
            verify(a == b)
        }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_err(),
            "a - b = s - t leaks relationship between secrets"
        );
    }

    /// NOT a leak: proper Schnorr with random blinding.
    /// Verifier cannot recover x from z = r + x*c (r is uniform mask).
    #[test]
    fn zk_safe_schnorr_with_blinding() {
        let ex = r#"
        proto safe<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
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
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_ok(),
            "Schnorr with proper blinding should be ZK"
        );
    }

    /// Leak: the two verify statements together leak private information.
    /// Each check is a trivial self-equality on a transcript value (`a == a` and `b == b`).
    /// Since `a = s + r` and `b = t + r` reuse the same blinding value `r`, publishing both
    /// values reveals `a - b = s - t`, so the transcript leaks information about the secrets.
    #[test]
    fn zk_multiple_verify_one_safe_one_subtle_leak() {
        let ex = r#"
        proto mixed<F: Field>(private s: F, private t: F, public y: F) where y == y {
            let r = random<F>;
            a <- s + r;
            b <- t + r;
            verify(a == a);
            verify(b == b)
        }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        assert!(
            kz.run().is_err(),
            "One safe and one leaking verify should fail knowledge analysis"
        );
    }

    /// Safe: both verify statements are properly blinded with independent random values.
    /// Each check uses a separate random blinding factor, so no private information leaks.
    #[test]
    fn zk_multiple_verify_both_safe() {
        let ex = r#"
        proto safe<F: Field>(private a: F, private b: F) where a == b {
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
        proto ke<F: Field, N: Size>(public a: Uni<F, N>) where a == a {
            r1 <- challenge<F>;
            let l = a(r1);
            verify(l == l)
        }"#;

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let m = UModule::from_str(ex).unwrap().concretize(&sizes).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        let mut kz = KnowledgeAnalysis::from_input(&g);
        // All inputs are public so nothing could leak; trivially ZK.
        assert!(
            kz.run().is_ok(),
            "public-only eval protocol should be ZK (no private secrets to leak)"
        );
    }

    #[test]
    fn knowledge_relation_basis_div_wit_cache_is_clean() {
        let ex = r#"
        proto clean_rel<F: Field>(
            private p: Poly<F, 1, 2>,
            public d: Poly<F, 1, 1>,
            public q: Poly<F, 1, 1>
        ) where q == p / d {
            let z = p / d;
            verify(z == q)
        }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let g = UniformityPropagation::from_dag(&g).annotate_dag(&g);

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
