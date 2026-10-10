use std::collections::HashMap;

use backend::ArkConfig;
use backend::op::HasOpFactory;
use share::Set;

use crate::backend::{GbBackendKind, GbBasis};
use crate::error::AnalysisError;
use crate::extractor::extract_locals;
use crate::frontend::{MonoOrder, Polynomial};
use crate::ideal::{Check, IdealBuilder, Substitution, is_division_witness};
use crate::{TransClos, Var};
use graph::{QDag, Ref};

/// Inputs to the Gröbner basis computation: the generating set (prover ∪
/// relation ∪ verifier-locals, after inlining) and the verifier
/// polynomials to reduce in `run()`.
///
/// Produced by [`CompletenessAnalysis::build_inputs`]; consumed by
/// [`CompletenessAnalysis::from_inputs`]. Splitting construction from GB
/// computation lets callers inspect pre-GB metrics before the expensive
/// step.
pub struct CompletenessInputs<F: ark_ff::PrimeField> {
    /// The generating set for the Gröbner basis (prover ∪ relation ∪
    /// verifier-locals). Every definition is substituted away, prover
    /// messages included, and so is every variable a generator pins down.
    pub generating_set: Vec<Polynomial<F>>,
    /// Verifier polynomials to reduce against the basis in `run()`, minus
    /// the verifier-locals' generators (members by construction).
    pub verifier: Vec<Polynomial<F>>,
    /// What each `verify` checks, over the verifier's own variables: its
    /// definitions are substituted, the prover messages are not. Unlike
    /// `verifier`, a check stays when the substitution discharges it, so it
    /// is what to report.
    pub checks: Vec<Check<F>>,
}

/// Perform a completeness analysis using Groebner bases.
/// This analysis checks if the relation is included in the implementation.
/// One shared namespace is used for prover, relation, and verifier.
pub struct CompletenessAnalysis<C: ArkConfig> {
    /// Gröbner basis of (prover ∪ relation ∪ verifier-locals) under grevlex.
    /// Computed in `from_inputs`.
    pub basis: GbBasis<C::F>,
    /// Verifier polynomials to reduce against `basis` in `run()`.
    pub verifier: Vec<Polynomial<C::F>>,
}

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    /// Build the inputs to the Gröbner basis computation: construct the
    /// prover, relation, and verifier ideals, substitute each one's
    /// definitions into it and the prover's into the verifier's, merge them
    /// into a single generating set, and substitute away every variable a
    /// generator pins down.
    ///
    /// This is the cheap phase — no GB computation. Call
    /// [`from_inputs`](Self::from_inputs) to compute the basis, or inspect
    /// the generating set for pre-GB metrics.
    pub fn build_inputs(dag: &QDag<C>) -> CompletenessInputs<C::F> {
        let mut builder = IdealBuilder::new();

        let prover_tc = TransClos::prover(dag);
        let mut prover_result = builder.build(prover_tc);

        let rel_result = builder.build(TransClos::relation(dag));
        prover_result.merge(&rel_result);

        // The prover's and the relation's definitions, the prover messages included.
        let prover_defs = prover_result.inline();

        let verifier_tc = TransClos::verifier(dag);
        let mut verifier_locals = extract_locals(&builder, &verifier_tc);
        verifier_locals.inline();

        let mut verifier_result = builder.build(verifier_tc);
        verifier_result.inline();

        // The verifier reads the prover messages as variables, which the
        // prover's definitions replace.
        let mut generating_set = prover_result.generating_set;
        generating_set.extend(
            verifier_locals
                .generating_set
                .iter()
                .map(|p| prover_defs.apply(p))
                .filter(|p| !p.is_zero()),
        );

        // Then every variable a generator pins down, such as an input the
        // `where` clause defines.
        let input_args: Set<Ref> = dag.input_args().into_iter().map(Ref::new).collect();
        let pins = pin(&mut generating_set, |x| input_args.contains(&x.reference));

        // verifier_locals keeps the `==` node under each `verify`, so its
        // encoding is already a generator; reducing it again is wasted work.
        let verifier = verifier_result
            .generating_set
            .iter()
            .filter(|p| !verifier_locals.generating_set.contains(p))
            .map(|p| pins.apply(&prover_defs.apply(p)))
            .filter(|p| !p.is_zero())
            .collect();

        CompletenessInputs {
            generating_set,
            verifier,
            checks: verifier_result.checks,
        }
    }

    /// Compute the Gröbner basis from pre-built inputs.
    ///
    /// This is the expensive phase — `compute_gb` may hang or take a long
    /// time. Call [`build_inputs`](Self::build_inputs) first if you need
    /// pre-GB metrics.
    pub fn from_inputs(inputs: CompletenessInputs<C::F>, backend: GbBackendKind) -> Self {
        let gb = backend.build::<C::F>();
        let basis = gb
            .compute_gb(inputs.generating_set, &MonoOrder::grevlex())
            .expect("GB backend should support grevlex");

        Self {
            basis,
            verifier: inputs.verifier,
        }
    }

    /// Reduces every verifier polynomial against the prover/relation Gröbner
    /// basis; a zero remainder means the verifier equation is implied by the
    /// prover's computation, i.e. the protocol is complete.
    ///
    /// # Errors
    /// Returns [`AnalysisError::UnitIdeal`] if the basis degenerated to the
    /// unit ideal, and [`AnalysisError::Incomplete`] with the non-zero
    /// remainder for the first verifier equation that is not derivable.
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

/// Substitute away every variable a generator pins down (see
/// [`pinned_var`]), drop that generator, and return the pins.
///
/// Each pass applies the pins so far to each generator in order. Passes
/// repeat until one pins nothing, since a pin can let an earlier generator
/// pin a variable: a division row that reads the quotient only as `f·q`
/// pins it once the relation pins `f := 1`. That last pass also leaves
/// every remaining generator resolved.
fn pin<F: ark_ff::Field>(
    generating_set: &mut Vec<Polynomial<F>>,
    is_input: impl Fn(&Var) -> bool,
) -> Substitution<F> {
    let mut pins = Substitution::default();
    loop {
        let mut pinned = false;
        generating_set.retain_mut(|p| {
            *p = pins.apply(p);
            let Some((x, value)) = pinned_var(p, &is_input) else {
                return !p.is_zero();
            };
            pins.insert(x, value)
                .expect("a generator the pins resolved mentions no pinned variable");
            pinned = true;
            false
        });
        if !pinned {
            return pins;
        }
    }
}

/// The variable `x` that `p = c·x + r` pins down, with `c` a nonzero constant
/// and `x` not in `r`, and its value `−r/c`.
///
/// Any `x` qualifies when `r` is constant. Otherwise a division witness
/// does, and an input does when `p` contains no division witness: a division
/// row whose dividend is linear in inputs then pins the quotient, and the
/// relation stays over the inputs. Ties go to the least `Var`.
fn pinned_var<F: ark_ff::Field>(
    p: &Polynomial<F>,
    is_input: impl Fn(&Var) -> bool,
) -> Option<(Var, Polynomial<F>)> {
    // The number of terms each variable occurs in.
    let mut occurrences: HashMap<&Var, usize> = HashMap::new();
    for m in p.terms.keys() {
        for (x, _) in m.0.iter() {
            *occurrences.entry(x).or_default() += 1;
        }
    }
    let has_witness = occurrences.keys().any(|x| is_division_witness(x));
    let qualifies = |x: &Var| match occurrences.len() {
        // `x` is the only variable, so `r` is constant.
        1 => true,
        _ if has_witness => is_division_witness(x),
        _ => is_input(x),
    };
    let (x, c) = p
        .terms
        .iter()
        .filter(|(m, _)| m.degree() == 1)
        .map(|(m, c)| (m.vars().remove(0), *c))
        .filter(|(x, _)| occurrences[x] == 1 && qualifies(x))
        .min_by(|(x, _), (y, _)| x.cmp(y))?;
    // −r/c = x − p/c
    let value = &Polynomial::var(&x) - &(p * &Polynomial::lit(&c.inverse()?));
    Some((x, value))
}

#[cfg(test)]
mod tests {
    use super::{CompletenessAnalysis, is_division_witness, pinned_var};
    use crate::QualifierPropagation;
    use crate::Var;
    use crate::backend::GbBackend;
    use crate::backend::GbBackendKind;
    use crate::error::AnalysisError;
    use crate::frontend::Polynomial;
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use graph::UDags;

    use share::Ctx;
    use share::unwrap;

    /// Test helper: build + compute in one call with the default backend.
    fn from_input(dag: &graph::QDag<ArkBls12_381>) -> CompletenessAnalysis<ArkBls12_381> {
        let inputs = CompletenessAnalysis::build_inputs(dag);
        CompletenessAnalysis::from_inputs(inputs, GbBackendKind::default())
    }

    /// The DAG of the first protocol in `ex`.
    fn dag_of(ex: &str) -> graph::QDag<ArkBls12_381> {
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        QualifierPropagation::from_dag(gs.protocols()[0])
    }

    /// The checks `build_inputs` records for the protocol `ex`, as `lhs == rhs`.
    fn checks_of(ex: &str) -> Vec<String> {
        CompletenessAnalysis::build_inputs(&dag_of(ex))
            .checks
            .iter()
            .map(|c| format!("{} == {}", c.lhs, c.rhs))
            .collect()
    }

    #[test]
    fn checks_keep_the_prover_messages() {
        // The substitution discharges this check, so `verifier` is empty, but
        // the check is still recorded, over the messages `u` and `z`.
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;
        assert_eq!(checks_of(ex), ["g*z == h*c + u"]);
    }

    #[test]
    fn checks_substitute_the_verifiers_definitions() {
        let ex = r#"
            proto defs<F: Field>(instance a: F, instance b: F) where a == b {
                let s = a + b;
                let t = b + a;
                verify(s == t)
            }"#;
        // Both sides are equal, and the check is still recorded.
        assert_eq!(checks_of(ex), ["b + a == b + a"]);
    }

    #[test]
    fn checks_record_each_conjunct_of_each_verify() {
        let ex = r#"
            proto conjuncts<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                u <- a * x;
                v <- b * y;
                verify(x == y && u == v);
                verify(u == x)
            }"#;
        assert_eq!(checks_of(ex), ["x == y", "u == v", "u == x"]);
    }

    #[test]
    fn checks_record_each_coefficient_slot() {
        let ex = r#"
            proto slots<F: Field>(instance p: Poly<F, 1, 1>, instance q: Poly<F, 1, 1>) where p == q {
                verify(p == q)
            }"#;
        assert_eq!(checks_of(ex), ["p[0] == q[0]", "p[1] == q[1]"]);
    }

    #[test]
    fn a_checked_message_is_checked_against_one() {
        // `b` is a prover message: the verifier checks it as sent, not the
        // `==` the prover computed it with.
        let ex = r#"
            proto message<F: Field>(instance x: F, instance y: F) where x == y {
                b <- x == y;
                verify(b)
            }"#;
        assert_eq!(checks_of(ex), ["b == 1"]);
    }

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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
        assert!(
            ca.run().is_ok(),
            "named-let partial-eval should be complete"
        );
    }

    #[test]
    fn materialized_partial_mle_eval_keeps_inferred_uni_shape() {
        let ex = r#"
            proto materialized_partial<F: Field>(instance vals: [F; 4]) where vals == vals {
                x <- challenge<F>;
                let q = eval(mle(vals), [x]);
                let z = q + poly([0, 0]);
                verify(z == z)
            }"#;

        let sizes = Ctx::new();
        let m = parse_and_concretize(ex, &sizes);
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = from_input(&g);
        assert!(
            ca.run().is_ok(),
            "materialized partial MLE eval consumed as Uni(1) should be complete"
        );
    }

    #[test]
    fn trans_clos_partial_mle_eval_boundary_is_mle() {
        let ex = r#"
            proto trans_clos_eval_shape<F: Field>(instance vals: [F; 4]) where vals == vals {
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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
            proto ifft_roundtrip<F: Field>(instance v: [F; 2]) where v == v {
                let p = interpolate(v);
                let u = eval(p);
                verify(u == v)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = from_input(&g);
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
                verify(vc == va + vb)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = from_input(&g);
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
            ) where u == u {
                let w = u + v;
                let pu = interpolate(u);
                let pv = interpolate(v);
                let pw = interpolate(w);
                verify(pw == pu + pv)
            }"#;
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
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

        let mut ca = from_input(&g);
        assert!(
            ca.run().is_ok(),
            "c = a*b, verify c == a*b should be complete"
        );
    }

    #[test]
    fn chained_prover_message_completeness() {
        // `w` and `v` are defined through earlier messages; all three must
        // still be substituted away.
        let ex = r#"
            proto chained<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                w <- u + u;
                v <- w + u;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*(z + z + z) == v + h*(c + c + c))
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let inputs = CompletenessAnalysis::build_inputs(&g);
        let leftover: Vec<_> = inputs
            .generating_set
            .iter()
            .chain(&inputs.verifier)
            .flat_map(|p| p.vars())
            .filter(|v| ["u", "w", "v"].contains(&v.name.as_str()))
            .collect();
        assert!(
            leftover.is_empty(),
            "prover messages should be substituted away, found {leftover:?}"
        );

        let mut ca =
            CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default());
        assert!(
            ca.run().is_ok(),
            "message defined via an earlier message should be complete"
        );
    }

    #[test]
    fn a_definition_that_reads_a_message_resolves_through_it() {
        // `z` reads the message `m`, whose definition reads the local `n`.
        // Resolved all the way down, `z` and `m + n` are the same polynomial,
        // so the substitution discharges the check.
        let ex = r#"
            proto through<F: Field>(instance a: F) where a == a {
                c <- challenge<F>;
                let n = a + c;
                m <- n * c;
                z <- m + n;
                verify(z == m + n)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let inputs = CompletenessAnalysis::build_inputs(&g);
        assert!(
            inputs.verifier.is_empty(),
            "left to reduce: {:?}",
            inputs.verifier
        );
    }

    #[test]
    fn chained_prover_message_incomplete() {
        let ex = r#"
            proto chained<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                w <- u + u;
                v <- w + u;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*(z + z + z) == v + h*c)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = from_input(&g);
        assert!(
            ca.run().is_err(),
            "3g*z == v + h*c does not hold for an honest prover"
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

        let mut ca = from_input(&g);
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

    /// `verify(check)` over `h` and `k`, which the `where` clause defines,
    /// `k` through `h`.
    fn defined_inputs(check: &str) -> String {
        format!(
            r#"
            proto defined<G: Group, F: Scalar<G>>(witness x: F, witness y: F, instance g: G, instance h: G, instance k: G) where h == g*x && k == h + g*y {{
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + (x + y)*c;
                verify({check})
            }}"#
        )
    }

    #[test]
    fn inputs_the_relation_defines_are_pinned() {
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(&defined_inputs("g*z == u + k*c")));
        let left: Vec<_> = inputs
            .generating_set
            .iter()
            .chain(&inputs.verifier)
            .flat_map(|p| p.vars())
            .filter(|v| ["h", "k"].contains(&v.name.as_str()))
            .collect();
        assert!(left.is_empty(), "{left:?}");

        let mut ca =
            CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default());
        let result = ca.run();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_wrong_check_over_pinned_inputs_stays_incomplete() {
        let result = from_input(&dag_of(&defined_inputs("g*z == u + h*c"))).run();
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    /// `verify(check)` after the opening quotient `(p − p(z)) / (f_one·X − z)`
    /// of `p(X) = a + bX`, which is `b` once the `where` clause fixes `f_one`
    /// to 1.
    fn opening(check: &str) -> String {
        format!(
            r#"
            proto opening<F: Field>(witness p: Uni<F, 1>, instance f_one: F) where f_one == 1 {{
                z <- challenge<F>;
                let q = (p - p(z)) / poly([-z, f_one]);
                t <- q(z);
                let pc = coef(p);
                b <- pc[1];
                verify({check})
            }}"#
        )
    }

    #[test]
    fn a_division_pins_its_witnesses_once_the_relation_fixes_the_leading_coefficient() {
        // The quotient appears only as `f_one·q` until a later generator pins
        // `f_one := 1`.
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(&opening("t == b")));
        let witnesses: Vec<_> = inputs
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .filter(is_division_witness)
            .collect();
        assert!(witnesses.is_empty(), "{witnesses:?}");

        let mut ca =
            CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default());
        let result = ca.run();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_wrong_check_over_a_pinned_quotient_stays_incomplete() {
        let result = from_input(&dag_of(&opening("t == b + 1"))).run();
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    #[test]
    fn a_division_row_pins_its_witness_and_leaves_the_input() {
        use crate::ideal::GB_GENERATED_NAME_PREFIX;
        use backend::ATyp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let var = |name: &str, node: usize| {
            Var::from_var(
                name,
                NodeIndex::new(node),
                ATyp::scalar(),
                Qualifier::Instance,
            )
        };
        let witness = |i: usize| var(&format!("{GB_GENERATED_NAME_PREFIX}div_q::{i}"), 10 + i);
        let (p1, z, f, q0, q1) = (
            var("p1", 0),
            var("z", 1),
            var("f", 2),
            witness(0),
            witness(1),
        );
        let v = |x: &Var| Polynomial::<ark_bls12_381::Fr>::var(x);
        let is_input = |x: &Var| [&p1, &f].contains(&x);

        // The row of `(p − p(z)) / (X − z)` at `X^1`, in which the input
        // `p1` and the quotient's `q0` both occur only linearly.
        let row = v(&p1) + v(&z) * v(&q1) - v(&q0);
        assert_eq!(
            pinned_var(&row, is_input),
            Some((q0.clone(), v(&p1) + v(&z) * v(&q1)))
        );
        // The same row divided by `f·X − z`, before `f` is pinned.
        let row = v(&p1) + v(&z) * v(&q1) - v(&f) * v(&q0);
        assert_eq!(pinned_var(&row, is_input), None);
    }
}
