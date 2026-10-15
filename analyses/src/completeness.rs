use std::collections::HashSet;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, ArkScalarOps};
use share::Set;

use crate::backend::{GbBackendKind, GbBasis};
use crate::error::AnalysisError;
use crate::frontend::{MonoOrder, Polynomial};
use crate::ideal::{Check, IdealBuilder, Substitution};
use crate::{TransClos, Var};
use graph::{QDag, Ref};

/// Inputs to the Gröbner basis computation: the generating set (prover ∪
/// relation ∪ verifier-locals, definitions substituted) and the verifier's
/// goals to reduce in `run()`.
///
/// Produced by [`CompletenessAnalysis::build_inputs`]; consumed by
/// [`CompletenessAnalysis::try_from_inputs`]. Splitting construction from GB
/// computation lets callers inspect pre-GB metrics before the expensive
/// step.
pub struct CompletenessInputs<F: ark_ff::PrimeField> {
    /// The generating set for the Gröbner basis (prover ∪ relation ∪
    /// verifier-locals). Every definition is substituted away, prover
    /// messages included, and so is every variable a generator solves for.
    pub generating_set: Vec<Polynomial<F>>,
    /// The goals to reduce against the basis in `run()`: what each `verify`
    /// asserts, and that every divisor of the prover and the verifier is
    /// nonzero. A goal that is already a verifier generator is left out.
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
    /// Computed in `try_from_inputs`.
    pub basis: GbBasis<C::F>,
    /// Goals to reduce against `basis` in `run()`.
    pub verifier: Vec<Polynomial<C::F>>,
}

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    /// Build the inputs to the Gröbner basis computation, in stages: the
    /// prover and the relation with their definitions substituted; the
    /// verifier, whose locals are generators and whose checks are the goals,
    /// with its own definitions and then the prover's substituted; and then
    /// every variable a generator solves for, substituted away.
    ///
    /// This is the cheap phase — no GB computation. Call
    /// [`try_from_inputs`](Self::try_from_inputs) to compute the basis, or inspect
    /// the generating set for pre-GB metrics.
    pub fn build_inputs(dag: &QDag<C>) -> CompletenessInputs<C::F> {
        let mut builder = IdealBuilder::new();

        // The prover and the relation, with their definitions substituted,
        // the prover messages included. The relation's divisor checks are
        // part of the relation.
        let mut prover = builder.build(TransClos::prover(dag));
        let mut relation = builder.build(TransClos::relation(dag));
        relation.generating_set.append(&mut relation.check_polys);
        prover.merge(&relation);
        let defs = prover.substitute_definitions();

        // The verifier, with its own definitions substituted. Its checks are
        // the goals; a goal that is already one of its generators holds by
        // construction.
        let mut verifier = builder.build(TransClos::verifier(dag));
        verifier.substitute_definitions();
        verifier
            .check_polys
            .retain(|g| !verifier.generating_set.contains(g));

        // The verifier reads the prover messages as variables, which the
        // prover's definitions replace.
        for p in verifier
            .generating_set
            .iter_mut()
            .chain(&mut verifier.check_polys)
            .chain(&mut verifier.divisors)
        {
            *p = defs.apply(p);
        }

        // Then every variable a generator solves for, such as an input the
        // `where` clause defines. The generators are resolved by `defs`, as
        // `solve` requires, and `defs` is not resolved against the result:
        // a goal takes `defs`, then `solved`.
        let inputs: HashSet<Ref> = dag.input_args().into_iter().map(Ref::new).collect();
        let witnesses: HashSet<Ref> = prover
            .division_witnesses
            .union(&verifier.division_witnesses)
            .copied()
            .collect();
        let mut generating_set = prover.generating_set;
        generating_set.extend(verifier.generating_set.into_iter().filter(|p| !p.is_zero()));
        let solved = Substitution::solve(&mut generating_set, |p, x| {
            completeness_accepts(p, x, &inputs, &witnesses)
        });

        // A checked divisor that mentions a sample makes its exclusion a
        // generator: `t·p − 1` for what the exclusion makes nonzero, `p`, and
        // a fresh `t`. Unmentioned ones would only slow the basis. The samples
        // are the prover's and the relation's: the verifier reads its
        // challenges as inputs.
        let mentioned: Set<Var> = prover
            .divisors
            .iter()
            .chain(&verifier.divisors)
            .flat_map(|d| solved.apply(d).vars())
            .collect();
        let one = Polynomial::lit(&C::FOps::one());
        for (sample, nonzero) in &prover.excluded {
            if mentioned.contains(sample) {
                let name = builder.ns.next_name("excluded_inv");
                let t = Polynomial::var(&builder.ns.sentinel_var(&name, ATyp::scalar()));
                generating_set.push(&(&t * &solved.apply(nonzero)) - &one);
            }
        }

        // The goals: the verifier's checks and the prover's divisor checks.
        let goals = prover
            .check_polys
            .iter()
            .chain(&verifier.check_polys)
            .map(|g| solved.apply(g))
            .filter(|g| !g.is_zero())
            .collect();

        CompletenessInputs {
            generating_set,
            verifier: goals,
            checks: verifier.checks,
        }
    }

    /// Compute the basis, propagating backend failures.
    ///
    /// # Errors
    /// Returns an error when the selected backend fails.
    #[allow(clippy::result_large_err)]
    pub fn try_from_inputs(
        inputs: CompletenessInputs<C::F>,
        backend: GbBackendKind,
    ) -> Result<Self, AnalysisError<C>> {
        let gb = backend.build::<C::F>();
        let basis = gb.compute_gb(inputs.generating_set, &MonoOrder::grevlex())?;

        Ok(Self {
            basis,
            verifier: inputs.verifier,
        })
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

/// Whether completeness may solve `p` for `x`.
///
/// Every `x` that [`Substitution::solve`] offers gives an exact substitution,
/// so this rule decides only which variables reach the Gröbner basis, and with
/// them its size. It accepts:
///
/// - any `x` that is `p`'s only variable, such as `f_one := 1` from
///   `where f_one == 1`;
/// - a division witness when `p` reads one: the row `p1 + z·q1 − q0` of
///   `(p − p(z)) / (X − z)` solves for the quotient `q0`, not the input `p1`,
///   which removes the variable the division introduced;
/// - otherwise an input, such as `h := g·x` from `where h == g*x`, which turns
///   a check written over `h` into an identity in the witness `x`.
///
/// Challenges, prover messages and random values are never solved for:
/// eliminating them is exact too, but leaves larger goals and bases.
fn completeness_accepts<F: ark_ff::Field>(
    p: &Polynomial<F>,
    x: &Var,
    inputs: &HashSet<Ref>,
    witnesses: &HashSet<Ref>,
) -> bool {
    let vars = || p.terms.keys().flat_map(|m| m.0.iter().map(|(y, _)| y));
    if vars().all(|y| y == x) {
        return true;
    }
    if vars().any(|y| witnesses.contains(&y.reference)) {
        witnesses.contains(&x.reference)
    } else {
        inputs.contains(&x.reference)
    }
}

#[cfg(test)]
mod tests {
    use super::{CompletenessAnalysis, completeness_accepts};
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
        CompletenessAnalysis::try_from_inputs(inputs, GbBackendKind::default()).unwrap()
    }

    /// The DAG of the first protocol in `ex`.
    fn dag_of(ex: &str) -> graph::QDag<ArkBls12_381> {
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        QualifierPropagation::from_dag(gs.protocols()[0])
    }

    /// Completeness of the first protocol in `ex`.
    fn completeness_of(ex: &str) -> Result<(), AnalysisError<ArkBls12_381>> {
        from_input(&dag_of(ex)).run()
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
        // The relation makes `d[0]`, and so `d`, nonzero; the identity and
        // remainder bound then determine the quotient as `p`.
        let ex = r#"
            proto poly_div_exact<F: Field>(
                instance p: Poly<F, 1, 1>,
                instance d0: F,
                instance d1: F,
                witness w: F
            ) where d0 * w == 1 {
                let d = poly([d0, d1]);
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
            "(p*d)/d == p should be complete for a nonzero d"
        );
    }

    #[test]
    fn poly_div_by_a_divisor_that_may_be_zero_is_incomplete() {
        // The relation admits `d = 0`, where the check holds (the quotient is
        // 0) but the verifier divides by zero.
        let ex = r#"
            proto poly_div_zero<F: Field>(
                instance p: Poly<F, 1, 1>,
                instance d: Poly<F, 1, 1>
            ) where p == p {
                let prod = p * d;
                let q = prod / d;
                verify(q * d == prod)
            }"#;
        let result = completeness_of(ex);
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    #[test]
    fn poly_divmod_identity_completeness() {
        let ex = r#"
            proto poly_divmod<F: Field>(
                instance p: Poly<F, 1, 2>,
                instance d0: F,
                instance d1: F,
                witness w: F
            ) where d0 * w == 1 {
                let d = poly([d0, d1]);
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
                instance d0: F,
                witness w: F
            ) where d0 * w == 1 {
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
        //
        // The relation makes the divisor nonzero, isolating the `r[0]` goal.
        let ex = r#"
            proto poly_div_mid_zero<F: Field>(
                instance p: Poly<F, 1, 3>,
                instance b0: F,
                instance b2: F,
                witness w: F
            ) where b0 * w == 1 {
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
            CompletenessAnalysis::<ArkBls12_381>::try_from_inputs(inputs, GbBackendKind::default())
                .unwrap();
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
    fn inputs_the_relation_defines_are_solved_for() {
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
            CompletenessAnalysis::<ArkBls12_381>::try_from_inputs(inputs, GbBackendKind::default())
                .unwrap();
        let result = ca.run();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_wrong_check_over_solved_inputs_stays_incomplete() {
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
    fn a_division_solves_for_its_witnesses_once_the_relation_fixes_the_leading_coefficient() {
        // The quotient appears only as `f_one·q` until a later generator
        // defines `f_one := 1`.
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(&opening("t == b")));
        let prefix = crate::ideal::GB_GENERATED_NAME_PREFIX;
        let witnesses: Vec<_> = inputs
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .filter(|x| {
                ["div_q::", "div_r::"]
                    .iter()
                    .any(|key| x.name.starts_with(&format!("{prefix}{key}")))
            })
            .collect();
        assert!(witnesses.is_empty(), "{witnesses:?}");

        let mut ca =
            CompletenessAnalysis::<ArkBls12_381>::try_from_inputs(inputs, GbBackendKind::default())
                .unwrap();
        let result = ca.run();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_wrong_check_over_a_solved_quotient_stays_incomplete() {
        let result = from_input(&dag_of(&opening("t == b + 1"))).run();
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    /// `verify(check)` over the quotient `c / b`, which is `a` once the
    /// `where` clause defines `c` as `a·b` with `b` nonzero.
    fn quotient(check: &str) -> String {
        format!(
            r#"
            proto quotient<F: Field>(witness a: F, instance b: F, instance c: F, witness b_inv: F) where c == a * b && b * b_inv == 1 {{
                t <- a;
                verify({check})
            }}"#
        )
    }

    #[test]
    fn a_check_over_a_quotient_by_a_nonzero_scalar_is_complete() {
        let result = completeness_of(&quotient("c / b == t"));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_wrong_check_over_a_quotient_by_a_scalar_stays_incomplete() {
        let result = completeness_of(&quotient("c / b == t + 1"));
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    /// A verifier that divides by `c <- challenge<{typ}>`. Its check holds
    /// even at `c = 0`, where the quotient is 0, so only the divisor's check
    /// can fail.
    fn by_challenge(typ: &str) -> String {
        format!(
            r#"
            proto by_challenge<F: Field>(instance a: F) where a == a {{
                c <- challenge<{typ}>;
                let t = a / c;
                verify(t * c * c == a * c)
            }}"#
        )
    }

    #[test]
    fn a_quotient_by_a_challenge_is_incomplete() {
        let result = completeness_of(&by_challenge("F"));
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    #[test]
    fn a_quotient_by_a_nonzero_challenge_is_complete() {
        let result = completeness_of(&by_challenge("F*"));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_divisor_that_vanishes_at_one_challenge_is_incomplete() {
        // `c − 1` is zero at `c = 1`, although `c` is nonzero.
        let result = completeness_of(
            r#"
            proto at_one<F: Field>(instance a: F) where a == a {
                c <- challenge<F*>;
                let t = (c * c - 1) / (c - 1);
                verify(t * (c - 1) == c * c - 1)
            }"#,
        );
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    /// A verifier that divides by `(c − a)(c − 1)` for a `challenge<{typ}>`.
    fn excluding(typ: &str) -> String {
        format!(
            r#"
            proto excluding<F: Field>(instance a: F) where a == a {{
                c <- challenge<{typ}>;
                let t = 1 / ((c - a) * (c - 1));
                verify(t * (c - a) * (c - 1) == 1)
            }}"#
        )
    }

    #[test]
    fn a_challenge_excluding_every_root_of_the_divisor_is_complete() {
        let result = completeness_of(&excluding("F - [a, 1]"));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_challenge_excluding_some_roots_of_the_divisor_is_incomplete() {
        let result = completeness_of(&excluding("F - [a]"));
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    #[test]
    fn a_divisor_mixing_exclusions_is_complete() {
        // `c·(d − 1)` is not a monomial, so `c`'s exclusion is needed too.
        let result = completeness_of(
            r#"
            proto mixed<F: Field>(instance a: F) where a == a {
                c <- challenge<F*>;
                d <- challenge<F - [1]>;
                let t = 1 / (c * (d - 1));
                verify(t * c * (d - 1) == 1)
            }"#,
        );
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn an_exclusion_no_divisor_mentions_is_no_generator() {
        let generators = |typ: &str| {
            CompletenessAnalysis::build_inputs(&dag_of(&format!(
                r#"
                proto unused<F: Field>(instance a: F) where a == a {{
                    c <- challenge<{typ}>;
                    d <- challenge<F - [1]>;
                    let t = 1 / (d - 1);
                    verify(t * (d - 1) == c - c + 1)
                }}"#
            )))
            .generating_set
            .len()
        };
        assert_eq!(generators("F - [a]"), generators("F"));
    }

    /// A verifier that divides by `c − w`, for a fourth root of unity `w` and
    /// a `challenge<{typ}>`.
    fn off_the_roots(typ: &str) -> String {
        format!(
            r#"
            proto off_the_roots<F: Field>(instance w: F) where w ^ 4 == 1 {{
                c <- challenge<{typ}>;
                let t = 1 / (c - w);
                verify(t * (c - w) == 1)
            }}"#
        )
    }

    #[test]
    fn a_challenge_off_the_fourth_roots_of_unity_is_complete() {
        let result = completeness_of(&off_the_roots("F - roots_of_unity(4)"));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_challenge_off_fewer_roots_of_unity_is_incomplete() {
        // `w` may be a primitive fourth root, which `c` may equal.
        let result = completeness_of(&off_the_roots("F - roots_of_unity(2)"));
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    /// A prover that divides by its own `random<{typ}>`. The check holds even
    /// at `r = 0`, so only the divisor's check can fail.
    fn prover_division(typ: &str) -> String {
        format!(
            r#"
            proto prover_division<F: Field>(witness x: F, instance y: F) where y == x {{
                let r = random<{typ}>;
                m <- x / r;
                s <- r;
                verify(m * s * s == y * s)
            }}"#
        )
    }

    #[test]
    fn a_prover_that_may_divide_by_zero_is_incomplete() {
        let result = completeness_of(&prover_division("F"));
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    #[test]
    fn a_prover_that_divides_by_a_nonzero_random_is_complete() {
        let result = completeness_of(&prover_division("F*"));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_prover_that_divides_by_a_random_excluding_zero_is_complete() {
        let result = completeness_of(&prover_division("F - [0]"));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_division_in_the_relation_makes_its_divisor_nonzero() {
        // The relation holds only for `z ≠ 0`, so `y·z` is `x`.
        let result = completeness_of(
            r#"
            proto relation_division<F: Field>(witness x: F, instance z: F, instance y: F) where y == x / z {
                t <- x;
                verify(t == y * z)
            }"#,
        );
        assert!(result.is_ok(), "{result:?}");
    }

    /// `verify(check)` with the group identity written `0 * g`, which folds to a constant.
    fn identity(check: &str) -> String {
        format!(
            r#"
            proto identity<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {{
                t <- g * x;
                let zero = 0 * g;
                verify({check})
            }}"#
        )
    }

    #[test]
    fn a_check_against_the_group_identity_is_complete() {
        let result = from_input(&dag_of(&identity("zero - t + h == zero"))).run();
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn a_wrong_check_against_the_group_identity_stays_incomplete() {
        let result = from_input(&dag_of(&identity("zero + t == zero"))).run();
        assert!(
            matches!(result, Err(AnalysisError::Incomplete(_))),
            "{result:?}"
        );
    }

    #[test]
    fn a_division_row_solves_for_its_witness_and_leaves_the_input() {
        use backend::ATyp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;
        use std::collections::HashSet;

        let var = |name: &str, node: usize| {
            Var::from_var(
                name,
                NodeIndex::new(node),
                ATyp::scalar(),
                Qualifier::Instance,
            )
        };
        let (p1, z, f, q0, q1) = (
            var("p1", 0),
            var("z", 1),
            var("f", 2),
            var("q0", 3),
            var("q1", 4),
        );
        let v = |x: &Var| Polynomial::<ark_bls12_381::Fr>::var(x);
        let inputs = HashSet::from([p1.reference, f.reference]);
        let witnesses = HashSet::from([q0.reference, q1.reference]);

        let solve = |row: &Polynomial<ark_bls12_381::Fr>| {
            let mut generators = vec![row.clone()];
            let solved = crate::ideal::Substitution::solve(&mut generators, |p, x| {
                completeness_accepts(p, x, &inputs, &witnesses)
            });
            (solved, generators)
        };

        // The row of `(p − p(z)) / (X − z)` at `X^1`, in which the input
        // `p1` and the quotient's `q0` both occur only linearly: the quotient
        // is solved for, and the input stays.
        let (solved, left) = solve(&(v(&p1) + v(&z) * v(&q1) - v(&q0)));
        assert!(left.is_empty(), "{left:?}");
        assert_eq!(solved.apply(&v(&q0)), v(&p1) + v(&z) * v(&q1));
        assert_eq!(solved.apply(&v(&p1)), v(&p1));
        // The same row divided by `f·X − z`, before `f` is defined: nothing.
        let row = v(&p1) + v(&z) * v(&q1) - v(&f) * v(&q0);
        let (solved, left) = solve(&row);
        assert_eq!(left, [row]);
        assert_eq!(solved.apply(&v(&q0)), v(&q0));
    }
}
