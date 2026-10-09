use std::collections::{BTreeMap, BTreeSet, HashMap};

use ark_ff::PrimeField;
use share::Ctx;

use crate::Var;
use crate::backend::{GbBasis, reduce_with_divisors};
use crate::frontend::Polynomial;
use crate::ideal::Check;

/// What each `verify` checks, and the prover messages to substitute into the
/// checks to explain why they hold.
#[derive(Clone)]
pub struct VerifierChecks<F: PrimeField> {
    /// What each `verify` checks, over the verifier's own variables: its
    /// definitions are substituted, the prover messages are not. A check
    /// stays when the substitution discharges it, so it is what to report.
    pub checks: Vec<Check<F>>,
    /// The prover messages: `t <- f` for each message `t`.
    pub messages: Ctx<Var, Polynomial<F>>,
}

/// Polynomials longer than this many terms are explained by their size only,
/// except for the checks themselves.
const EXPLAIN_MAX_TERMS: usize = 16;

/// What [`VerifierChecks::explain`] shows for one check.
struct CheckExplanation<F: PrimeField> {
    check: Check<F>,
    /// The prover messages the check mentions.
    messages: Vec<(Var, Polynomial<F>)>,
    /// Both sides after substitution.
    lhs: Polynomial<F>,
    rhs: Polynomial<F>,
    /// When the sides differ: the remainder of their difference against the
    /// basis, and the basis polynomials the reduction divided by.
    reduction: Option<(Polynomial<F>, Vec<Polynomial<F>>)>,
}

impl<F: PrimeField> CheckExplanation<F> {
    /// Every variable the explanation prints.
    fn vars(&self) -> impl Iterator<Item = Var> + '_ {
        let mut polys = vec![&self.check.lhs, &self.check.rhs];
        polys.extend(self.messages.iter().map(|(_, value)| value));
        if let Some((remainder, used)) = &self.reduction {
            polys.push(remainder);
            polys.extend(used);
        }
        self.messages
            .iter()
            .map(|(t, _)| t.clone())
            .chain(polys.into_iter().flat_map(|p| p.vars()))
    }

    fn render(&self, names: &HashMap<Var, Var>) -> String {
        let full = |p: &Polynomial<F>| {
            p.remap_vars(&|v| names.get(v).unwrap_or(v).clone())
                .to_string()
        };
        let show = |p: &Polynomial<F>| {
            if p.terms.len() > EXPLAIN_MAX_TERMS {
                format!("<{} terms>", p.terms.len())
            } else {
                full(p)
            }
        };
        let name = |x: &Var| names.get(x).unwrap_or(x).to_string();
        // The check itself in full: it is what the verifier writes.
        let mut out = format!(
            "check: {} == {}\n",
            full(&self.check.lhs),
            full(&self.check.rhs)
        );
        for (t, value) in &self.messages {
            out += &format!("  {} <- {}\n", name(t), show(value));
        }
        match &self.reduction {
            None => out += &format!("  both sides: {}\n", show(&self.lhs)),
            Some((remainder, used)) => {
                out += &format!("  lhs: {}\n  rhs: {}\n", show(&self.lhs), show(&self.rhs));
                if remainder.is_zero() {
                    out += "  equal modulo the basis, using:\n";
                    for g in used {
                        out += &format!("    {}\n", show(g));
                    }
                } else {
                    out += &format!("  differ by {} modulo the basis\n", show(remainder));
                }
            }
        }
        out
    }
}

/// Distinct variables that print alike, such as a challenge drawn at every
/// level of a recursion, get `#1`, `#2`, … in `Var` order, which follows the
/// order the graph creates them in.
fn disambiguate(vars: impl IntoIterator<Item = Var>) -> HashMap<Var, Var> {
    let mut by_name: BTreeMap<String, BTreeSet<Var>> = BTreeMap::new();
    for v in vars {
        by_name.entry(v.to_string()).or_default().insert(v);
    }
    let mut names = HashMap::new();
    for group in by_name.into_values().filter(|group| group.len() > 1) {
        for (k, v) in group.into_iter().enumerate() {
            let mut named = v.clone();
            named.name = format!("{}#{}", v.name, k + 1);
            names.insert(v, named);
        }
    }
    names
}

impl<F: PrimeField> VerifierChecks<F> {
    /// Explain why each check holds modulo `basis`, one block per check,
    /// sorted:
    ///
    /// ```text
    /// check: g*z == h*c + u
    ///   u <- g*r
    ///   z <- x*c + r
    ///   lhs: g*x*c + g*r
    ///   rhs: h*c + g*r
    ///   equal modulo the basis, using:
    ///     g*x - h
    /// ```
    ///
    /// The check is shown as the verifier writes it, followed by the prover
    /// messages substituted into it, `t <- …`. If both sides then agree, the
    /// substitution alone discharged the check. Otherwise the basis has to
    /// prove the rest, and the explanation lists the basis polynomials that
    /// reduce their difference to 0, or the remainder if it is not 0.
    /// Polynomials other than the checks that are longer than
    /// [`EXPLAIN_MAX_TERMS`] are shown by their number of terms, and variables
    /// that print alike are told apart as in [`disambiguate`].
    pub fn explain(&self, basis: &GbBasis<F>) -> String {
        let explanations: Vec<_> = self
            .checks
            .iter()
            .map(|c| self.explain_check(c, basis))
            .collect();
        let names = disambiguate(explanations.iter().flat_map(CheckExplanation::vars));
        let mut blocks: Vec<String> = explanations.iter().map(|e| e.render(&names)).collect();
        blocks.sort();
        blocks.concat()
    }

    fn explain_check(&self, check: &Check<F>, basis: &GbBasis<F>) -> CheckExplanation<F> {
        let messages = self
            .messages
            .iter()
            .filter(|(t, _)| check.lhs.contains(t) || check.rhs.contains(t))
            .map(|(t, value)| (t.clone(), value.clone()))
            .collect();
        let lhs = check.lhs.clone().inline_vars(&self.messages).0;
        let rhs = check.rhs.clone().inline_vars(&self.messages).0;
        let difference = &lhs - &rhs;
        let reduction = (!difference.is_zero()).then(|| {
            let (remainder, divisors) =
                reduce_with_divisors(difference, &basis.polys, &basis.order);
            let used = divisors
                .into_iter()
                .map(|i| basis.polys[i].clone())
                .collect();
            (remainder, used)
        });
        CheckExplanation {
            check: check.clone(),
            messages,
            lhs,
            rhs,
            reduction,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::CompletenessAnalysis;
    use crate::GbBackendKind;
    use crate::QualifierPropagation;
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use graph::UDags;

    use share::Ctx;
    use share::unwrap;

    /// Runs the completeness analysis of the first protocol in `ex` and
    /// returns the explanation of its checks, and whether `run()` passed.
    fn explain(ex: &str) -> (String, bool) {
        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(gs.protocols()[0]);
        let inputs = CompletenessAnalysis::build_inputs(&g);
        let checks = inputs.checks.clone();
        let mut ca =
            CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default());
        let complete = ca.run().is_ok();
        (checks.explain(&ca.basis), complete)
    }

    #[test]
    fn explain_shows_the_messages_that_discharge_a_check() {
        let ex = r#"
            proto simple<F: Field>(instance a: F, instance b: F) where a == a {
                c <- a * b;
                verify(c == a * b)
            }"#;
        let (explanation, complete) = explain(ex);
        assert!(complete);
        assert_eq!(
            explanation,
            "check: c == a*b\n  c <- a*b\n  both sides: a*b\n"
        );
    }

    #[test]
    fn explain_shows_the_basis_polynomials_that_discharge_a_check() {
        let ex = r#"
            proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g*x {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + x*c;
                verify(g*z == u + h*c)
            }"#;
        let (explanation, complete) = explain(ex);
        assert!(complete);
        assert_eq!(
            explanation,
            "check: g*z == h*c + u\n  u <- g*r\n  z <- x*c + r\n  lhs: g*x*c + g*r\n  \
             rhs: h*c + g*r\n  equal modulo the basis, using:\n    g*x - h\n"
        );
    }

    #[test]
    fn explain_shows_what_is_left_of_an_incomplete_check() {
        let ex = r#"
            proto defined<G: Group, F: Scalar<G>>(
                witness x: F, witness y: F, instance g: G, instance h: G, instance k: G,
            ) where h == g*x && k == h + g*y {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + (x + y)*c;
                verify(g*z == u + h*c)
            }"#;
        let (explanation, complete) = explain(ex);
        assert!(!complete, "g*z == u + h*c misses the g*y*c term");
        assert!(
            explanation.contains("differ by k*c - h*c modulo the basis"),
            "the missing g*y*c term should be named:\n{explanation}"
        );
    }

    #[test]
    fn explain_numbers_variables_that_print_alike() {
        // Each call to `round` sends its own `v` and `t` and draws its own `c`.
        let ex = r#"
            fn round<F: Field>(witness w: F) -> Unit {
                v <- w;
                c <- challenge<F>;
                t <- w * c;
                verify(t == v * c)
            }
            proto twice<F: Field>(witness a: F, witness b: F) where a == b {
                round(a);
                round(b)
            }"#;
        let (explanation, complete) = explain(ex);
        assert!(complete);
        assert_eq!(
            explanation,
            "check: t#1 == v#1*c#1\n  v#1 <- a\n  t#1 <- a*c#1\n  both sides: a*c#1\n\
             check: t#2 == v#2*c#2\n  v#2 <- b\n  t#2 <- b*c#2\n  both sides: b*c#2\n"
        );
    }
}
