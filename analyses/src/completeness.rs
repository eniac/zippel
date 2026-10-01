use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use ark_ff::PrimeField;
use backend::ArkConfig;
use backend::op::{GOp, HasOpFactory};
use share::{Ctx, Set};

use crate::TransClos;
use crate::Var;
use crate::backend::{GbBackendKind, GbBasis, reduce_with_divisors};
use crate::error::AnalysisError;
use crate::extractor::extract_locals;
use crate::frontend::{MonoOrder, Polynomial};
use crate::ideal::{Check, EncodeOptions, Ideal, IdealBuilder, Origin, Stage};
use graph::Ref;
use graph::eval::collect_refs;
use graph::{Op, QDag};

/// Inputs to the Gröbner basis computation: the generating set (prover ∪
/// relation ∪ verifier-locals, after optional inlining) and the verifier
/// polynomials to reduce in `run()`.
///
/// Produced by [`CompletenessAnalysis::build_inputs`]; consumed by
/// [`CompletenessAnalysis::from_inputs`]. Splitting construction from GB
/// computation lets callers inspect pre-GB metrics before the expensive
/// step.
pub struct CompletenessInputs<F: ark_ff::PrimeField> {
    /// The generating set for the Gröbner basis (prover ∪ relation ∪
    /// verifier-locals). When inlining, every definition is substituted away,
    /// prover messages and inputs the relation pins down included.
    pub generating_set: Vec<Polynomial<F>>,
    /// Verifier polynomials to reduce against the basis in `run()`, minus
    /// those already in `generating_set` (members by construction).
    pub verifier: Vec<Polynomial<F>>,
    /// What each `verify` checks, over the verifier's own variables, before
    /// any substitution. Unlike `verifier`, it does not vanish when the
    /// substitution discharges a check, so it is what to report or snapshot.
    pub checks: Vec<Check<F>>,
    /// The prover messages substituted away, `t <- f`, each resolved down to
    /// non-message variables.
    pub messages: Ctx<Var, Polynomial<F>>,
    /// The variables a generator pinned down and that were substituted away
    /// after the messages, `x == f`: inputs the `where` clause defines, and
    /// asserted bools.
    pub pinned: Ctx<Var, Polynomial<F>>,
    /// Where each generator came from, index-aligned with `generating_set`, or
    /// empty if that was lost. Diagnostic only; see [`Self::describe`].
    pub origins: Vec<Origin>,
    /// How many `assert`s written in the protocol body (not the one wrapping
    /// the `where` clause) the prover and verifier closures reach.
    pub body_asserts: usize,
}

impl<F: PrimeField> CompletenessInputs<F> {
    /// The generating set grouped by where each generator came from, with each
    /// generator's degree, number of terms and number of variables, preceded by
    /// a summary. Polynomials longer than [`EXPLAIN_MAX_TERMS`] terms are shown
    /// by their size only.
    pub fn describe(&self) -> String {
        let vars: Set<Var> = self.generating_set.iter().flat_map(|p| p.vars()).collect();
        let max_degree = self
            .generating_set
            .iter()
            .map(Polynomial::degree)
            .max()
            .unwrap_or(0);
        let names = disambiguate(
            vars.iter()
                .cloned()
                .chain(self.pinned.keys())
                .chain(self.origins.iter().map(|o| o.node.clone())),
        );
        let name = |x: &Var| names.get(x).unwrap_or(x).to_string();
        let show = |p: &Polynomial<F>| {
            if p.terms.len() > EXPLAIN_MAX_TERMS {
                format!("<{} terms>", p.terms.len())
            } else {
                p.remap_vars(&|v| names.get(v).unwrap_or(v).clone())
                    .to_string()
            }
        };

        let mut out = format!(
            "generating set: {} polynomials, max degree {max_degree}, {} variables\n",
            self.generating_set.len(),
            vars.len()
        );
        out += &format!(
            "goals: {}, checks: {}, prover messages substituted: {}\n",
            self.verifier.len(),
            self.checks.len(),
            self.messages.len()
        );
        out += &format!(
            "body asserts reaching the analysis: {}\n",
            self.body_asserts
        );
        let mut pinned: Vec<(String, usize)> = self
            .pinned
            .iter()
            .map(|(x, value)| (name(x), value.terms.len()))
            .collect();
        pinned.sort();
        out += &format!("pinned and substituted away ({}):", pinned.len());
        for (x, terms) in &pinned {
            out += &format!(" {x} ({terms} terms)");
        }
        out += "\n";

        if self.origins.len() != self.generating_set.len() {
            out += "\n[origins lost]\n";
            for p in &self.generating_set {
                out += &format!("  {}  {}\n", stats(p), show(p));
            }
            return out;
        }
        let mut groups: BTreeMap<Stage, Vec<usize>> = BTreeMap::new();
        for (i, origin) in self.origins.iter().enumerate() {
            groups.entry(origin.stage).or_default().push(i);
        }
        for (stage, members) in groups {
            let degree = members
                .iter()
                .map(|&i| self.generating_set[i].degree())
                .max()
                .unwrap_or(0);
            out += &format!(
                "\n[{}] {} generators, max degree {degree}\n",
                stage_label(stage),
                members.len()
            );
            for i in members {
                let (p, origin) = (&self.generating_set[i], &self.origins[i]);
                out += &format!(
                    "  {}  from {} `{}`: {}\n",
                    stats(p),
                    origin.op,
                    name(&origin.node),
                    show(p)
                );
            }
        }
        out
    }
}

/// `deg D, T terms, V vars` for `p`.
fn stats<F: PrimeField>(p: &Polynomial<F>) -> String {
    format!(
        "deg {}, {} terms, {} vars",
        p.degree(),
        p.terms.len(),
        p.vars().len()
    )
}

fn stage_label(stage: Stage) -> String {
    match stage {
        Stage::Prover => "prover".to_string(),
        Stage::RelationAssert => "where: the assert around it".to_string(),
        Stage::Relation { conjunct: Some(k) } => format!("where: conjunct {k}"),
        Stage::Relation { conjunct: None } => "where: shared by several conjuncts".to_string(),
        Stage::VerifierLocal => "verifier local".to_string(),
        Stage::CheckBookkeeping => "check bookkeeping".to_string(),
        Stage::Unknown => "unattributed".to_string(),
    }
}

/// How many `assert` nodes `tc` contains.
fn count_asserts<C: ArkConfig>(tc: &TransClos<C>) -> usize {
    tc.clos
        .iter()
        .filter(|(_, op)| matches!(op, Op::Assert(_)))
        .count()
}

/// Attribute the generators of the relation ideal: those of the `assert`
/// wrapping the `where` clause to [`Stage::RelationAssert`], and every other one
/// to the top-level conjunct whose computation its node belongs to. `clos` is
/// the relation closure, already built by `builder`.
fn attribute_relation<C: ArkConfig + HasOpFactory>(
    builder: &IdealBuilder<C>,
    clos: &[(Var, GOp<C>)],
    ideal: &mut Ideal<C>,
) {
    let deps: HashMap<Ref, Vec<Ref>> = clos
        .iter()
        .map(|(v, op)| (v.reference, collect_refs(op)))
        .collect();
    let mut conjunct_of: HashMap<Ref, Option<usize>> = HashMap::new();
    let asserted = clos.iter().find_map(|(_, op)| match op {
        Op::Assert(exp) => Some(exp.clone()),
        _ => None,
    });
    if let Some(exp) = asserted {
        // The elements split out of one `reduce(&&, …)` form one conjunct.
        let mut numbered: HashMap<Ref, usize> = HashMap::new();
        let mut conjuncts = 0;
        for leaf in builder.collect_and_leaves(&exp) {
            let mut next = || {
                conjuncts += 1;
                conjuncts - 1
            };
            let k = match leaf.reduction {
                Some(r) => *numbered.entry(r).or_insert_with(next),
                None => next(),
            };
            let mut stack = leaf.refs();
            let mut seen = HashSet::new();
            while let Some(r) = stack.pop() {
                if !seen.insert(r) {
                    continue;
                }
                match conjunct_of.entry(r) {
                    Entry::Vacant(e) => {
                        e.insert(Some(k));
                    }
                    Entry::Occupied(mut e) => {
                        if *e.get() != Some(k) {
                            e.insert(None);
                        }
                    }
                }
                if let Some(ds) = deps.get(&r) {
                    stack.extend(ds.iter().copied());
                }
            }
        }
    }
    for origin in &mut ideal.origins {
        origin.stage = if origin.op == "assert" {
            Stage::RelationAssert
        } else {
            Stage::Relation {
                conjunct: conjunct_of.get(&origin.node.reference).copied().flatten(),
            }
        };
    }
}

/// Substitute `defs` into every generator, dropping those that vanish together
/// with their origins. `origins` ends up empty if it did not describe `polys`.
fn substitute_generators<F: PrimeField>(
    polys: Vec<Polynomial<F>>,
    origins: &mut Vec<Origin>,
    defs: &Ctx<Var, Polynomial<F>>,
) -> Vec<Polynomial<F>> {
    let aligned = origins.len() == polys.len();
    let mut old = std::mem::take(origins).into_iter();
    let mut out = Vec::with_capacity(polys.len());
    for p in polys {
        let origin = if aligned { old.next() } else { None };
        let p = p.inline_vars(defs).0;
        if !p.is_zero() {
            out.push(p);
            origins.extend(origin);
        }
    }
    out
}

/// Polynomials longer than this many terms are explained by their size only,
/// except for the checks themselves.
const EXPLAIN_MAX_TERMS: usize = 16;

/// What [`CompletenessAnalysis::explain`] shows for one check.
struct CheckExplanation<F: PrimeField> {
    check: Check<F>,
    /// The prover messages the check mentions.
    messages: Vec<(Var, Polynomial<F>)>,
    /// The pinned variables the check mentions once the messages are substituted.
    pinned: Vec<(Var, Polynomial<F>)>,
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
        let defs = self.messages.iter().chain(&self.pinned);
        let mut polys = vec![&self.check.lhs, &self.check.rhs];
        polys.extend(defs.clone().map(|(_, value)| value));
        if let Some((remainder, used)) = &self.reduction {
            polys.push(remainder);
            polys.extend(used);
        }
        defs.map(|(x, _)| x.clone())
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
        for (x, value) in &self.pinned {
            out += &format!("  {} == {}\n", name(x), show(value));
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

/// Substitute `defs` into every polynomial, dropping those that vanish.
fn substitute<F: PrimeField>(
    polys: Vec<Polynomial<F>>,
    defs: &Ctx<Var, Polynomial<F>>,
) -> Vec<Polynomial<F>> {
    polys
        .into_iter()
        .map(|p| p.inline_vars(defs).0)
        .filter(|p| !p.is_zero())
        .collect()
}

/// If `p` pins a variable down, i.e. `p = c·x + r` with `c` constant and
/// `x ∉ r`, return `x` and its value `−r/c`. Any `x` qualifies when `r` is
/// constant; otherwise `x` must satisfy `eligible`. Ties go to the least
/// `Var`, so the choice does not depend on hash order.
fn defined_var<F: PrimeField>(
    p: &Polynomial<F>,
    eligible: &impl Fn(&Var) -> bool,
) -> Option<(Var, Polynomial<F>)> {
    // The number of terms each variable occurs in.
    let mut occurrences: HashMap<Var, usize> = HashMap::new();
    for mono in p.terms.keys() {
        for v in mono.vars() {
            *occurrences.entry(v).or_default() += 1;
        }
    }
    let rest_constant = p.terms.keys().filter(|m| !m.is_constant()).count() == 1;
    let (x, c) = p
        .terms
        .iter()
        .filter(|(mono, _)| mono.degree() == 1)
        .filter_map(|(mono, c)| {
            let x = mono.vars().pop()?;
            (occurrences[&x] == 1 && (rest_constant || eligible(&x))).then_some((x, *c))
        })
        .min_by(|(a, _), (b, _)| a.cmp(b))?;
    // x = (c·x − p) / c
    let cx = &Polynomial::lit(&c) * &Polynomial::var(&x);
    let inv = Polynomial::lit(&c.inverse().expect("terms have nonzero coefficients"));
    Some((x, &(&cx - p) * &inv))
}

/// Substitute away every variable that a generator pins down (see
/// [`defined_var`]), in `generating_set` and `verifier` alike, and return
/// what each was pinned to.
///
/// These come from the `where` clause. Each asserted `a == b` arrives as the
/// bool encoding `d·β`, `Σ d·ι + β − 1`, `β − 1` with `d = a − b`: the last
/// pins `β := 1`, which turns the first into `d`, and `d` pins `a` whenever
/// `a` is an input that `b` does not mention. Left to Buchberger, the grevlex
/// leading term of `a − b` lies in `b`, so it rewrites `b`'s monomials instead
/// of eliminating `a` (Dory at S=3 does not finish). The substitution is exact
/// for the same reason as for prover messages.
fn eliminate_definitions<F: PrimeField>(
    generating_set: &mut Vec<Polynomial<F>>,
    origins: &mut Vec<Origin>,
    verifier: &mut Vec<Polynomial<F>>,
    eligible: impl Fn(&Var) -> bool,
) -> Ctx<Var, Polynomial<F>> {
    // Kept resolved: no value mentions a defined variable.
    let mut defs: Ctx<Var, Polynomial<F>> = Ctx::new();
    loop {
        let mut found = false;
        let mut kept = Vec::with_capacity(generating_set.len());
        let aligned = origins.len() == generating_set.len();
        let mut old_origins = std::mem::take(origins).into_iter();
        for p in std::mem::take(generating_set) {
            let origin = if aligned { old_origins.next() } else { None };
            let p = if p.vars().iter().any(|v| defs.contains(v)) {
                p.inline_vars(&defs).0
            } else {
                p
            };
            if p.is_zero() {
                continue;
            }
            match defined_var(&p, &eligible) {
                Some((x, value)) => {
                    let def = Ctx::singleton(x.clone(), value.clone());
                    defs.modify(|_, v| {
                        if v.contains(&x) {
                            *v = v.clone().inline_vars(&def).0;
                        }
                    });
                    defs.insert(&x, &value);
                    found = true;
                }
                None => {
                    kept.push(p);
                    origins.extend(origin);
                }
            }
        }
        *generating_set = kept;
        // A pass that defined nothing new left every generator resolved.
        if !found {
            break;
        }
    }
    *verifier = substitute(std::mem::take(verifier), &defs);
    defs
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
    /// What each `verify` checks; see [`CompletenessInputs::checks`].
    pub checks: Vec<Check<C::F>>,
    /// The prover messages substituted away; see [`CompletenessInputs::messages`].
    pub messages: Ctx<Var, Polynomial<C::F>>,
    /// The variables pinned down and substituted away; see
    /// [`CompletenessInputs::pinned`].
    pub pinned: Ctx<Var, Polynomial<C::F>>,
}

impl<C: HasOpFactory> CompletenessAnalysis<C> {
    /// Build the inputs to the Gröbner basis computation: construct the
    /// prover, relation, and verifier ideals, optionally inline the `pl`
    /// table, and merge them into a single generating set.
    ///
    /// When inlining, prover messages are substituted by their definitions
    /// too. Otherwise each message `t` stays in the basis as `f(…) − t`, and
    /// under grevlex its leading term is the top monomial of `f` rather than
    /// `t`, so Buchberger works on the whole polynomial map instead of
    /// substituting (hyrax_ipa does not finish). The substitution is exact:
    /// `t − f ∈ I` for every definition, so `p ∈ I` iff `p[t ↦ f]` lies in
    /// the ideal generated by the substituted generators.
    ///
    /// The same holds for an input the `where` clause defines, as in
    /// `x == f(…)` with `x ∉ f`, and those are substituted too (see
    /// [`eliminate_definitions`]).
    ///
    /// This is the cheap phase — no GB computation. Call
    /// [`from_inputs`](Self::from_inputs) to compute the basis, or inspect
    /// the generating set for pre-GB metrics.
    pub fn build_inputs(dag: &QDag<C>, inline: bool) -> CompletenessInputs<C::F> {
        let rel_tc = TransClos::relation(dag);
        let rel_clos = rel_tc.clos.clone();
        // The `assert` wrapping the `where` clause; any other is a runtime
        // check written in a protocol body.
        let relation_asserts = rel_clos
            .iter()
            .filter(|(_, op)| matches!(op, Op::Assert(_)))
            .map(|(v, _)| v.reference)
            .collect();
        let mut builder = IdealBuilder::with_options(EncodeOptions {
            split_reductions: true,
            relation_asserts: Some(relation_asserts),
        });

        let prover_tc = TransClos::prover(dag);
        let mut body_asserts = count_asserts(&prover_tc);
        let mut prover_result = builder.build(prover_tc);
        prover_result.set_stage(Stage::Prover);

        let mut rel_result = builder.build(rel_tc);
        attribute_relation(&builder, &rel_clos, &mut rel_result);
        prover_result.merge(&rel_result);

        let transcript_refs: Set<Ref> = dag.transcript_nodes().into_iter().map(Ref::new).collect();
        if inline {
            prover_result.inline(&transcript_refs);
        }

        let verifier_tc = TransClos::verifier(dag);
        body_asserts += count_asserts(&verifier_tc);
        let verified: Vec<_> = verifier_tc
            .clos
            .iter()
            .filter_map(|(_, op)| match op {
                Op::Verify(exp) => Some(exp.clone()),
                _ => None,
            })
            .collect();
        let mut verifier_locals = extract_locals(&builder, &verifier_tc);
        verifier_locals.set_stage(Stage::VerifierLocal);
        if inline {
            verifier_locals.inline(&Set::new());
        }

        let mut verifier_result = builder.build(verifier_tc);
        if inline {
            verifier_result.inline(&Set::new());
        }

        // The nodes each `verify` checks, now that `builder` knows the
        // verifier's `&&` chains.
        let checked: HashSet<Ref> = verified
            .iter()
            .flat_map(|exp| builder.collect_and_leaves(exp))
            .flat_map(|leaf| leaf.refs())
            .collect();
        for origin in &mut verifier_locals.origins {
            if checked.contains(&origin.node.reference) {
                origin.stage = Stage::CheckBookkeeping;
            }
        }

        // Merge verifier_locals into prover generating set.
        let mut origins = if prover_result.origins_aligned() && verifier_locals.origins_aligned() {
            let mut origins = prover_result.origins;
            origins.extend(verifier_locals.origins);
            origins
        } else {
            Vec::new()
        };
        let mut generating_set = prover_result.generating_set;
        generating_set.extend(verifier_locals.generating_set);
        let mut verifier = verifier_result.generating_set;

        // verifier_locals keeps the `==` node under each `verify`, so its
        // encoding is already a generator; reducing it again is wasted work.
        // What is left are the goals, one `b − 1` per checked bool.
        verifier.retain(|p| !generating_set.contains(p));

        let mut messages = Ctx::new();
        let mut pinned = Ctx::new();
        if inline {
            // `inline` kept the prover-message definitions back in `pl`,
            // already resolved down to non-message variables.
            generating_set = substitute_generators(generating_set, &mut origins, &prover_result.pl);
            verifier = substitute(verifier, &prover_result.pl);

            // Then every input a generator pins down, e.g. one the `where`
            // clause defines. Other variables only when pinned to a constant
            // (an asserted bool), which leaves the verifier's `==` encodings
            // alone.
            let inputs: Set<Ref> = dag.input_args().into_iter().map(Ref::new).collect();
            pinned = eliminate_definitions(&mut generating_set, &mut origins, &mut verifier, |v| {
                inputs.contains(&v.reference)
            });
            messages = prover_result.pl;
        }

        CompletenessInputs {
            generating_set,
            verifier,
            checks: verifier_result.checks,
            messages,
            pinned,
            origins,
            body_asserts,
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
            checks: inputs.checks,
            messages: inputs.messages,
            pinned: inputs.pinned,
        }
    }

    /// Explain why each `verify` holds, one block per check, sorted:
    ///
    /// ```text
    /// check: g*beta_z == v*c + v_r
    ///   v_r <- g*beta_r
    ///   beta_z <- beta*c + beta_r
    ///   v == beta*g
    ///   both sides: beta*g*c + g*beta_r
    /// ```
    ///
    /// The check is shown as the verifier writes it, followed by the
    /// definitions substituted into it: `t <- …` for a prover message and
    /// `x == …` for a variable a constraint pins down, such as an input the
    /// `where` clause defines. If both sides then agree, substitution alone
    /// discharged the check. Otherwise the basis has to prove the rest, and
    /// the explanation lists the basis polynomials that reduce their
    /// difference to 0, or the remainder if it is not 0. Polynomials other than
    /// the checks that are longer than [`EXPLAIN_MAX_TERMS`] are shown by their
    /// number of terms, and variables that print alike are told apart as in
    /// [`disambiguate`].
    pub fn explain(&self) -> String {
        let explanations: Vec<_> = self.checks.iter().map(|c| self.explain_check(c)).collect();
        let names = disambiguate(explanations.iter().flat_map(CheckExplanation::vars));
        let mut blocks: Vec<String> = explanations.iter().map(|e| e.render(&names)).collect();
        blocks.sort();
        blocks.concat()
    }

    fn explain_check(&self, check: &Check<C::F>) -> CheckExplanation<C::F> {
        let used =
            |defs: &Ctx<Var, Polynomial<C::F>>, lhs: &Polynomial<C::F>, rhs: &Polynomial<C::F>| {
                defs.iter()
                    .filter(|(x, _)| lhs.contains(x) || rhs.contains(x))
                    .map(|(x, value)| (x.clone(), value.clone()))
                    .collect::<Vec<_>>()
            };
        let messages = used(&self.messages, &check.lhs, &check.rhs);
        let lhs = check.lhs.clone().inline_vars(&self.messages).0;
        let rhs = check.rhs.clone().inline_vars(&self.messages).0;
        let pinned = used(&self.pinned, &lhs, &rhs);
        let lhs = lhs.inline_vars(&self.pinned).0;
        let rhs = rhs.inline_vars(&self.pinned).0;
        let difference = &lhs - &rhs;
        let reduction = (!difference.is_zero()).then(|| {
            let (remainder, divisors) =
                reduce_with_divisors(difference, &self.basis.polys, &self.basis.order);
            let used = divisors
                .into_iter()
                .map(|i| self.basis.polys[i].clone())
                .collect();
            (remainder, used)
        });
        CheckExplanation {
            check: check.clone(),
            messages,
            pinned,
            lhs,
            rhs,
            reduction,
        }
    }

    /// Reduces every verifier polynomial not already in the generating set
    /// against the prover/relation Gröbner basis; a zero remainder means the
    /// verifier equation is implied by the prover's computation, i.e. the
    /// protocol is complete.
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

#[cfg(test)]
mod tests {
    use super::CompletenessAnalysis;
    use crate::QualifierPropagation;
    use crate::Var;
    use crate::backend::GbBackend;
    use crate::backend::GbBackendKind;
    use crate::error::AnalysisError;
    use crate::frontend::Polynomial;
    use crate::ideal::Stage;
    use crate::tests::parse_and_concretize;
    use backend::ArkBls12_381;
    use graph::UDags;

    use share::Ctx;
    use share::unwrap;

    /// Test helper: build + compute in one call with default backend and
    /// inlining enabled (the common case in tests).
    fn from_input(dag: &graph::QDag<ArkBls12_381>) -> CompletenessAnalysis<ArkBls12_381> {
        let inputs = CompletenessAnalysis::build_inputs(dag, true);
        CompletenessAnalysis::from_inputs(inputs, GbBackendKind::default())
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

        let mut ca = from_input(&g);
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
            proto ifft_roundtrip<F: Field>(instance v: [F; 2]) where reduce(&&, v == v) {
                let p = interpolate(v);
                let u = eval(p);
                verify(reduce(&&, u == v))
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
                verify(reduce(&&, vc == va + vb))
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

        let inputs = CompletenessAnalysis::build_inputs(&g, true);
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
    fn relation_defined_input_completeness() {
        // The `where` clause defines `h`, and `k` through `h`; both must be
        // substituted away.
        let ex = r#"
            proto defined<G: Group, F: Scalar<G>>(
                witness x: F, witness y: F, instance g: G, instance h: G, instance k: G,
            ) where h == g*x && k == h + g*y {
                let r = random<F>;
                u <- g*r;
                c <- challenge<F>;
                z <- r + (x + y)*c;
                verify(g*z == u + k*c)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let inputs = CompletenessAnalysis::build_inputs(&g, true);
        let leftover: Vec<_> = inputs
            .generating_set
            .iter()
            .chain(&inputs.verifier)
            .flat_map(|p| p.vars())
            .filter(|v| ["h", "k"].contains(&v.name.as_str()))
            .collect();
        assert!(
            leftover.is_empty(),
            "inputs the relation defines should be substituted away, found {leftover:?}"
        );

        let mut ca =
            CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default());
        assert!(ca.run().is_ok(), "k = g*(x + y), so g*z == u + k*c holds");
    }

    #[test]
    fn relation_defined_input_incomplete() {
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

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let mut ca = from_input(&g);
        assert!(ca.run().is_err(), "g*z == u + h*c misses the g*y*c term");
    }

    #[test]
    fn explain_shows_the_substitution_that_discharges_a_check() {
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
        assert!(ca.run().is_ok());
        assert_eq!(
            ca.explain(),
            "check: g*z == h*c + u\n  u <- g*r\n  z <- x*c + r\n  h == g*x\n  both sides: g*x*c + g*r\n"
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

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let ca = from_input(&g);
        let explanation = ca.explain();
        assert!(
            explanation.contains("differ by g*y*c modulo the basis"),
            "the missing g*y*c term should be named:\n{explanation}"
        );
    }

    #[test]
    fn origins_follow_the_generating_set() {
        let ex = r#"
            proto inv<F: Field>(witness x: F, witness y: F) where x * y == 1 && x == x {
                c <- challenge<F>;
                t <- x * c;
                u <- y * c;
                verify(t * u == c * c)
            }"#;

        let m = parse_and_concretize(ex, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);

        let inputs = CompletenessAnalysis::build_inputs(&g, true);
        assert_eq!(inputs.origins.len(), inputs.generating_set.len());
        let stages: Vec<Stage> = inputs.origins.iter().map(|o| o.stage).collect();
        assert!(
            stages.contains(&Stage::Relation { conjunct: Some(0) }),
            "x * y - 1 should come from the first conjunct: {stages:?}"
        );
        assert!(
            stages.contains(&Stage::CheckBookkeeping),
            "the verified == should be check bookkeeping: {stages:?}"
        );
        assert_eq!(inputs.body_asserts, 0);
        let description = inputs.describe();
        assert!(description.contains("[where: conjunct 0]"), "{description}");
        assert!(description.contains("[check bookkeeping]"), "{description}");
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

    // -----------------------------------------------------------------
    // Splitting an asserted or verified `reduce(&&, …)` like `&&`
    // -----------------------------------------------------------------

    fn dag_of(src: &str) -> graph::QDag<ArkBls12_381> {
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        QualifierPropagation::from_dag(&gs[0])
    }

    /// Whether `Singular` is on `PATH`.
    fn singular_available() -> bool {
        std::process::Command::new("Singular")
            .arg("-q")
            .arg("-c")
            .arg("ring r = (integer, 7), (x(1)), dp;")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .is_ok()
    }

    /// The completeness verdict for the first protocol in `src`, with the
    /// basis computed by Singular, or `None` when Singular is not on `PATH`.
    fn singular_verdict(src: &str) -> Option<Result<(), AnalysisError<ArkBls12_381>>> {
        if !singular_available() {
            eprintln!("skipping: Singular not on PATH");
            return None;
        }
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(src), true);
        let mut ca = CompletenessAnalysis::from_inputs(inputs, GbBackendKind::Singular);
        Some(ca.run())
    }

    /// The names of the variables `build_inputs` pinned down for `src`.
    fn pinned_names(src: &str) -> Vec<String> {
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(src), true);
        inputs.pinned.iter().map(|(x, _)| x.to_string()).collect()
    }

    /// Whether, for every `i < n`, `x[i]` or `y[i]` was pinned down, which
    /// takes the `i`-th equality on its own: their product pins nothing.
    fn pins_every_element(pinned: &[String], n: usize) -> bool {
        (0..n).all(|i| pinned.contains(&format!("x[{i}]")) || pinned.contains(&format!("y[{i}]")))
    }

    #[test]
    fn and_chain_of_bools_stays_complete() {
        let ex = r#"
            proto and_chain<F: Field>(instance a: Bool, instance b: Bool) where a && b {
                verify(a)
            }"#;
        if let Some(result) = singular_verdict(ex) {
            assert!(result.is_ok(), "a && b gives a: {result:?}");
        }
    }

    #[test]
    fn reduce_and_of_bools_is_complete() {
        let ex = r#"
            proto reduce_bools<F: Field>(instance a: Bool, instance b: Bool) where reduce(&&, [a, b]) {
                verify(a)
            }"#;
        if let Some(result) = singular_verdict(ex) {
            assert!(result.is_ok(), "reduce(&&, [a, b]) gives a: {result:?}");
        }
    }

    #[test]
    fn asserted_reduce_and_splits_per_element() {
        let ex = r#"
            proto split<F: Field>(instance x: [F; 3], instance y: [F; 3]) where reduce(&&, x == y) {
                verify(x[2] == y[2])
            }"#;
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(ex), true);
        let pinned: Vec<String> = inputs.pinned.iter().map(|(x, _)| x.to_string()).collect();
        assert!(pins_every_element(&pinned, 3), "pinned: {pinned:?}");
        // No product of the equalities' bools is left over, nor anything else.
        assert!(
            inputs.generating_set.is_empty(),
            "{:?}",
            inputs.generating_set
        );
        assert!(inputs.verifier.is_empty(), "{:?}", inputs.verifier);
    }

    #[test]
    fn mapped_reduce_and_splits_per_element() {
        let ex = r#"
            proto mapped<F: Field>(instance x: [F; 3], instance y: [F; 3]) where reduce(&&, [x[i] == y[i] for i in 0..3]) {
                verify(x[2] == y[2])
            }"#;
        let pinned = pinned_names(ex);
        assert!(pins_every_element(&pinned, 3), "pinned: {pinned:?}");
    }

    #[test]
    fn reduce_and_through_a_function_splits_per_element() {
        let ex = r#"
            fn all_equal<F: Field>(instance x: [F; 3], instance y: [F; 3]) -> Bool {
                let same = reduce(&&, x == y);
                same
            }

            proto aliased<F: Field>(instance x: [F; 3], instance y: [F; 3]) where all_equal(x, y) {
                verify(x[2] == y[2])
            }"#;
        let pinned = pinned_names(ex);
        assert!(pins_every_element(&pinned, 3), "pinned: {pinned:?}");
    }

    #[test]
    fn verified_message_is_not_traced_into_the_prover() {
        // `b` is a prover message, an alias of the prover's reduction: the
        // verifier checks the message as sent, not how it was computed.
        let ex = r#"
            proto message<F: Field>(instance x: [F; 3], instance y: [F; 3]) where reduce(&&, x == y) {
                b <- reduce(&&, x == y);
                verify(b)
            }"#;
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(ex), true);
        let checks: Vec<String> = inputs
            .checks
            .iter()
            .map(|c| format!("{} == {}", c.lhs, c.rhs))
            .collect();
        assert_eq!(checks, ["b == 1"]);
        if let Some(result) = singular_verdict(ex) {
            assert!(result.is_ok(), "{result:?}");
        }
    }

    #[test]
    fn verified_reduce_and_checks_each_element() {
        let ex = r#"
            proto checks<F: Field>(instance x: [F; 3], instance y: [F; 3]) where reduce(&&, x == y) {
                verify(reduce(&&, x == y))
            }"#;
        let inputs = CompletenessAnalysis::build_inputs(&dag_of(ex), true);
        let checks: Vec<String> = inputs
            .checks
            .iter()
            .map(|c| format!("{} == {}", c.lhs, c.rhs))
            .collect();
        assert_eq!(checks, ["x[0] == y[0]", "x[1] == y[1]", "x[2] == y[2]"]);
        assert!(inputs.verifier.is_empty(), "{:?}", inputs.verifier);
    }

    #[test]
    fn computed_reduce_and_is_not_split() {
        // `c` may be false, so the relation says nothing about x and y.
        let ex = r#"
            proto computed<F: Field>(instance x: [F; 2], instance y: [F; 2], instance c: Bool) where c == reduce(&&, x == y) {
                verify(x[0] == y[0])
            }"#;
        let pinned = pinned_names(ex);
        assert!(!pins_every_element(&pinned, 1), "pinned: {pinned:?}");
        if let Some(result) = singular_verdict(ex) {
            assert!(
                matches!(result, Err(AnalysisError::Incomplete(_))),
                "c == reduce(&&, x == y) does not give x == y: {result:?}"
            );
        }
    }

    #[test]
    #[should_panic(expected = "reduce-map-empty")]
    fn empty_mapped_reduce_and_is_still_rejected() {
        use crate::ideal::{EncodeOptions, Ideal, IdealBuilder};
        use backend::{ABase, ATyp};
        use graph::{Op, Ref};
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::with_options(EncodeOptions {
            split_reductions: true,
            relation_asserts: None,
        });
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let bools = ATyp::Vec(Box::new(ATyp::Base(ABase::Bool)), 0);
        let v = Var::from_node(NodeIndex::new(0), bools.clone(), Qualifier::Instance);
        ideal.register(&v);
        let all = Var::from_node(
            NodeIndex::new(1),
            ATyp::Base(ABase::Bool),
            Qualifier::Instance,
        );
        ideal.register(&all);
        let domain = backend::op::mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), bools));
        let body = backend::op::mk::<ArkBls12_381>(Op::LoopParam(0, ATyp::Base(ABase::Bool)));
        builder.add_op(all, Op::ReduceMap(BinOp::And, domain, body), &mut ideal);
    }

    #[test]
    fn body_asserts_encode_to_nothing() {
        use crate::ideal::{EncodeOptions, Ideal, IdealBuilder};
        use backend::{ABase, ATyp};
        use graph::{Op, Ref};
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        // `assert(b)` on node 1, with `b` on node 0.
        let generators = |relation_asserts: Option<Vec<usize>>| {
            let mut builder = IdealBuilder::<ArkBls12_381>::with_options(EncodeOptions {
                split_reductions: true,
                relation_asserts: relation_asserts.map(|ns| {
                    ns.into_iter()
                        .map(|n| Ref::new(NodeIndex::new(n)))
                        .collect()
                }),
            });
            let mut ideal = Ideal::<ArkBls12_381>::new();
            let bool_t = ATyp::Base(ABase::Bool);
            let b = Var::from_node(NodeIndex::new(0), bool_t.clone(), Qualifier::Instance);
            ideal.register(&b);
            let assert = Var::from_node(
                NodeIndex::new(1),
                ATyp::Base(ABase::Unit),
                Qualifier::Instance,
            );
            ideal.register(&assert);
            let exp = backend::op::mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), bool_t));
            builder.add_op(assert, Op::Assert(exp), &mut ideal);
            ideal.generating_set.len()
        };
        assert_eq!(
            generators(None),
            1,
            "without the rule, assert(b) gives b - 1"
        );
        assert_eq!(generators(Some(vec![1])), 1, "the relation's assert stays");
        assert_eq!(
            generators(Some(vec![])),
            0,
            "a body assert encodes to nothing"
        );
    }
}
