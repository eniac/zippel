//! The `Ideal` struct: the polynomial ideal being built during a single
//! `IdealBuilder::build()` call. Holds the generating set, polynomial
//! definitions (`pl`), and the variable namespace.

use std::collections::HashMap;
use std::fmt;

use backend::ArkConfig;
use backend::op::HasOpFactory;
use graph::Ref;
use share::{Ctx, Set};

use crate::Var;
use crate::frontend::Polynomial;

/// One coefficient slot of what a `verify` checks: `lhs == rhs`, or `b == 1` for
/// a bool that is not an `==`.
#[derive(Clone, Debug)]
pub struct Check<F: ark_ff::Field> {
    /// The left-hand side.
    pub lhs: Polynomial<F>,
    /// The right-hand side.
    pub rhs: Polynomial<F>,
}

/// Which part of the protocol a generator was encoded from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Stage {
    /// The prover's computation.
    Prover,
    /// The `assert` the graph wraps around the `where` clause.
    RelationAssert,
    /// A node under the `where` clause: `conjunct` is the index of the one
    /// top-level conjunct whose computation it belongs to, or `None` when it
    /// is shared by several.
    Relation {
        /// Index of the top-level `&&` leaf of the `where` clause.
        conjunct: Option<usize>,
    },
    /// A verifier computation other than the encoding of a checked equality.
    VerifierLocal,
    /// The encoding of a node a `verify` checks, such as its `==`.
    CheckBookkeeping,
    /// Not yet attributed by the caller.
    Unknown,
}

/// Where a generator came from: the DAG node whose encoding emitted it.
/// Diagnostic metadata only; it never affects the ideal.
#[derive(Clone, Debug)]
pub struct Origin {
    /// The part of the protocol the node belongs to.
    pub stage: Stage,
    /// The node's variable.
    pub node: Var,
    /// The node's operation, e.g. `==` or `reduce(*)`.
    pub op: &'static str,
}

/// The ideal of building a Gröbner basis — the basis polynomials, their
/// polynomial definitions (pl), and the vars used in the basis.
#[derive(Clone)]
pub struct Ideal<C: ArkConfig> {
    /// The generators of the ideal: every polynomial constrained to vanish on
    /// honest executions of the protocol fragment being analysed.
    pub generating_set: Vec<Polynomial<C::F>>,
    /// Where each generator came from, index-aligned with `generating_set`.
    /// Empty once lost: code that pushes generators without an origin leaves
    /// the two lengths different, and the next operation that keeps them in
    /// step drops the origins instead.
    pub origins: Vec<Origin>,
    /// What each `verify` checks. Recorded for reporting only, never a generator.
    pub checks: Vec<Check<C::F>>,
    /// What each `verify` requires, `b − 1` per checked bool, kept out of the
    /// generating set. Only filled with
    /// [`EncodeOptions::separate_goals`](crate::ideal::EncodeOptions); otherwise
    /// these are generators.
    pub goals: Vec<Polynomial<C::F>>,
    /// Definitional equations kept out of the generating set: each `Var` maps to
    /// the polynomial it abbreviates, so chains of intermediate DAG nodes can be
    /// substituted away by [`Ideal::inline`] instead of bloating the basis.
    pub pl: Ctx<Var, Polynomial<C::F>>,
    /// Namespace mapping each DAG node reference to the `Var` that stands for its
    /// value, so repeated visits to the same node reuse one variable.
    pub vars: HashMap<Ref, Var>,
    /// Variables in the order they were introduced; used as the seed ranking when
    /// building the lex / elimination monomial order for the Gröbner run.
    pub var_order: Vec<Var>,
}

impl<C: ArkConfig + HasOpFactory> Ideal<C> {
    /// Create an empty ideal: no generators, no definitions, empty namespace.
    pub fn new() -> Self {
        Self {
            generating_set: Vec::new(),
            origins: Vec::new(),
            checks: Vec::new(),
            goals: Vec::new(),
            pl: Ctx::new(),
            vars: HashMap::new(),
            var_order: Vec::new(),
        }
    }

    /// Register a Var in the namespace. Overwrites any existing entry
    /// for the same reference. Returns the previous entry if one existed.
    pub fn register(&mut self, var: &Var) -> Option<Var> {
        self.vars.insert(var.reference, var.clone())
    }

    /// Look up a Ref in the namespace. Panics if not found.
    ///
    /// # Panics
    /// Panics if `r` was never registered, which means a DAG node was consumed
    /// before the ideal builder visited its definition.
    pub fn find_ref(&self, r: &Ref) -> Var {
        if let Some(v) = self.vars.get(r) {
            return v.clone();
        }
        panic!("ideal: ref {} not found in namespace vars", r)
    }

    /// All variables occurring in the ideal: the defined `pl` keys together with
    /// every variable appearing in a generator.
    pub fn vars(&self) -> Set<Var> {
        let mut vars: Set<Var> = self.pl.keys().into_iter().collect();
        for p in &self.generating_set {
            for v in p.vars() {
                vars.insert(v);
            }
        }
        vars
    }

    /// Whether `origins` still describes `generating_set`.
    pub fn origins_aligned(&self) -> bool {
        self.origins.len() == self.generating_set.len()
    }

    /// Attribute every generator to `stage`.
    pub fn set_stage(&mut self, stage: Stage) {
        for origin in &mut self.origins {
            origin.stage = stage;
        }
    }

    /// Keep the generators `keep` accepts, and their origins with them.
    fn retain_generators(&mut self, mut keep: impl FnMut(&Polynomial<C::F>) -> bool) {
        if !self.origins_aligned() {
            self.origins.clear();
            self.generating_set.retain(keep);
            return;
        }
        let generators = std::mem::take(&mut self.generating_set);
        let origins = std::mem::take(&mut self.origins);
        for (p, origin) in generators.into_iter().zip(origins) {
            if keep(&p) {
                self.generating_set.push(p);
                self.origins.push(origin);
            }
        }
    }

    /// Filter out variables that satisfy the predicate
    pub fn eliminate_var<F: Fn(&Var) -> bool>(&mut self, f: &F) {
        self.retain_generators(|p| p.vars().iter().all(|v| !f(v)));
        self.pl.retain(|p, _| !f(p));
    }

    /// Drop every generator all of whose monomials satisfy the predicate, then
    /// prune `pl` down to the definitions still reachable from the surviving
    /// generators.
    pub fn eliminate_monomial<F: Fn(&crate::frontend::Monomial) -> bool>(&mut self, f: &F) {
        self.retain_generators(|p| p.terms.keys().any(|t| !f(t)));
        let basis_vars: Set<Var> = self.generating_set.iter().flat_map(|p| p.vars()).collect();
        self.pl.retain(|p, _| basis_vars.contains(p));
    }

    /// Inline all `pl` definitions into the basis polynomials, the goals and
    /// the checks.
    ///
    /// Topologically sorts `pl` entries, substitutes dependencies into
    /// each other to resolve chains, then substitutes the resolved
    /// definitions into all basis polynomials. Clears `pl` afterwards,
    /// except for the definitions of `transcript_refs`, which it keeps,
    /// resolved, instead of substituting.
    ///
    /// Those are resolved in the same order as the rest: a definition that
    /// reads one gets its resolved value. Its raw value can name a variable
    /// whose own definition is substituted away, which would leave that
    /// variable behind, undefined.
    ///
    /// A generator that restates a definition, `def − x` for `x := def` as
    /// `link_to_polys` emits next to each one, is dropped first instead of
    /// being expanded only to cancel: `x` is substituted by `def` everywhere,
    /// or, for a transcript variable, its definition stays in `pl`. This is
    /// only done when the definitions have no cycle, since a cyclic one is
    /// not substituted away.
    pub fn inline(&mut self, transcript_refs: &Set<Ref>) {
        if self.pl.is_empty() {
            return;
        }

        let pl_keys: Set<Var> = self.pl.keys();
        let mut order: Vec<Var> = Vec::with_capacity(pl_keys.len());
        let mut resolved: Set<Var> = Set::new();
        let mut remaining: Vec<(Var, usize)> = pl_keys
            .iter()
            .map(|k| {
                let deps = self.pl[k]
                    .terms
                    .keys()
                    .flat_map(|t| t.vars())
                    .filter(|v| pl_keys.contains(v))
                    .count();
                (k.clone(), deps)
            })
            .collect();

        let mut acyclic = true;
        loop {
            let mut next_remaining = Vec::new();
            let mut made_progress = false;
            for (k, deps) in remaining {
                if deps == 0 {
                    order.push(k.clone());
                    resolved.insert(k.clone());
                    made_progress = true;
                } else {
                    let new_deps = self.pl[&k]
                        .terms
                        .keys()
                        .flat_map(|t| t.vars())
                        .filter(|v| pl_keys.contains(v) && !resolved.contains(v))
                        .count();
                    if new_deps < deps {
                        made_progress = true;
                    }
                    next_remaining.push((k, new_deps));
                }
            }
            remaining = next_remaining;
            if !made_progress {
                for (k, _) in remaining {
                    order.push(k);
                }
                acyclic = false;
                break;
            }
            if remaining.is_empty() {
                break;
            }
        }

        if acyclic {
            // An O(1) copy: `Ctx` shares structure.
            let pl = self.pl.clone();
            self.retain_generators(|p| !restates_definition(p, &pl));
        }

        for k in &order {
            if let Some(def) = self.pl.remove(k) {
                let (new_def, _) = def.inline_vars(&self.pl);
                self.pl.insert(k, &new_def);
            }
        }

        // save transcript vars
        let mut saved: Vec<(Var, Polynomial<C::F>)> = Vec::new();
        for k in pl_keys.iter() {
            if transcript_refs.contains(&k.reference)
                && let Some(v) = self.pl.remove(k)
            {
                let (new_v, _) = v.inline_vars(&self.pl);
                saved.push((k.clone(), new_v));
            }
        }

        // fully inline all non-transcript vars
        for p in self.generating_set.iter_mut() {
            let (new_p, _) = p.clone().inline_vars(&self.pl);
            *p = new_p;
        }
        self.retain_generators(|p| !p.is_zero());
        for goal in self.goals.iter_mut() {
            *goal = goal.clone().inline_vars(&self.pl).0;
        }
        self.goals.retain(|g| !g.is_zero());
        for check in self.checks.iter_mut() {
            check.lhs = check.lhs.clone().inline_vars(&self.pl).0;
            check.rhs = check.rhs.clone().inline_vars(&self.pl).0;
        }

        for k in &order {
            self.pl.remove(k);
        }

        for (k, v) in saved {
            self.pl.insert(&k, &v);
        }
    }

    /// Merge another ideal's basis and polynomial definitions into this ideal.
    pub fn merge(&mut self, other: &Self) {
        if self.origins_aligned() && other.origins_aligned() {
            self.origins.extend(other.origins.iter().cloned());
        } else {
            self.origins.clear();
        }
        self.generating_set
            .extend(other.generating_set.iter().cloned());
        self.goals.extend(other.goals.iter().cloned());
        self.checks.extend(other.checks.iter().cloned());
        for (k, v) in other.pl.iter() {
            self.pl.insert(k, v);
        }
        self.var_order.extend(other.var_order.iter().cloned());
        for (k, v) in other.vars.iter() {
            self.vars.entry(*k).or_insert_with(|| v.clone());
        }
    }
}

/// Whether `p` is `def − x` for the definition `x := def` in `defs`.
fn restates_definition<F: ark_ff::Field>(
    p: &Polynomial<F>,
    defs: &Ctx<Var, Polynomial<F>>,
) -> bool {
    let minus_one = -F::one();
    p.terms.iter().any(|(mono, c)| {
        if *c != minus_one || mono.degree() != 1 {
            return false;
        }
        let Some(x) = mono.vars().pop() else {
            return false;
        };
        defs.get(&x).is_some_and(|def| {
            def.terms.len() + 1 == p.terms.len() && &(def - &Polynomial::var(&x)) == p
        })
    })
}

impl<C: ArkConfig + HasOpFactory> Default for Ideal<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// `Basis: ` followed by one generator per line, indented.
impl<C: ArkConfig> fmt::Display for Ideal<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Basis: ")?;
        for p in &self.generating_set {
            write!(f, "\n        {p}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::{ATyp, ArkBls12_381};

    /// This test is expected to FAIL before Task 3 because current vars() ignores basis-only vars.

    #[test]
    fn vars_is_pl_keys_union_basis_vars() {
        use ark_bls12_381::Fr;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let pl_ref = Var::from_var(
            "pl_v",
            NodeIndex::new(10),
            ATyp::scalar(),
            Qualifier::Instance,
        );
        let basis_ref = Var::from_var(
            "basis_v",
            NodeIndex::new(11),
            ATyp::scalar(),
            Qualifier::Instance,
        );

        let mut ideal = Ideal::<ArkBls12_381>::new();
        ideal.pl.insert(&pl_ref, &Polynomial::<Fr>::zero());
        ideal.generating_set.push(Polynomial::<Fr>::var(&basis_ref));

        let vars = ideal.vars();
        assert!(
            vars.contains(&pl_ref),
            "vars() should contain pl key: {:?}",
            pl_ref
        );
        assert!(
            vars.contains(&basis_ref),
            "vars() should contain basis var: {:?}",
            basis_ref
        );
        assert_eq!(vars.len(), 2, "vars() should have exactly 2 elements");
    }

    /// A scalar instance variable named `name` on node `n`.
    fn scalar(n: usize, name: &str) -> Var {
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        Var::from_var(name, NodeIndex::new(n), ATyp::scalar(), Qualifier::Instance)
    }

    #[test]
    fn inline_drops_a_generator_that_restates_a_kept_definition() {
        use ark_bls12_381::Fr;

        // `t := a + b` for a transcript variable `t`: `inline` keeps the
        // definition, so `a + b − t`, which restates it, is dropped instead of
        // staying behind as a generator.
        let (a, b, t) = (scalar(0, "a"), scalar(1, "b"), scalar(2, "t"));
        let def = &Polynomial::<Fr>::var(&a) + &Polynomial::var(&b);
        let uses_t = &(&Polynomial::<Fr>::var(&t) * &Polynomial::var(&a))
            - &Polynomial::lit(&Fr::from(1u64));
        let mut ideal = Ideal::<ArkBls12_381>::new();
        ideal.pl.insert(&t, &def);
        ideal.generating_set.push(&def - &Polynomial::var(&t));
        ideal.generating_set.push(uses_t.clone());
        let mut transcript = Set::new();
        transcript.insert(t.reference);
        ideal.inline(&transcript);
        assert_eq!(ideal.generating_set, vec![uses_t]);
        assert_eq!(ideal.pl.get(&t), Some(&def));
    }

    #[test]
    fn inline_keeps_a_generator_that_differs_from_the_definition() {
        use ark_bls12_381::Fr;

        // `x := a + b` next to `a + c − x`, which is not a restatement: it
        // says `b == c`.
        let (a, b, c, x) = (
            scalar(0, "a"),
            scalar(1, "b"),
            scalar(2, "c"),
            scalar(3, "x"),
        );
        let var = Polynomial::<Fr>::var;
        let mut ideal = Ideal::<ArkBls12_381>::new();
        ideal.pl.insert(&x, &(&var(&a) + &var(&b)));
        ideal.generating_set.push(&(&var(&a) + &var(&c)) - &var(&x));
        ideal.inline(&Set::new());
        assert_eq!(ideal.generating_set, vec![&var(&c) - &var(&b)]);
    }
}
