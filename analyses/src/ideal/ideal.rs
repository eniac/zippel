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
    /// What each `assert` or `verify` checks. Callers choose which checks are
    /// assumptions and which are proof obligations.
    pub checks: Vec<Check<C::F>>,
    /// Definitional equations kept out of the generating set: each `Var` maps to
    /// the polynomial it abbreviates, so chains of intermediate DAG nodes can be
    /// substituted away by [`Ideal::inline`] instead of bloating the basis.
    pub pl: Ctx<Var, Polynomial<C::F>>,
    /// Total Boolean definitions that cannot be represented by `pl`: each
    /// equality result and its defining equations (including inverse witnesses).
    /// These define the result for every input; they do not assert it is true.
    pub(crate) boolean_definitions: HashMap<Var, Vec<Polynomial<C::F>>>,
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
            pl: Ctx::new(),
            boolean_definitions: HashMap::new(),
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
        self.boolean_definitions.retain(|p, _| !f(p));
    }

    /// Drop every generator all of whose monomials satisfy the predicate, then
    /// prune `pl` down to the definitions still reachable from the surviving
    /// generators.
    pub fn eliminate_monomial<F: Fn(&crate::frontend::Monomial) -> bool>(&mut self, f: &F) {
        self.retain_generators(|p| p.terms.keys().any(|t| !f(t)));
        let basis_vars: Set<Var> = self.generating_set.iter().flat_map(|p| p.vars()).collect();
        self.pl.retain(|p, _| basis_vars.contains(p));
        self.boolean_definitions
            .retain(|p, _| basis_vars.contains(p));
    }

    /// Inline all `pl` definitions into the basis polynomials and the checks.
    ///
    /// Topologically sorts `pl` entries, substitutes dependencies into
    /// each other to resolve chains, then substitutes the resolved
    /// definitions into all basis polynomials. Clears `pl` afterwards.
    pub fn inline(&mut self, transcript_refs: &Set<Ref>) {
        if self.pl.is_empty() {
            return;
        }

        let pl_keys: Set<Var> = self.pl.keys();
        let mut order: Vec<Var> = Vec::with_capacity(pl_keys.len());
        let mut resolved: Set<Var> = Set::new();
        let mut inlineable: Set<Var> = pl_keys.clone();
        inlineable.retain(|k| !transcript_refs.contains(&k.reference));
        let mut remaining: Vec<(Var, usize)> = inlineable
            .iter()
            .map(|k| {
                let deps = self.pl[k]
                    .terms
                    .keys()
                    .flat_map(|t| t.vars())
                    .filter(|v| inlineable.contains(v))
                    .count();
                (k.clone(), deps)
            })
            .collect();

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
                        .filter(|v| inlineable.contains(v) && !resolved.contains(v))
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
                break;
            }
            if remaining.is_empty() {
                break;
            }
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
        for check in self.checks.iter_mut() {
            check.lhs = check.lhs.clone().inline_vars(&self.pl).0;
            check.rhs = check.rhs.clone().inline_vars(&self.pl).0;
        }
        for definitions in self.boolean_definitions.values_mut() {
            for p in definitions {
                *p = p.clone().inline_vars(&self.pl).0;
            }
        }

        for (k, v) in saved {
            self.pl.insert(&k, &v);
        }

        for k in &order {
            self.pl.remove(k);
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
        self.checks.extend(other.checks.iter().cloned());
        self.boolean_definitions
            .extend(other.boolean_definitions.clone());
        for (k, v) in other.pl.iter() {
            self.pl.insert(k, v);
        }
        self.var_order.extend(other.var_order.iter().cloned());
        for (k, v) in other.vars.iter() {
            self.vars.entry(*k).or_insert_with(|| v.clone());
        }
    }
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
}
