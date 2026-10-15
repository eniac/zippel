//! The `Ideal` struct: the polynomial ideal being built during a single
//! `IdealBuilder::build()` call. Holds the generating set, polynomial
//! definitions (`pl`), and the variable namespace.

use std::collections::{HashMap, HashSet};
use std::fmt;

use backend::ArkConfig;
use backend::op::HasOpFactory;
use graph::Ref;
use share::{Ctx, Set};

use super::Substitution;
use crate::Var;
use crate::frontend::Polynomial;

/// The ideal of building a Gröbner basis — the basis polynomials, their
/// polynomial definitions (pl), and the vars used in the basis.
#[derive(Clone)]
pub struct Ideal<C: ArkConfig> {
    /// The generators of the ideal: what a run of the fragment computes. Its
    /// `conditions` are not among them.
    pub generating_set: Vec<Polynomial<C::F>>,
    /// When a run of the fragment succeeds: each polynomial vanishes exactly
    /// when its `verify` or `assert` holds, or its operation (a division, an
    /// interpolation) is defined rather than aborting. Kept apart from the
    /// generators because an analysis decides what they mean: it either
    /// assumes them ([`Ideal::assuming_conditions`]) or proves them
    /// ([`Ideal::take_conditions`]), and [`Ideal::into_generators`] refuses
    /// an ideal that did neither.
    pub(super) conditions: Vec<Polynomial<C::F>>,
    /// One-step definitions `x := f` recorded by the encoders, each also a
    /// generator `f − x`. [`Ideal::substitute_definitions`] resolves them and
    /// substitutes them away.
    pub pl: Ctx<Var, Polynomial<C::F>>,
    /// Namespace mapping each DAG node reference to the `Var` that stands for its
    /// value, so repeated visits to the same node reuse one variable.
    pub vars: HashMap<Ref, Var>,
    /// Variables in the order they were introduced; used as the seed ranking when
    /// building the lex / elimination monomial order for the Gröbner run.
    pub var_order: Vec<Var>,
    /// The quotient and remainder witnesses of every polynomial division
    /// encoded into this ideal, each a sentinel with its own `Ref`.
    pub division_witnesses: HashSet<Ref>,
    /// Each sample with an exclusion, and what the exclusion makes nonzero:
    /// `r`, `∏ (r − s)` over the excluded values `s`, or `r^n − 1`.
    pub excluded: Vec<(Var, Polynomial<C::F>)>,
    /// The divisors whose definedness conditions require them nonzero.
    pub divisors: Vec<Polynomial<C::F>>,
}

impl<C: ArkConfig + HasOpFactory> Ideal<C> {
    /// Create an empty ideal: no generators, no definitions, empty namespace.
    pub fn new() -> Self {
        Self {
            generating_set: Vec::new(),
            conditions: Vec::new(),
            pl: Ctx::new(),
            vars: HashMap::new(),
            var_order: Vec::new(),
            division_witnesses: HashSet::new(),
            excluded: Vec::new(),
            divisors: Vec::new(),
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

    /// Resolve the `pl` definitions, substitute them into the generators, the
    /// conditions, the exclusions and the divisors, and return them.
    ///
    /// Empties `pl` and drops the generators and conditions that become
    /// zero. A definition that [`Substitution::resolve`] leaves out
    /// stays a variable, which its generator `f − x` still defines.
    pub fn substitute_definitions(&mut self) -> Substitution<C::F> {
        let defs = Substitution::resolve(&std::mem::take(&mut self.pl));
        for p in &mut self.generating_set {
            *p = defs.apply(p);
        }
        self.generating_set.retain(|p| !p.is_zero());
        for p in &mut self.conditions {
            *p = defs.apply(p);
        }
        self.conditions.retain(|p| !p.is_zero());
        for p in self
            .excluded
            .iter_mut()
            .map(|(_, p)| p)
            .chain(&mut self.divisors)
        {
            *p = defs.apply(p);
        }
        defs
    }

    /// The fragment restricted to its successful runs: its conditions become
    /// generators.
    #[must_use]
    pub fn assuming_conditions(mut self) -> Self {
        self.generating_set.append(&mut self.conditions);
        self
    }

    /// Removes and returns the conditions, for an analysis that proves them.
    pub fn take_conditions(&mut self) -> Vec<Polynomial<C::F>> {
        std::mem::take(&mut self.conditions)
    }

    /// The generators, for a Gröbner basis computation.
    ///
    /// # Panics
    /// Panics if conditions remain: each must be assumed or proved, never
    /// silently left out.
    pub fn into_generators(self) -> Vec<Polynomial<C::F>> {
        assert!(
            self.conditions.is_empty(),
            "{} unresolved condition(s): assume them with `assuming_conditions` \
             or prove them with `take_conditions`",
            self.conditions.len()
        );
        self.generating_set
    }

    /// Merge another ideal's generators, conditions, definitions, exclusions
    /// and divisors into this ideal. Its conditions stay conditions.
    pub fn merge(&mut self, other: &Self) {
        self.generating_set
            .extend(other.generating_set.iter().cloned());
        self.conditions.extend(other.conditions.iter().cloned());
        for (k, v) in other.pl.iter() {
            self.pl.insert(k, v);
        }
        self.var_order.extend(other.var_order.iter().cloned());
        for (k, v) in other.vars.iter() {
            self.vars.entry(*k).or_insert_with(|| v.clone());
        }
        self.division_witnesses
            .extend(other.division_witnesses.iter().copied());
        self.excluded.extend(other.excluded.iter().cloned());
        self.divisors.extend(other.divisors.iter().cloned());
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

    #[test]
    fn substitute_definitions_resolves_and_returns_them() {
        use ark_bls12_381::Fr;
        use ark_ff::One;

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
        let (a, b, s, t) = (var("a", 0), var("b", 1), var("s", 2), var("t", 3));
        let v = |x: &Var| Polynomial::<Fr>::var(x);
        let a_plus_1 = &v(&a) + &Polynomial::lit(&Fr::one());
        let t_value = &a_plus_1 * &a_plus_1;

        // `t := s*s` reads `s := a + 1`.
        let mut ideal = Ideal::<ArkBls12_381>::new();
        ideal.pl.insert(&s, &a_plus_1);
        ideal.pl.insert(&t, &(&v(&s) * &v(&s)));
        ideal.generating_set.push(&v(&t) - &v(&b));
        ideal.generating_set.push(&v(&t) - &(&v(&s) * &v(&s)));

        let defs = ideal.substitute_definitions();

        assert!(ideal.pl.is_empty());
        assert_eq!(defs.apply(&v(&t)), t_value);
        assert_eq!(
            ideal.generating_set,
            [&t_value - &v(&b)],
            "a generator that becomes zero is dropped"
        );
    }

    /// A condition stays a condition through `merge`, and leaves only by
    /// being assumed or taken.
    #[test]
    fn conditions_are_assumed_or_taken() {
        use ark_bls12_381::Fr;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let v = |name: &str, node: usize| {
            Polynomial::<Fr>::var(&Var::from_var(
                name,
                NodeIndex::new(node),
                ATyp::scalar(),
                Qualifier::Instance,
            ))
        };
        let (generator, condition) = (v("g", 0), v("c", 1));
        let mut fragment = Ideal::<ArkBls12_381>::new();
        fragment.generating_set.push(generator.clone());
        fragment.conditions.push(condition.clone());

        let mut merged = Ideal::<ArkBls12_381>::new();
        merged.merge(&fragment);
        assert_eq!(merged.conditions, vec![condition.clone()]);
        assert_eq!(merged.generating_set, vec![generator.clone()]);

        let assumed = fragment.clone().assuming_conditions();
        assert!(assumed.conditions.is_empty());
        assert_eq!(
            assumed.into_generators(),
            vec![generator.clone(), condition.clone()]
        );

        assert_eq!(merged.take_conditions(), vec![condition]);
        assert_eq!(merged.into_generators(), vec![generator]);
    }

    #[test]
    #[should_panic(expected = "unresolved condition")]
    fn generators_refuse_unresolved_conditions() {
        let mut ideal = Ideal::<ArkBls12_381>::new();
        ideal.conditions.push(Polynomial::zero());
        let _ = ideal.into_generators();
    }
}
