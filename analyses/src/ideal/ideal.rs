//! The `Ideal` struct: the polynomial ideal being built during a single
//! `IdealBuilder::build()` call. Holds the generating set, polynomial
//! definitions (`pl`), and the variable namespace.

use std::collections::HashMap;
use std::fmt;

use backend::ArkConfig;
use backend::op::HasOpFactory;
use graph::Ref;
use share::{Ctx, Set};

use super::Substitution;
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

/// The ideal of building a Gröbner basis — the basis polynomials, their
/// polynomial definitions (pl), and the vars used in the basis.
#[derive(Clone)]
pub struct Ideal<C: ArkConfig> {
    /// The generators of the ideal: every polynomial constrained to vanish on
    /// honest executions of the protocol fragment being analysed.
    pub generating_set: Vec<Polynomial<C::F>>,
    /// What each `verify` checks. Recorded for reporting only, never a generator.
    pub checks: Vec<Check<C::F>>,
    /// One-step definitions `x := f` recorded by the encoders, each also a
    /// generator `f − x`. [`Ideal::inline`] resolves them and substitutes them away.
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
            checks: Vec::new(),
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

    /// Resolve the `pl` definitions, substitute them into the generators and
    /// both sides of every check, and return them.
    ///
    /// Empties `pl` and drops the generators that become zero. A definition
    /// that [`Substitution::resolve`] leaves out stays a variable, which its
    /// generator `f − x` still defines.
    pub fn inline(&mut self) -> Substitution<C::F> {
        let defs = Substitution::resolve(&std::mem::take(&mut self.pl));
        for p in &mut self.generating_set {
            *p = defs.apply(p);
        }
        self.generating_set.retain(|p| !p.is_zero());
        // Checks keep their sides even when equal: a check that holds is still a check.
        for check in &mut self.checks {
            check.lhs = defs.apply(&check.lhs);
            check.rhs = defs.apply(&check.rhs);
        }
        defs
    }

    /// Merge another ideal's basis, checks and polynomial definitions into this ideal.
    pub fn merge(&mut self, other: &Self) {
        self.generating_set
            .extend(other.generating_set.iter().cloned());
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
    fn inline_substitutes_resolved_definitions_and_returns_them() {
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
        ideal.checks.push(Check {
            lhs: v(&s),
            rhs: v(&t),
        });
        ideal.checks.push(Check {
            lhs: v(&s),
            rhs: a_plus_1.clone(),
        });

        let defs = ideal.inline();

        assert!(ideal.pl.is_empty());
        assert_eq!(defs.apply(&v(&t)), t_value);
        assert_eq!(
            ideal.generating_set,
            [&t_value - &v(&b)],
            "a generator that becomes zero is dropped"
        );
        assert_eq!(ideal.checks.len(), 2, "a check that holds is still a check");
        assert_eq!(ideal.checks[0].lhs, a_plus_1);
        assert_eq!(ideal.checks[0].rhs, t_value);
        assert_eq!(ideal.checks[1].lhs, a_plus_1);
        assert_eq!(ideal.checks[1].rhs, a_plus_1);
    }
}
