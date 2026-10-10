//! Definitions `x := f`, kept resolved so that one pass substitutes them all.
//!
//! Substituting `f` for `x` is exact whenever `x − f` lies in the ideal and
//! `x` does not occur in `f`: the substitution is a ring map onto the
//! polynomials without `x`, with kernel `⟨x − f⟩`, so a polynomial lies in the
//! ideal iff its image lies in the image of the ideal. Encoder definitions,
//! prover messages and hypotheses `c·x + r`, with `c` a nonzero constant and
//! `x` not in `r`, all qualify.

use std::collections::{BTreeSet, HashMap};

use ark_ff::Field;
use petgraph::Direction::Incoming;
use petgraph::algo::kosaraju_scc;
use petgraph::graphmap::DiGraphMap;
use share::Ctx;

use crate::Var;
use crate::frontend::Polynomial;

/// Why [`Substitution::insert`] refused a definition.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Refused {
    /// The variable already has a definition.
    #[error("the variable is already defined")]
    Defined,
    /// The variable occurs in its own resolved value, as in `x := x·y`.
    #[error("the variable occurs in its own resolved value")]
    Occurs,
}

/// Definitions `x := f` for distinct variables `x`, kept resolved: no value
/// mentions a defined variable, so [`Substitution::apply`] needs one pass.
///
/// Iteration follows insertion order, so nothing that iterates a
/// substitution depends on hashing.
#[derive(Clone, Debug, Default)]
pub struct Substitution<F: Field> {
    /// The defined variables, in insertion order.
    order: Vec<Var>,
    /// The resolved value of each defined variable.
    values: Ctx<Var, Polynomial<F>>,
}

impl<F: Field> Substitution<F> {
    /// Resolve encoder definitions in dependency order: each comes after
    /// every definition it mentions, and ties go to the least `Var`.
    ///
    /// Definitions that depend on each other cyclically, including one that
    /// mentions itself, are left out, so their variables stay variables. A
    /// definition that only reads one of them is kept.
    pub fn resolve(defs: &Ctx<Var, Polynomial<F>>) -> Self {
        // An edge `x → y` when the definition of `x` mentions the key `y`.
        let mut graph = DiGraphMap::<&Var, ()>::new();
        for (x, f) in defs.iter() {
            graph.add_node(x);
            for y in f.terms.keys().flat_map(|m| m.0.iter().map(|(y, _)| y)) {
                if defs.contains(y) {
                    graph.add_edge(x, y, ());
                }
            }
        }
        // Kosaraju's, not Tarjan's: petgraph's Tarjan recurses, and chains of
        // definitions run thousands deep.
        for scc in kosaraju_scc(&graph) {
            if scc.len() > 1 || graph.contains_edge(scc[0], scc[0]) {
                for x in scc {
                    graph.remove_node(x);
                }
            }
        }

        // Kahn's algorithm over the rest, which is acyclic.
        let mut waiting: HashMap<&Var, usize> = graph
            .nodes()
            .map(|x| (x, graph.neighbors(x).count()))
            .collect();
        let mut ready: BTreeSet<&Var> = graph.nodes().filter(|x| waiting[x] == 0).collect();
        let mut s = Self::default();
        while let Some(x) = ready.pop_first() {
            // Every key that `x` mentions is resolved already, or cyclic.
            s.push(x.clone(), s.apply(&defs[x]));
            for k in graph.neighbors_directed(x, Incoming) {
                let n = waiting.get_mut(k).expect("a node of the graph");
                *n -= 1;
                if *n == 0 {
                    ready.insert(k);
                }
            }
        }
        s
    }

    /// The part whose keys `keep` accepts, in the same order. Still resolved,
    /// since no value mentioned any key before.
    pub fn restrict(&self, keep: impl Fn(&Var) -> bool) -> Self {
        let order: Vec<Var> = self.order.iter().filter(|x| keep(x)).cloned().collect();
        let values = order
            .iter()
            .map(|x| (x.clone(), self.values[x].clone()))
            .collect();
        Self { order, values }
    }

    /// Add `x := f`: resolve `f`, then substitute it into every value that
    /// mentions `x`.
    ///
    /// # Errors
    /// [`Refused::Defined`] if `x` is already defined, and [`Refused::Occurs`]
    /// if `x` occurs in the resolved `f`. Either way, nothing changes.
    pub fn insert(&mut self, x: Var, f: Polynomial<F>) -> Result<(), Refused> {
        if self.values.contains(&x) {
            return Err(Refused::Defined);
        }
        let f = self.apply(&f);
        if f.contains(&x) {
            return Err(Refused::Occurs);
        }
        let def = Ctx::singleton(x.clone(), f.clone());
        let stale: Vec<Var> = self
            .values
            .iter()
            .filter(|(_, v)| v.contains(&x))
            .map(|(k, _)| k.clone())
            .collect();
        for k in stale {
            if let Some(v) = self.values.get_mut(&k) {
                *v = std::mem::replace(v, Polynomial::zero()).inline_vars(&def).0;
            }
        }
        self.push(x, f);
        Ok(())
    }

    /// Substitute every definition into `p`. One pass suffices, since no
    /// value mentions a key.
    pub fn apply(&self, p: &Polynomial<F>) -> Polynomial<F> {
        p.clone().inline_vars(&self.values).0
    }

    /// The resolved value of `x`, if `x` is defined.
    pub fn get(&self, x: &Var) -> Option<&Polynomial<F>> {
        self.values.get(x)
    }

    /// The definitions `x := f`, in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = (&Var, &Polynomial<F>)> {
        self.order.iter().map(|x| (x, &self.values[x]))
    }

    /// Append `x := value`, which the caller has resolved: `value` mentions no
    /// key, and no value mentions `x`.
    fn push(&mut self, x: Var, value: Polynomial<F>) {
        self.values.entry(x.clone()).or_insert(value);
        self.order.push(x);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use backend::ATyp;
    use lang::typ::Qualifier;
    use petgraph::graph::NodeIndex;

    fn var(name: &str, node: usize) -> Var {
        Var::from_var(
            name,
            NodeIndex::new(node),
            ATyp::scalar(),
            Qualifier::Instance,
        )
    }

    /// One variable per name, on nodes `0, 1, …`, so they order like `names`.
    fn vars<const N: usize>(names: [&str; N]) -> [Var; N] {
        std::array::from_fn(|i| var(names[i], i))
    }

    fn v(x: &Var) -> Polynomial<Fr> {
        Polynomial::var(x)
    }

    fn lit(c: i64) -> Polynomial<Fr> {
        Polynomial::lit(&Fr::from(c))
    }

    fn defs<const N: usize>(entries: [(&Var, Polynomial<Fr>); N]) -> Ctx<Var, Polynomial<Fr>> {
        entries.into_iter().map(|(x, f)| (x.clone(), f)).collect()
    }

    fn keys(s: &Substitution<Fr>) -> Vec<String> {
        s.iter().map(|(x, _)| x.to_string()).collect()
    }

    /// Substitute `defs` into `p` until nothing changes, which ends when
    /// `defs` is acyclic.
    fn naive(p: &Polynomial<Fr>, defs: &Ctx<Var, Polynomial<Fr>>) -> Polynomial<Fr> {
        match p.clone().inline_vars(defs) {
            (q, true) => naive(&q, defs),
            (q, false) => q,
        }
    }

    /// Up to three terms, each a small coefficient times at most one of `keys`
    /// and powers of `free`. One key per term keeps resolved values small.
    fn arbitrary_poly(
        u: &mut arbitrary::Unstructured,
        keys: &[Var],
        free: &[Var],
    ) -> arbitrary::Result<Polynomial<Fr>> {
        let mut p = Polynomial::zero();
        for _ in 0..u.int_in_range(0..=3)? {
            let mut term = lit(*u.choose(&[-2, -1, 1, 2, 3])?);
            if !keys.is_empty() && u.arbitrary()? {
                term *= v(u.choose(keys)?);
            }
            for x in free {
                let mut power = v(x);
                power.pow(u.int_in_range(0..=2)?);
                term *= power;
            }
            p += term;
        }
        Ok(p)
    }

    #[test]
    fn resolve_agrees_with_naive_substitution_on_triangular_systems() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            // Shuffle the nodes, so that `Var` order is not dependency order.
            let mut nodes: Vec<usize> = (0..n).collect();
            for i in (1..n).rev() {
                nodes.swap(i, u.int_in_range(0..=i)?);
            }
            let keys: Vec<Var> = nodes.iter().map(|&i| var(&format!("k{i}"), i)).collect();
            let free = [var("a", n), var("b", n + 1)];
            // The key at rank `r` may mention the keys after it.
            let mut system = Ctx::new();
            for r in 0..n {
                system.insert(&keys[r], &arbitrary_poly(u, &keys[r + 1..], &free)?);
            }

            let s = Substitution::resolve(&system);
            assert_eq!(s.iter().count(), n, "a triangular system has no cycle");
            for (x, f) in system.iter() {
                assert_eq!(s.get(x), Some(&naive(f, &system)), "{x} := {f}");
            }
            let position: HashMap<&Var, usize> =
                s.iter().enumerate().map(|(i, (x, _))| (x, i)).collect();
            for (x, f) in system.iter() {
                for y in f.vars().iter().filter(|y| system.contains(y)) {
                    assert!(position[y] < position[x], "{x} := {f} comes before {y}");
                }
            }
            let p = arbitrary_poly(u, &keys, &free)?;
            assert_eq!(s.apply(&p), naive(&p, &system), "{p}");

            // `Var` order, which the shuffle makes unrelated to dependency order.
            let mut inserted = Substitution::default();
            for (x, f) in system.iter() {
                inserted.insert(x.clone(), f.clone()).unwrap();
            }
            for (x, f) in s.iter() {
                assert_eq!(inserted.get(x), Some(f), "{x}");
            }
            Ok(())
        });
    }

    #[test]
    fn zero_constants_resolve_to_zero() {
        // `Polynomial::lit(0)` keeps a zero term, which `inline_vars` drops.
        let [t] = vars(["t"]);
        let s = Substitution::resolve(&defs([(&t, lit(0))]));
        assert!(s.get(&t).unwrap().is_zero());
        assert!(s.apply(&lit(0)).is_zero());
    }

    #[test]
    fn resolve_orders_by_dependency_then_var() {
        let [a, b, c, d] = vars(["a", "b", "c", "d"]);
        let s = Substitution::resolve(&defs([
            (&a, v(&b) + v(&d)),
            (&b, v(&c) * v(&c)),
            (&c, lit(3)),
            (&d, v(&c) + lit(1)),
        ]));
        assert_eq!(keys(&s), ["c", "b", "d", "a"]);
        assert_eq!(s.get(&a), Some(&lit(13)));
    }

    #[test]
    fn iteration_follows_insertion_order() {
        let [a, b, c] = vars(["a", "b", "c"]);
        let mut s = Substitution::default();
        for x in [&c, &a, &b] {
            s.insert(x.clone(), lit(1)).unwrap();
        }
        assert_eq!(keys(&s), ["c", "a", "b"]);

        let without_a = s.restrict(|x| x != &a);
        assert_eq!(keys(&without_a), ["c", "b"]);
        assert_eq!(without_a.apply(&(v(&a) + v(&b))), v(&a) + lit(1));
    }

    #[test]
    fn insert_refuses_a_defined_variable_and_one_its_value_mentions() {
        let [a, x, y] = vars(["a", "x", "y"]);
        let mut s = Substitution::resolve(&defs([(&a, v(&x) * v(&y))]));

        assert_eq!(s.insert(a.clone(), lit(1)), Err(Refused::Defined));
        assert_eq!(s.insert(y.clone(), v(&y) * v(&y)), Err(Refused::Occurs));
        // `x := a + 1` resolves to `x·y + 1`, which mentions `x`.
        assert_eq!(s.insert(x.clone(), v(&a) + lit(1)), Err(Refused::Occurs));

        assert_eq!(keys(&s), ["a"], "a refused definition changes nothing");
        assert_eq!(s.get(&a), Some(&(v(&x) * v(&y))));
    }

    #[test]
    fn insert_substitutes_into_every_value_that_mentions_the_variable() {
        let [a, b, c, x, y] = vars(["a", "b", "c", "x", "y"]);
        let mut s = Substitution::resolve(&defs([
            (&a, v(&x) + lit(1)),
            (&b, v(&x) * v(&x) * v(&y)),
            (&c, v(&y) + lit(2)),
        ]));

        // `x := 2·c` resolves through `c` first.
        s.insert(x.clone(), lit(2) * v(&c)).unwrap();

        let two_c = lit(2) * v(&y) + lit(4);
        assert_eq!(s.get(&x), Some(&two_c));
        assert_eq!(s.get(&a), Some(&(&two_c + &lit(1))));
        assert_eq!(s.get(&b), Some(&(&two_c * &two_c * v(&y))));
        assert_eq!(s.get(&c), Some(&(v(&y) + lit(2))));
        assert_eq!(keys(&s), ["a", "b", "c", "x"]);
    }

    #[test]
    fn resolve_leaves_out_cyclic_definitions() {
        let [x, y, z, w, u, a] = vars(["x", "y", "z", "w", "u", "a"]);
        let s = Substitution::resolve(&defs([
            // Reads the cycle between `y` and `z`.
            (&x, v(&y) + lit(1)),
            (&y, v(&z) * v(&a)),
            (&z, v(&y) + lit(2)),
            // Mentions itself.
            (&w, v(&w) * v(&a)),
            (&u, v(&x) + v(&w)),
        ]));

        assert_eq!(keys(&s), ["x", "u"]);
        assert_eq!(s.get(&x), Some(&(v(&y) + lit(1))));
        assert_eq!(s.get(&u), Some(&(v(&y) + lit(1) + v(&w))));
    }
}
