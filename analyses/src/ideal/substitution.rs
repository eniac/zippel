//! Definitions `x := f`, kept resolved so that one pass substitutes them all.
//!
//! Substituting `f` for `x` is exact whenever `x − f` lies in the ideal and
//! `x` does not occur in `f`: the substitution is a ring map onto the
//! polynomials without `x`, with kernel `⟨x − f⟩`, so a polynomial lies in the
//! ideal iff its image lies in the image of the ideal. Encoder definitions,
//! prover messages and hypotheses `c·x + r` with `c` constant all qualify.

use std::collections::{BTreeSet, HashMap};

use ark_ff::Field;
use petgraph::algo::kosaraju_scc;
use petgraph::graph::{DiGraph, NodeIndex};
use share::Ctx;

use crate::Var;
use crate::frontend::Polynomial;

/// Why [`Substitution::insert`] refused a definition.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Refused {
    /// The variable already has a definition.
    #[error("{0} is already defined")]
    Defined(Var),
    /// The variable occurs in its own resolved value, as in `x := x·y`.
    #[error("{0} occurs in its own resolved value")]
    Occurs(Var),
}

/// Definitions `x := f` for distinct variables `x`, kept resolved: no value
/// mentions a defined variable, so [`Substitution::apply`] needs one pass.
///
/// Iteration follows insertion order, so nothing that iterates a
/// substitution depends on hashing.
#[derive(Clone, Debug)]
pub struct Substitution<F: Field> {
    /// The defined variables, in insertion order.
    order: Vec<Var>,
    /// The resolved value of each defined variable.
    values: Ctx<Var, Polynomial<F>>,
}

impl<F: Field> Default for Substitution<F> {
    fn default() -> Self {
        Self {
            order: Vec::new(),
            values: Ctx::new(),
        }
    }
}

impl<F: Field> Substitution<F> {
    /// Resolve encoder definitions in dependency order: each comes after
    /// every definition it mentions, and ties go to the least `Var`.
    ///
    /// Definitions that depend on each other cyclically, including one that
    /// mentions itself, are left out, so their variables stay variables. A
    /// definition that only reads one of them is kept.
    pub fn resolve(defs: &Ctx<Var, Polynomial<F>>) -> Self {
        // In `Var` order, so that indices compare like the keys.
        let entries: Vec<(&Var, &Polynomial<F>)> = defs.iter().collect();
        let n = entries.len();
        let index: HashMap<&Var, usize> = entries
            .iter()
            .enumerate()
            .map(|(i, (x, _))| (*x, i))
            .collect();
        // The keys that each definition mentions.
        let deps: Vec<Vec<usize>> = entries
            .iter()
            .map(|(_, f)| {
                let mut d: Vec<usize> =
                    mentioned(f).filter_map(|v| index.get(v).copied()).collect();
                d.sort_unstable();
                d.dedup();
                d
            })
            .collect();

        let mut graph = DiGraph::<(), ()>::with_capacity(n, 0);
        for _ in 0..n {
            graph.add_node(());
        }
        for (i, d) in deps.iter().enumerate() {
            for &j in d {
                graph.add_edge(NodeIndex::new(i), NodeIndex::new(j), ());
            }
        }
        // Kosaraju's, not Tarjan's: petgraph's Tarjan recurses, and chains of
        // definitions run thousands deep.
        let mut cyclic: Vec<bool> = deps
            .iter()
            .enumerate()
            .map(|(i, d)| d.contains(&i))
            .collect();
        for scc in kosaraju_scc(&graph).into_iter().filter(|scc| scc.len() > 1) {
            for node in scc {
                cyclic[node.index()] = true;
            }
        }

        // Kahn's algorithm over the rest, which is acyclic.
        let mut waiting = vec![0usize; n];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, d) in deps.iter().enumerate().filter(|(i, _)| !cyclic[*i]) {
            for &j in d.iter().filter(|&&j| !cyclic[j]) {
                waiting[i] += 1;
                dependents[j].push(i);
            }
        }
        let mut ready: BTreeSet<usize> =
            (0..n).filter(|&i| !cyclic[i] && waiting[i] == 0).collect();
        let mut s = Self::default();
        while let Some(i) = ready.pop_first() {
            // Every key that `i` mentions is resolved already, or cyclic.
            let (x, f) = entries[i];
            let value = s.apply(f);
            s.push(x.clone(), value);
            for &k in &dependents[i] {
                waiting[k] -= 1;
                if waiting[k] == 0 {
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
        let mut values = self.values.clone();
        values.retain(|x, _| keep(x));
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
            return Err(Refused::Defined(x));
        }
        let f = self.apply(&f);
        if mentions(&f, &x) {
            return Err(Refused::Occurs(x));
        }
        let def = Ctx::singleton(x.clone(), f.clone());
        let stale: Vec<Var> = self
            .values
            .iter()
            .filter(|(_, v)| mentions(v, &x))
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
        if !mentioned(p).any(|v| self.values.contains(v)) {
            return p.clone();
        }
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

    /// The number of definitions.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// Whether there are no definitions.
    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    /// Append `x := value`, which the caller has resolved: `value` mentions no
    /// key, and no value mentions `x`.
    fn push(&mut self, x: Var, value: Polynomial<F>) {
        self.values.entry(x.clone()).or_insert(value);
        self.order.push(x);
    }
}

/// The variables of each of `p`'s terms, with repeats.
fn mentioned<F: Field>(p: &Polynomial<F>) -> impl Iterator<Item = &Var> {
    p.terms.keys().flat_map(|m| m.0.iter().map(|(v, _)| v))
}

/// Whether `x` occurs in `p`. Unlike [`Polynomial::contains`], it builds no
/// set of variables.
fn mentions<F: Field>(p: &Polynomial<F>, x: &Var) -> bool {
    p.terms.keys().any(|m| m.0.contains(x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use backend::ATyp;
    use lang::typ::Qualifier;

    fn var(name: &str, node: usize) -> Var {
        Var::from_var(
            name,
            NodeIndex::new(node),
            ATyp::scalar(),
            Qualifier::Instance,
        )
    }

    fn v(x: &Var) -> Polynomial<Fr> {
        Polynomial::var(x)
    }

    fn lit(c: i64) -> Polynomial<Fr> {
        Polynomial::lit(&Fr::from(c))
    }

    fn defs(entries: &[(&Var, Polynomial<Fr>)]) -> Ctx<Var, Polynomial<Fr>> {
        let mut ctx = Ctx::new();
        for &(x, ref f) in entries {
            ctx.insert(x, f);
        }
        ctx
    }

    fn keys(s: &Substitution<Fr>) -> Vec<String> {
        s.iter().map(|(x, _)| x.to_string()).collect()
    }

    /// No value mentions a key.
    fn assert_resolved(s: &Substitution<Fr>) {
        for (x, f) in s.iter() {
            for k in f.vars().iter() {
                assert!(s.get(k).is_none(), "{x} := {f} mentions the key {k}");
            }
        }
    }

    /// Substitute `defs` into `p` until nothing changes, which ends when
    /// `defs` is acyclic.
    fn naive(p: &Polynomial<Fr>, defs: &Ctx<Var, Polynomial<Fr>>) -> Polynomial<Fr> {
        let mut p = p.clone();
        loop {
            let (q, changed) = p.inline_vars(defs);
            if !changed {
                return q;
            }
            p = q;
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
                term = &term * &v(u.choose(keys)?);
            }
            for x in free {
                let mut power = v(x);
                power.pow(u.int_in_range(0..=2)?);
                term = &term * &power;
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
            assert_resolved(&s);
            assert_eq!(s.len(), n, "a triangular system has no cycle");
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
            Ok(())
        });
    }

    #[test]
    fn resolve_orders_by_dependency_then_var() {
        let (a, b, c, d) = (var("a", 0), var("b", 1), var("c", 2), var("d", 3));
        let s = Substitution::resolve(&defs(&[
            (&a, &v(&b) + &v(&d)),
            (&b, &v(&c) * &v(&c)),
            (&c, lit(3)),
            (&d, &v(&c) + &lit(1)),
        ]));
        assert_eq!(keys(&s), ["c", "b", "d", "a"]);
        assert_eq!(s.get(&a), Some(&lit(13)));
    }

    #[test]
    fn iteration_follows_insertion_order() {
        let (a, b, c) = (var("a", 0), var("b", 1), var("c", 2));
        let mut s = Substitution::default();
        for x in [&c, &a, &b] {
            s.insert(x.clone(), lit(1)).unwrap();
        }
        assert_eq!(keys(&s), ["c", "a", "b"]);

        let without_a = s.restrict(|x| x != &a);
        assert_eq!(keys(&without_a), ["c", "b"]);
        assert_eq!(without_a.apply(&(&v(&a) + &v(&b))), &v(&a) + &lit(1));
    }

    #[test]
    fn insert_refuses_a_defined_variable_and_one_its_value_mentions() {
        let (a, x, y) = (var("a", 0), var("x", 1), var("y", 2));
        let mut s = Substitution::resolve(&defs(&[(&a, &v(&x) * &v(&y))]));

        assert_eq!(
            s.insert(a.clone(), lit(1)),
            Err(Refused::Defined(a.clone()))
        );
        assert_eq!(
            s.insert(y.clone(), &v(&y) * &v(&y)),
            Err(Refused::Occurs(y.clone()))
        );
        // `x := a + 1` resolves to `x·y + 1`, which mentions `x`.
        assert_eq!(
            s.insert(x.clone(), &v(&a) + &lit(1)),
            Err(Refused::Occurs(x.clone()))
        );

        assert_eq!(keys(&s), ["a"], "a refused definition changes nothing");
        assert_eq!(s.get(&a), Some(&(&v(&x) * &v(&y))));
    }

    #[test]
    fn insert_substitutes_into_every_value_that_mentions_the_variable() {
        let (a, b, c, x, y) = (
            var("a", 0),
            var("b", 1),
            var("c", 2),
            var("x", 3),
            var("y", 4),
        );
        let x_squared = &v(&x) * &v(&x);
        let mut s = Substitution::resolve(&defs(&[
            (&a, &v(&x) + &lit(1)),
            (&b, &x_squared * &v(&y)),
            (&c, &v(&y) + &lit(2)),
        ]));

        // `x := 2·c` resolves through `c` first.
        s.insert(x.clone(), &lit(2) * &v(&c)).unwrap();

        let two_c = &(&lit(2) * &v(&y)) + &lit(4);
        assert_eq!(s.get(&x), Some(&two_c));
        assert_eq!(s.get(&a), Some(&(&two_c + &lit(1))));
        assert_eq!(s.get(&b), Some(&(&(&two_c * &two_c) * &v(&y))));
        assert_eq!(s.get(&c), Some(&(&v(&y) + &lit(2))));
        assert_eq!(keys(&s), ["a", "b", "c", "x"]);
        assert_resolved(&s);
    }

    #[test]
    fn resolve_leaves_out_cyclic_definitions() {
        let (x, y, z, w, u, a) = (
            var("x", 0),
            var("y", 1),
            var("z", 2),
            var("w", 3),
            var("u", 4),
            var("a", 5),
        );
        let s = Substitution::resolve(&defs(&[
            // Reads the cycle between `y` and `z`.
            (&x, &v(&y) + &lit(1)),
            (&y, &v(&z) * &v(&a)),
            (&z, &v(&y) + &lit(2)),
            // Mentions itself.
            (&w, &v(&w) * &v(&a)),
            (&u, &v(&x) + &v(&w)),
        ]));

        assert_eq!(keys(&s), ["x", "u"]);
        assert_eq!(s.get(&x), Some(&(&v(&y) + &lit(1))));
        assert_eq!(s.get(&u), Some(&(&(&v(&y) + &lit(1)) + &v(&w))));
        assert_resolved(&s);
    }
}
