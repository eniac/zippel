//! Definitions `x := f`, kept resolved so that one pass substitutes them all.
//!
//! Substituting `f` for `x` is exact whenever `x − f` lies in the ideal and
//! `x` does not occur in `f`: the substitution is a ring map onto the
//! polynomials without `x`, with kernel `⟨x − f⟩`, so a polynomial lies in the
//! ideal iff its image lies in the image of the ideal. Encoder definitions,
//! prover messages and hypotheses `c·x + r`, with `c` a nonzero constant and
//! `x` not in `r`, all qualify.

use std::collections::{HashMap, HashSet};

use ark_ff::Field;
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
#[derive(Clone, Debug, Default)]
pub struct Substitution<F: Field> {
    /// The resolved value of each defined variable.
    defs: Ctx<Var, Polynomial<F>>,
}

impl<F: Field> Substitution<F> {
    /// Resolve encoder definitions in dependency order.
    ///
    /// A definition on a cycle, or one that reads such a definition, has no
    /// place in that order and is left out, so its variable stays a variable.
    pub fn resolve(defs: &Ctx<Var, Polynomial<F>>) -> Self {
        // Kahn's algorithm: the number of keys each definition still waits
        // for, and the definitions that read each key.
        let mut waiting: HashMap<&Var, usize> = HashMap::new();
        let mut readers: HashMap<&Var, Vec<&Var>> = HashMap::new();
        for (x, f) in defs.iter() {
            let keys: HashSet<&Var> = f
                .terms
                .keys()
                .flat_map(|m| m.0.iter().map(|(y, _)| y))
                .filter(|y| defs.contains(y))
                .collect();
            waiting.insert(x, keys.len());
            for y in keys {
                readers.entry(y).or_default().push(x);
            }
        }
        let mut ready: Vec<&Var> = defs
            .iter()
            .map(|(x, _)| x)
            .filter(|x| waiting[x] == 0)
            .collect();
        let mut s = Self::default();
        while let Some(x) = ready.pop() {
            let value = s.apply(&defs[x]);
            s.defs.entry(x.clone()).or_insert(value);
            for &k in readers.get(x).into_iter().flatten() {
                let n = waiting.get_mut(k).expect("every key waits");
                *n -= 1;
                if *n == 0 {
                    ready.push(k);
                }
            }
        }
        s
    }

    /// Add `x := f`: resolve `f`, then substitute it into every value that
    /// mentions `x`.
    ///
    /// # Errors
    /// [`Refused::Defined`] if `x` is already defined, and [`Refused::Occurs`]
    /// if `x` occurs in the resolved `f`. Either way, nothing changes.
    pub fn insert(&mut self, x: Var, f: Polynomial<F>) -> Result<(), Refused> {
        if self.defs.contains(&x) {
            return Err(Refused::Defined);
        }
        let f = self.apply(&f);
        if f.contains(&x) {
            return Err(Refused::Occurs);
        }
        let def = Ctx::singleton(x.clone(), f.clone());
        let stale: Vec<Var> = self
            .defs
            .iter()
            .filter(|(_, v)| v.contains(&x))
            .map(|(k, _)| k.clone())
            .collect();
        for k in stale {
            if let Some(v) = self.defs.get_mut(&k) {
                *v = v.inline_vars(&def).0;
            }
        }
        self.defs.entry(x).or_insert(f);
        Ok(())
    }

    /// Substitute every definition into `p`. One pass suffices, since no
    /// value mentions a defined variable.
    pub fn apply(&self, p: &Polynomial<F>) -> Polynomial<F> {
        p.inline_vars(&self.defs).0
    }

    /// The definitions solved out of `generators`: each `c·x + r`, with `c` a
    /// nonzero constant, `x` not in `r` and `accepts(p, x)`, defines
    /// `x := −r/c` and is dropped. Ties go to the least `Var`.
    ///
    /// `generators` must already be resolved by every substitution applied
    /// before this one, so the definitions it finds mention no variable those
    /// substitutions define. On return, no remaining generator mentions a
    /// variable the result defines.
    ///
    /// Each pass applies the definitions so far to each generator in order.
    /// Passes repeat until one solves nothing, since a definition can let an
    /// earlier generator solve: a division row that reads the quotient only as
    /// `f·q` solves for it once another generator defines `f := 1`.
    pub fn solve(
        generators: &mut Vec<Polynomial<F>>,
        accepts: impl Fn(&Polynomial<F>, &Var) -> bool,
    ) -> Self {
        let mut solved = Self::default();
        loop {
            let mut found = false;
            generators.retain_mut(|p| {
                *p = solved.apply(p);
                let Some((x, value)) = solve_for(p, &accepts) else {
                    return !p.is_zero();
                };
                solved
                    .insert(x, value)
                    .expect("a generator the solved definitions resolved mentions none of them");
                found = true;
                false
            });
            if !found {
                return solved;
            }
        }
    }
}

/// `p = c·x + r` solved for the least `x` that `accepts`, with `c` a nonzero
/// constant and `x` not in `r`: `x` and its value `−r/c`.
fn solve_for<F: Field>(
    p: &Polynomial<F>,
    accepts: impl Fn(&Polynomial<F>, &Var) -> bool,
) -> Option<(Var, Polynomial<F>)> {
    // The number of terms each variable occurs in.
    let mut occurrences: HashMap<&Var, usize> = HashMap::new();
    for m in p.terms.keys() {
        for (x, _) in m.0.iter() {
            *occurrences.entry(x).or_default() += 1;
        }
    }
    let (x, c) = p
        .terms
        .iter()
        .filter_map(|(m, c)| {
            // `c·x`: exactly one variable, with exponent 1.
            let mut vars = m.iter();
            match (vars.next(), vars.next()) {
                (Some((x, &1)), None) => Some((x, c)),
                _ => None,
            }
        })
        .filter(|(x, _)| occurrences[*x] == 1 && accepts(p, x))
        .min_by(|(x, _), (y, _)| x.cmp(y))?;
    // `p` is a generator, so `p ≡ 0` modulo the ideal. With `p = c·x + r`,
    // that gives `x ≡ x − p/c = −r/c`, and `x`'s own term cancels from the value.
    let value = &Polynomial::var(x) - &(p * &Polynomial::lit(&c.inverse()?));
    Some((x.clone(), value))
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

    /// One variable per name, on nodes `0, 1, …`.
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

    /// Substitute `defs` into `p` until nothing changes, which ends when
    /// `defs` is acyclic.
    fn naive(p: &Polynomial<Fr>, defs: &Ctx<Var, Polynomial<Fr>>) -> Polynomial<Fr> {
        match p.inline_vars(defs) {
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
    fn resolve_and_insert_agree_with_naive_substitution_on_triangular_systems() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            // Shuffle the nodes, so that `Var` order is unrelated to dependency order.
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

            let resolved = Substitution::resolve(&system);
            // In `Var` order, which the shuffle makes unrelated to dependency order.
            let mut inserted = Substitution::default();
            for (x, f) in system.iter() {
                inserted.insert(x.clone(), f.clone()).unwrap();
            }
            for (x, f) in system.iter() {
                let value = naive(f, &system);
                assert_eq!(resolved.apply(&v(x)), value, "{x} := {f}");
                assert_eq!(inserted.apply(&v(x)), value, "{x} := {f}");
            }
            let p = arbitrary_poly(u, &keys, &free)?;
            assert_eq!(resolved.apply(&p), naive(&p, &system), "{p}");
            Ok(())
        });
    }

    #[test]
    fn resolve_leaves_out_definitions_on_or_after_a_cycle() {
        let [x, y, z, w, c, d, a] = vars(["x", "y", "z", "w", "c", "d", "a"]);
        let s = Substitution::resolve(&defs([
            // Reads the cycle between `y` and `z`.
            (&x, v(&y) + lit(1)),
            (&y, v(&z) * v(&a)),
            (&z, v(&y) + lit(2)),
            // Mentions itself.
            (&w, v(&w) * v(&a)),
            (&c, v(&a) + lit(1)),
            (&d, v(&c) * lit(2)),
        ]));

        for left_out in [&x, &y, &z, &w] {
            assert_eq!(s.apply(&v(left_out)), v(left_out), "{left_out}");
        }
        assert_eq!(s.apply(&v(&d)), (v(&a) + lit(1)) * lit(2));
    }

    #[test]
    fn insert_refuses_a_defined_variable_and_one_its_value_mentions() {
        let [a, x, y] = vars(["a", "x", "y"]);
        let mut s = Substitution::resolve(&defs([(&a, v(&x) * v(&y))]));

        assert_eq!(s.insert(a.clone(), lit(1)), Err(Refused::Defined));
        assert_eq!(s.insert(y.clone(), v(&y) * v(&y)), Err(Refused::Occurs));
        // `x := a + 1` resolves to `x·y + 1`, which mentions `x`.
        assert_eq!(s.insert(x.clone(), v(&a) + lit(1)), Err(Refused::Occurs));

        // A refused definition changes nothing.
        assert_eq!(s.apply(&v(&a)), v(&x) * v(&y));
        assert_eq!(s.apply(&v(&x)), v(&x));
    }

    #[test]
    fn solve_takes_the_least_linear_variable_and_drops_the_generator() {
        let [x, y, z] = vars(["x", "y", "z"]);
        // `x` and `y` both occur once, linearly; `z` occurs twice.
        let mut generators = vec![lit(2) * v(&x) + v(&y) + v(&z) * v(&z) + v(&z) - lit(3)];
        let s = Substitution::solve(&mut generators, |_, _| true);

        assert!(generators.is_empty());
        // x := −(y + z² + z − 3)/2
        let half = Polynomial::lit(&Fr::from(2).inverse().unwrap());
        assert_eq!(
            s.apply(&v(&x)),
            &(lit(3) - v(&y) - v(&z) * v(&z) - v(&z)) * &half
        );
        assert_eq!(s.apply(&v(&y)), v(&y));
    }

    #[test]
    fn solve_revisits_a_generator_once_a_later_one_defines_its_coefficient() {
        let [a, f, q] = vars(["a", "f", "q"]);
        // `f·q − a` solves for `q` only once `f − 1` defines `f`; `a` is refused.
        let mut generators = vec![v(&f) * v(&q) - v(&a), v(&f) - lit(1)];
        let s = Substitution::solve(&mut generators, |_, x| *x != a);

        assert!(generators.is_empty(), "{generators:?}");
        assert_eq!(s.apply(&v(&f)), lit(1));
        assert_eq!(s.apply(&v(&q)), v(&a));
    }

    #[test]
    fn solve_leaves_nothing_that_mentions_a_solved_variable() {
        arbtest::arbtest(|u| {
            let keys: Vec<Var> = (0..4).map(|i| var(&format!("k{i}"), i)).collect();
            let free = [var("a", 4), var("b", 5)];
            let mut generators = Vec::new();
            for _ in 0..u.int_in_range(1..=5)? {
                generators.push(arbitrary_poly(u, &keys, &free)? + v(u.choose(&keys)?));
            }
            let s = Substitution::solve(&mut generators, |_, _| true);

            let solved: Vec<&Var> = s.defs.iter().map(|(x, _)| x).collect();
            for p in generators
                .iter()
                .chain(s.defs.iter().map(|(_, value)| value))
            {
                for x in &solved {
                    assert!(!p.contains(x), "{p} mentions {x}");
                }
            }
            Ok(())
        });
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
        assert_eq!(s.apply(&v(&x)), two_c);
        assert_eq!(s.apply(&v(&a)), &two_c + &lit(1));
        assert_eq!(s.apply(&v(&b)), &two_c * &two_c * v(&y));
        assert_eq!(s.apply(&v(&c)), v(&y) + lit(2));
    }
}
