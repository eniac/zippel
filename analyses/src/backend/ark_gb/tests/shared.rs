//! Shared Katsura/Cyclic polynomial generators used by both the Criterion
//! bench (`benches/groebner.rs`) and the Sage cross-check tests
//! (`tests/groebner_sage.rs`).
//!
//! Ported from Singular's `polylib.lib` (`proc cyclic`, `proc katsura`,
//! `proc kat_var`). See `benches/groebner.rs` header for provenance details.

#![allow(dead_code)]

use super::super::monomial::Monomial;
use super::super::{GroebnerBasis, SparsePolynomial};
use ark_bls12_381::Fr;
use ark_ff::One;
use backend::ATyp;
use graph::PRef;
use lang::id::Vid;
use lang::typ::{Distribution, Qualifier};
use petgraph::graph::NodeIndex;

// ---------------------------------------------------------------------------
// Bench sizes — used by the Criterion bench (`benches/groebner.rs`).
//
// Sizes are the largest n for which a single Buchberger run terminates in
// under a few minutes on a developer workstation (release build, BLS12-381
// scalar field). Going one step higher in any family takes ≫10 min:
//
//   * Katsura-6 grevlex did not complete in 10 min (probed).
//   * Cyclic-6 / Cyclic-5 lex are intractable for our implementation.
//
// At these sizes a full `cargo bench --bench groebner` takes on the order
// of an hour because Criterion's default `MEASUREMENT_TIME` (30s) is small
// vs. one Buchberger iteration (≥1 min for n=5), forcing it to fall back
// to `SAMPLE_SIZE`-many single-iter samples.
// ---------------------------------------------------------------------------

/// Katsura-n under GrevLex — n=5 single-iter ≈ 60–100s in release;
/// n=6 did not complete in 10 min.
pub const KATSURA_GREVLEX_SIZES: &[usize] = &[3, 4, 5];
/// Katsura-n under ElimTerm — n=5 single-iter ≈ 124s in release.
pub const KATSURA_ELIM_SIZES: &[usize] = &[3, 4, 5];
/// Cyclic-n — n=5 single-iter ≈ 135s (grevlex), 201s (elim) in release.
/// n=6 is the classic SymbolicData hard case and is intractable for us.
pub const CYCLIC_SIZES: &[usize] = &[4, 5];

// ---------------------------------------------------------------------------
// Variable + polynomial construction helpers (inline clones of the
// `#[cfg(test)]` helpers in graph/src/analyses/groebner/buchberger.rs).
// ---------------------------------------------------------------------------

pub fn mk_var(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Private,
        Distribution::Uniform,
    )
}

pub fn mk_vars(prefix: &str, count: usize) -> Vec<PRef> {
    (0..count)
        .map(|i| mk_var(&format!("{prefix}{i}")))
        .collect()
}

pub fn var_poly<T: Monomial>(p: &PRef) -> SparsePolynomial<Fr, T> {
    SparsePolynomial::<Fr, T>::var(p)
}

pub fn one_poly<T: Monomial>() -> SparsePolynomial<Fr, T> {
    SparsePolynomial::<Fr, T>::lit(&Fr::one())
}

pub fn product_poly<T: Monomial, I>(factors: I) -> SparsePolynomial<Fr, T>
where
    I: IntoIterator<Item = SparsePolynomial<Fr, T>>,
{
    let mut acc = one_poly::<T>();
    for f in factors {
        acc *= f;
    }
    acc
}

// ---------------------------------------------------------------------------
// Cyclic-n — translation of Singular polylib.lib `proc cyclic(int n)`
// ---------------------------------------------------------------------------
// Original (lines 159-178):
//   ideal m = maxideal(1);
//   m = m[1..n], m[1..n];
//   for (j = 0; j <= n-2; j++) {
//     t = 0;
//     for (i = 1; i <= n; i++) { t = t + product(m, i..i+j); }
//     s = s + t;
//   }
//   s = s, product(m, 1..n) - 1;
//
// `m = m[1..n], m[1..n]` is the cyclic doubling trick so that `product(m, i..i+j)`
// for `i+j > n` wraps around. We implement the wrap with `% n`.
//
// Produces `n` generators in `n` variables.

pub fn cyclic_polys<T: Monomial>(vars: &[PRef]) -> Vec<SparsePolynomial<Fr, T>> {
    let n = vars.len();
    assert!(n >= 1, "Cyclic-n requires n >= 1");

    let mut polys = Vec::with_capacity(n);
    // Outer loop: degree-(j+1) elementary symmetric over cyclic windows.
    for j in 0..n.saturating_sub(1) {
        let mut t = SparsePolynomial::<Fr, T>::zero();
        for i in 0..n {
            let factors = (0..=j).map(|k| var_poly::<T>(&vars[(i + k) % n]));
            t += product_poly(factors);
        }
        polys.push(t);
    }
    // Final generator: x_0 * x_1 * ... * x_{n-1} - 1.
    let full = product_poly((0..n).map(|i| var_poly::<T>(&vars[i])));
    polys.push(full - one_poly::<T>());
    polys
}

// ---------------------------------------------------------------------------
// Katsura-n — translation of Singular polylib.lib `proc katsura` + `kat_var`
// ---------------------------------------------------------------------------
// Original (lines 249-316):
//   // Singular takes integer argument n_arg; internally: n = n_arg - 1.
//   // kat_var(i, n): if |i| <= n, returns var(|i|+1) (1-indexed), else 0.
//   s[1] = -1 + sum_{i=-n..=n} kat_var(i, n)
//   for (i = 0; i < n; i++) {
//     s[i+2] = -kat_var(i, n) + sum_{j=-n..=n} kat_var(j, n) * kat_var(i-j, n)
//   }
//
// Matching Sage's convention `sage.rings.ideal.Katsura(R, n_arg)`: `n_arg`
// variables produce `n_arg` generators, with Singular-internal `n = n_arg - 1`.

pub fn katsura_polys<T: Monomial>(vars: &[PRef]) -> Vec<SparsePolynomial<Fr, T>> {
    let n_arg = vars.len();
    assert!(n_arg >= 1, "Katsura-n requires at least one variable");
    let n = (n_arg - 1) as isize;

    // kat_var(i, n): Some(vars[|i|]) if |i| <= n else None.
    let kat_var = |i: isize| -> Option<SparsePolynomial<Fr, T>> {
        let ai = i.unsigned_abs();
        if (ai as isize) <= n {
            Some(var_poly::<T>(&vars[ai]))
        } else {
            None
        }
    };

    let mut polys = Vec::with_capacity(n_arg);

    // Linear generator: -1 + sum_{i=-n..=n} kat_var(i, n)
    let mut lin = SparsePolynomial::<Fr, T>::zero();
    for i in -n..=n {
        if let Some(v) = kat_var(i) {
            lin += v;
        }
    }
    lin -= one_poly::<T>();
    polys.push(lin);

    // Quadratic generators: for i = 0..n:
    //   -kat_var(i, n) + sum_{j=-n..=n} kat_var(j, n) * kat_var(i - j, n)
    for i in 0..n {
        let mut q = SparsePolynomial::<Fr, T>::zero();
        for j in -n..=n {
            if let (Some(a), Some(b)) = (kat_var(j), kat_var(i - j)) {
                q += &a * &b;
            }
        }
        if let Some(v) = kat_var(i) {
            q -= v;
        }
        polys.push(q);
    }
    polys
}

// ---------------------------------------------------------------------------
// Basis builders (unreduced input to Buchberger).
// ---------------------------------------------------------------------------

pub fn cyclic_basis<T: Monomial>(n: usize) -> GroebnerBasis<Fr, T> {
    let vars = mk_vars("c", n);
    GroebnerBasis::new(n, cyclic_polys::<T>(&vars))
}

pub fn katsura_basis<T: Monomial>(n: usize) -> GroebnerBasis<Fr, T> {
    let vars = mk_vars("k", n);
    GroebnerBasis::new(n, katsura_polys::<T>(&vars))
}
