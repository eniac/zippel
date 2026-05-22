//! Cross-backend regression suite: legacy in-tree Buchberger vs ark-gb.
//!
//! For each fixture (family × size × monomial order) compute the
//! reduced GB through both backends and assert element-wise equality
//! of the resulting `Vec<SparsePolynomial<Fr, T>>`. ark-gb is the
//! shipping production path; the legacy in-tree implementation lives
//! in `#[cfg(test)]` scope (see `buchberger::legacy_compute_reduced_gb`)
//! specifically so this test (and `speedup_bench`) can A/B against it.
//!
//! Run with:
//! ```sh
//! cargo test -p graph regression                          # default tests
//! cargo test -p graph regression -- --ignored             # + Katsura-5 / Cyclic-5
//! ```

#![cfg(test)]

use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, One};
use backend::ATyp;
use lang::id::Vid;
use lang::typ::{Distribution, Qualifier};
use petgraph::graph::NodeIndex;

use crate::PRef;
use crate::analyses::groebner::buchberger::legacy_compute_reduced_gb;
use crate::analyses::groebner::monomial::{ElimTerm, GrevLexTerm, Monomial};
use crate::analyses::groebner::sparsepoly::SparsePolynomial;

#[path = "../../../../benches/groebner_shared.rs"]
mod shared;

/// Compute the reduced Gröbner basis of `input` through both the legacy
/// in-tree Buchberger and the ark-gb-backed `T::compute_reduced_gb`, then
/// assert element-wise equality of the resulting vectors. On mismatch the
/// `assert_eq!` formatter dumps both bases for diagnosis.
fn compare<T: Monomial + std::fmt::Debug>(
    label: &str,
    num_vars: usize,
    input: Vec<SparsePolynomial<Fr, T>>,
) {
    let legacy = legacy_compute_reduced_gb(num_vars, input.clone());
    let ark = T::compute_reduced_gb(num_vars, input);
    assert_eq!(legacy, ark, "[{label}] backends disagree on reduced GB");
}

// ---------------------------------------------------------------------------
// Local `elim_var` / `noelim_var` clones. These mirror the `#[cfg(test)]`
// helpers in `buchberger.rs` (lines 477–498). Duplicated inline because the
// originals aren't re-exported across sibling test modules; the bodies are
// tiny and self-explanatory.
// ---------------------------------------------------------------------------

fn elim_var(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Private,
        Distribution::Uniform,
    )
}

fn noelim_var(name: &str) -> PRef {
    PRef::from_var(
        Vid::new(name),
        NodeIndex::new(0),
        ATyp::scalar(),
        0,
        Qualifier::Public,
        Distribution::Nonuniform,
    )
}

// ---------------------------------------------------------------------------
// GrevLex matrix — uses `shared::mk_vars`, `shared::katsura_polys`,
// `shared::cyclic_polys` so we don't duplicate fixture generators.
// ---------------------------------------------------------------------------

#[test]
fn regression_grevlex_katsura_3() {
    let n = 3;
    let vars = shared::mk_vars("k", n);
    let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::katsura_polys(&vars);
    compare("grevlex/katsura/3", n, input);
}

#[test]
fn regression_grevlex_katsura_4() {
    let n = 4;
    let vars = shared::mk_vars("k", n);
    let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::katsura_polys(&vars);
    compare("grevlex/katsura/4", n, input);
}

#[test]
#[ignore]
fn regression_grevlex_katsura_5() {
    let n = 5;
    let vars = shared::mk_vars("k", n);
    let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::katsura_polys(&vars);
    compare("grevlex/katsura/5", n, input);
}

#[test]
fn regression_grevlex_cyclic_3() {
    let n = 3;
    let vars = shared::mk_vars("c", n);
    let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::cyclic_polys(&vars);
    compare("grevlex/cyclic/3", n, input);
}

#[test]
fn regression_grevlex_cyclic_4() {
    let n = 4;
    let vars = shared::mk_vars("c", n);
    let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::cyclic_polys(&vars);
    compare("grevlex/cyclic/4", n, input);
}

#[test]
#[ignore]
fn regression_grevlex_cyclic_5() {
    let n = 5;
    let vars = shared::mk_vars("c", n);
    let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::cyclic_polys(&vars);
    compare("grevlex/cyclic/5", n, input);
}

// ---------------------------------------------------------------------------
// ElimTerm matrix — uniform-qualifier variables (degenerates to grevlex
// because no var is marked Private+Uniform-vs-Public-Nonuniform mixed, but
// still exercises the `ZippelElimMono` code path in ark-gb).
// ---------------------------------------------------------------------------

#[test]
fn regression_elim_katsura_3() {
    let n = 3;
    let vars = shared::mk_vars("k", n);
    let input: Vec<SparsePolynomial<Fr, ElimTerm>> = shared::katsura_polys(&vars);
    compare("elim/katsura/3", n, input);
}

#[test]
fn regression_elim_katsura_4() {
    let n = 4;
    let vars = shared::mk_vars("k", n);
    let input: Vec<SparsePolynomial<Fr, ElimTerm>> = shared::katsura_polys(&vars);
    compare("elim/katsura/4", n, input);
}

#[test]
#[ignore]
fn regression_elim_katsura_5() {
    let n = 5;
    let vars = shared::mk_vars("k", n);
    let input: Vec<SparsePolynomial<Fr, ElimTerm>> = shared::katsura_polys(&vars);
    compare("elim/katsura/5", n, input);
}

#[test]
fn regression_elim_cyclic_3() {
    let n = 3;
    let vars = shared::mk_vars("c", n);
    let input: Vec<SparsePolynomial<Fr, ElimTerm>> = shared::cyclic_polys(&vars);
    compare("elim/cyclic/3", n, input);
}

#[test]
fn regression_elim_cyclic_4() {
    let n = 4;
    let vars = shared::mk_vars("c", n);
    let input: Vec<SparsePolynomial<Fr, ElimTerm>> = shared::cyclic_polys(&vars);
    compare("elim/cyclic/4", n, input);
}

#[test]
#[ignore]
fn regression_elim_cyclic_5() {
    let n = 5;
    let vars = shared::mk_vars("c", n);
    let input: Vec<SparsePolynomial<Fr, ElimTerm>> = shared::cyclic_polys(&vars);
    compare("elim/cyclic/5", n, input);
}

// ---------------------------------------------------------------------------
// ElimTerm matrix — mixed-qualifier vars. These exercise the real
// elimination ordering, where `Private+Uniform` vars sort before
// `Public+Nonuniform` vars regardless of degree.
// ---------------------------------------------------------------------------

/// Mirrors `buchberger::test_maple` (the Maplesoft LexDeg fixture), but
/// asserts that both backends produce the *same* reduced GB rather than
/// matching a hand-written reference. Keeps legacy and ark-gb in
/// lock-step on a small elimination-order example with mixed qualifiers.
#[test]
fn regression_elim_maple() {
    use crate::analyses::groebner::sparsepoly::elim_sparse_poly;

    let t = elim_var("t");
    let x = noelim_var("x");
    let y = noelim_var("y");
    let num_vars = 3;

    // Ideal (verbatim from buchberger::test_maple):
    //   f1 = t^2 y - 2 t + y
    //   f2 = t^2 x + t^2 + x - 1
    let f1: SparsePolynomial<Fr, ElimTerm> = elim_sparse_poly(vec![
        (Fr::one(), vec![(&t, 2), (&y, 1)]),
        (-Fr::one().double(), vec![(&t, 1)]),
        (Fr::one(), vec![(&y, 1)]),
    ]);
    let f2: SparsePolynomial<Fr, ElimTerm> = elim_sparse_poly(vec![
        (Fr::one(), vec![(&t, 2), (&x, 1)]),
        (Fr::one(), vec![(&t, 2)]),
        (Fr::one(), vec![(&x, 1)]),
        (-Fr::one(), vec![]),
    ]);

    compare("elim/maple", num_vars, vec![f1, f2]);
}

/// Small hand-built ideal with one `elim_var` (`u`) and two `noelim_var`s
/// (`a`, `b`). The two generators interact through `u`, forcing the
/// elimination ordering to actually do work eliminating `u`.
#[test]
fn regression_elim_small_mixed() {
    use crate::analyses::groebner::sparsepoly::elim_sparse_poly;

    let u = elim_var("u");
    let a = noelim_var("a");
    let b = noelim_var("b");
    let num_vars = 3;

    // Generators:
    //   g1 = u^2 - a
    //   g2 = u b - 1
    // The reduced GB should eliminate `u` and produce a relation in `a, b`.
    let g1: SparsePolynomial<Fr, ElimTerm> = elim_sparse_poly(vec![
        (Fr::one(), vec![(&u, 2)]),
        (-Fr::one(), vec![(&a, 1)]),
    ]);
    let g2: SparsePolynomial<Fr, ElimTerm> = elim_sparse_poly(vec![
        (Fr::one(), vec![(&u, 1), (&b, 1)]),
        (-Fr::one(), vec![]),
    ]);

    compare("elim/small_mixed", num_vars, vec![g1, g2]);
}
