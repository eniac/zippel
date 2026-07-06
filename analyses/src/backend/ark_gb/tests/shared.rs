//! Shared Katsura/Cyclic polynomial generators used by the Sage cross-check
//! tests (`tests/sage.rs`) and the correctness suite (`tests/correctness.rs`).
//!
//! Ported from Singular's `polylib.lib` (`proc cyclic`, `proc katsura`,
//! `proc kat_var`).

#![allow(dead_code)]

use crate::Var;
use crate::frontend::Polynomial;
use ark_bls12_381::Fr;
use ark_ff::One;
use backend::ATyp;
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;

// ---------------------------------------------------------------------------
// Bench sizes — used by the Criterion bench (`benches/groebner.rs`).
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
// Variable construction helpers
// ---------------------------------------------------------------------------

pub fn mk_var(name: &str) -> Var {
    Var::from_var(name, NodeIndex::new(0), ATyp::scalar(), Qualifier::Private)
}

pub fn mk_vars(prefix: &str, count: usize) -> Vec<Var> {
    (0..count)
        .map(|i| mk_var(&format!("{prefix}{i}")))
        .collect()
}

// ---------------------------------------------------------------------------
// Cyclic-n — translation of Singular polylib.lib `proc cyclic(int n)`
// ---------------------------------------------------------------------------

pub fn cyclic_polys(vars: &[Var]) -> Vec<Polynomial<Fr>> {
    let n = vars.len();
    assert!(n >= 1, "Cyclic-n requires n >= 1");
    let one = Polynomial::<Fr>::lit(&Fr::one());

    let mut polys = Vec::with_capacity(n);
    for j in 0..n.saturating_sub(1) {
        let mut t = Polynomial::<Fr>::zero();
        for i in 0..n {
            let mut product = one.clone();
            for k in 0..=j {
                product *= Polynomial::<Fr>::var(&vars[(i + k) % n]);
            }
            t += product;
        }
        polys.push(t);
    }
    let mut full = one.clone();
    for var in vars.iter().take(n) {
        full *= Polynomial::<Fr>::var(var);
    }
    polys.push(full - one);
    polys
}

// ---------------------------------------------------------------------------
// Katsura-n — translation of Singular polylib.lib `proc katsura` + `kat_var`
// ---------------------------------------------------------------------------

pub fn katsura_polys(vars: &[Var]) -> Vec<Polynomial<Fr>> {
    let n_arg = vars.len();
    assert!(n_arg >= 1, "Katsura-n requires at least one variable");
    let n = (n_arg - 1) as isize;

    let kat_var = |i: isize| -> Option<Polynomial<Fr>> {
        let ai = i.unsigned_abs();
        if (ai as isize) <= n {
            Some(Polynomial::<Fr>::var(&vars[ai]))
        } else {
            None
        }
    };

    let mut polys = Vec::with_capacity(n_arg);

    let mut lin = Polynomial::<Fr>::zero();
    for i in -n..=n {
        if let Some(v) = kat_var(i) {
            lin += v;
        }
    }
    lin -= Polynomial::<Fr>::lit(&Fr::one());
    polys.push(lin);

    for i in 0..n {
        let mut q = Polynomial::<Fr>::zero();
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
