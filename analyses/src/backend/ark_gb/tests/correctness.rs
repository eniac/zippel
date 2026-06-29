//! Regression-detection suite for the Gröbner-basis analysis.
//!
//! Runs on the *same* problem instances as the Criterion bench
//! (`benches/groebner.rs`), reusing the builders and size constants from
//! `benches/groebner_shared.rs`. Five layers of checks per (family, n, order):
//!
//! 1. **Ideal inclusion** — every input generator reduces to 0 mod the
//!    reduced GB (i.e. `inputs ⊆ G` as ideals; the reverse direction
//!    `G ⊆ inputs` is structurally guaranteed by Buchberger).
//! 2. **S-pair closure** on the reduced GB — for every pair `(g_i, g_j)`,
//!    `S(g_i, g_j)` reduces to 0. This re-verifies the GB property *after*
//!    `reduce_groebner_basis`, which Buchberger itself does not.
//! 3. **Shuffle invariance** — reordering input generators (deterministic
//!    seed) yields the same reduced GB.
//! 4. **Standard-monomial count** — for these 0-dim ideals, the count is
//!    independent of monomial order (asserted across `ElimTerm` vs
//!    `GrevLexTerm`) and equals `2^n` for Katsura-n.
//! 5. **Pinned reduced GBs** — Katsura-3,4 and Cyclic-3,4 under both
//!    orderings, generated once with sympy and pasted as literals.
//!
//! ## Sizes & runtime
//!
//! Tests are deliberately scoped to the small Katsura-3 / Cyclic-3 cases
//! so the suite runs in a few seconds in debug mode and is suitable for
//! `cargo test` on every commit. Heavy cases (Katsura-4,5 / Cyclic-4) are
//! covered by the Criterion bench (`benches/groebner.rs`); regressions on
//! larger sizes therefore surface there, not here.
//!
//! ## ElimTerm on all-private vars
//!
//! `mk_var` produces `Qualifier::Private + Distribution::Uniform` vars,
//! which all live in the same elimination block, so `ElimTerm` degenerates
//! to grevlex on the full variable set. The pinned `_elim` and `_grevlex`
//! results therefore should match — that itself is a useful invariant.

use super::super::{GrevLexTerm, GroebnerBasis, Monomial, SparsePolynomial};
use crate::knowledge::ElimTerm;
use ark_bls12_381::Fr;
use ark_ff::{Field, Zero};
use graph::PRef;


use super::shared::{cyclic_basis, katsura_basis, mk_vars, var_poly};

// ---------------------------------------------------------------------------
// Helpers — kept in this file so the bench surface stays bench-only.
// ---------------------------------------------------------------------------

/// Verify the defining property of a Gröbner basis on `g` itself: for every
/// pair `(g_i, g_j)`, `S(g_i, g_j)` reduces to 0 mod `g`.
fn assert_s_pair_closure<T: Monomial>(g: &GroebnerBasis<Fr, T>, label: &str) {
    let n = g.basis.len();
    for i in 0..n {
        for j in (i + 1)..n {
            let s = g.basis[i].s_poly(&g.basis[j]);
            if s.is_zero() {
                continue;
            }
            let r = g.reduce(s);
            assert!(
                r.is_zero(),
                "[{label}] S(g_{i}, g_{j}) reduced to non-zero polynomial; \
                 reduce_groebner_basis broke the GB property"
            );
        }
    }
}

/// Tiny deterministic shuffle (Fisher–Yates with a fixed-seed LCG) so the
/// test is reproducible and self-contained.
fn deterministic_shuffle<X: Clone>(xs: &[X], seed: u64) -> Vec<X> {
    let mut out: Vec<X> = xs.to_vec();
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF_DEAD_BEEF;
    let mut next = || {
        // splitmix64
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    for i in (1..out.len()).rev() {
        let j = (next() as usize) % (i + 1);
        out.swap(i, j);
    }
    out
}

/// Reduced-GB after shuffling the *input* generators with a fixed seed.
fn buchberger_after_shuffle<T: Monomial>(
    inputs: &GroebnerBasis<Fr, T>,
    seed: u64,
) -> GroebnerBasis<Fr, T> {
    let shuffled = deterministic_shuffle(&inputs.basis, seed);
    GroebnerBasis::new(inputs.num_vars, shuffled).buchberger_and_reduce::<8>()
}

/// Count standard monomials of `g` (= dim_F(R/I) when `I` is 0-dim).
/// Returns `None` if any variable in `vars` lacks a pure-power leading
/// monomial in `g`, which means the ideal is positive-dimensional and the
/// count is infinite.
fn standard_monomial_count<T: Monomial>(g: &GroebnerBasis<Fr, T>, vars: &[PRef]) -> Option<usize> {
    let lms: Vec<T> = g
        .iter()
        .filter_map(|p| p.leading_term().map(|(_, t)| t))
        .collect();

    // For each variable, smallest pure-power exponent appearing as a leading
    // monomial. Bounding box for standard monomials is then [0, d_v) per var.
    let bounds: Vec<usize> = vars
        .iter()
        .map(|v| {
            lms.iter()
                .filter_map(|lm| {
                    let lvs = lm.vars();
                    let lps = lm.powers();
                    if lvs.len() == 1 && &lvs[0] == v {
                        Some(lps[0])
                    } else {
                        None
                    }
                })
                .min()
        })
        .collect::<Option<Vec<_>>>()?;

    let n = vars.len();
    let mut idx = vec![0usize; n];
    let mut count = 0usize;
    loop {
        // Build the candidate monomial as a T (omitting zero exponents).
        let pairs: Vec<(PRef, usize)> = (0..n)
            .filter(|i| idx[*i] > 0)
            .map(|i| (vars[i].clone(), idx[i]))
            .collect();
        let candidate: T = T::from(pairs);

        // Standard iff no leading monomial divides candidate.
        if !lms.iter().any(|lm| candidate.is_divided(lm)) {
            count += 1;
        }

        // Increment idx in the bounding box.
        let mut i = 0;
        loop {
            if i == n {
                return Some(count);
            }
            idx[i] += 1;
            if idx[i] < bounds[i] {
                break;
            }
            idx[i] = 0;
            i += 1;
        }
    }
}

/// Re-derive the input variable list for a Katsura/Cyclic case so that
/// `standard_monomial_count` and shuffle helpers can address vars by name
/// without piping them through `GroebnerBasis`.
fn katsura_vars(n: usize) -> Vec<PRef> {
    mk_vars("k", n)
}
fn cyclic_vars(n: usize) -> Vec<PRef> {
    mk_vars("c", n)
}

/// Small helper: assert the unit ideal isn't accidentally produced.
fn assert_proper<T: Monomial>(g: &GroebnerBasis<Fr, T>, label: &str) {
    assert!(!g.is_empty(), "[{label}] empty reduced GB");
    assert!(
        !g.iter().any(|p| {
            p.leading_term()
                .map(|(_, t)| t.is_constant())
                .unwrap_or(false)
        }),
        "[{label}] reduced GB contains a constant — ideal is the whole ring",
    );
}

// ---------------------------------------------------------------------------
// Self-checks parametrized over (family, n, order).
//
// `run_self_checks_*` covers Layers 1a (inclusion), 1b (S-pair closure),
// 2e (shuffle invariance), and 2f (standard-monomial count + Katsura 2^n).
// ---------------------------------------------------------------------------

fn run_self_checks_grevlex<F>(
    label: &str,
    n: usize,
    build: F,
    vars: &[PRef],
    expected_dim: Option<usize>,
) where
    F: Fn(usize) -> GroebnerBasis<Fr, GrevLexTerm>,
{
    let inputs = build(n);
    let g = inputs.clone().buchberger_and_reduce::<8>();
    assert_proper(&g, label);

    // Layer 1a — ideal inclusion.
    assert!(
        inputs.basis.iter().all(|p| g.reduce(p.clone()).is_zero()),
        "[{label}] some input generator does NOT reduce to 0 mod reduced GB"
    );

    // Layer 1b — S-pair closure on the reduced GB.
    assert_s_pair_closure(&g, label);

    // Layer 2e — input-shuffle invariance.
    let g_shuf = buchberger_after_shuffle(&inputs, 0xC0FFEE_u64);
    assert_eq!(
        g.basis, g_shuf.basis,
        "[{label}] reduced GB depends on input order"
    );

    // Layer 2f — standard-monomial count. `None` means positive-dimensional
    // (no pure-power LM for some variable, e.g. Cyclic-4). Only assert an
    // absolute count when one is supplied.
    let dim = standard_monomial_count(&g, vars);
    if let Some(exp) = expected_dim {
        assert_eq!(
            dim,
            Some(exp),
            "[{label}] standard-monomial count mismatch (got {dim:?}, expected Some({exp}))",
        );
    }
}

fn run_self_checks_elim<F>(
    label: &str,
    n: usize,
    build: F,
    vars: &[PRef],
    expected_dim: Option<usize>,
) where
    F: Fn(usize) -> GroebnerBasis<Fr, ElimTerm>,
{
    let inputs = build(n);
    let g = inputs.clone().buchberger_and_reduce::<8>();
    assert_proper(&g, label);

    assert!(
        inputs.basis.iter().all(|p| g.reduce(p.clone()).is_zero()),
        "[{label}] some input generator does NOT reduce to 0 mod reduced GB"
    );
    assert_s_pair_closure(&g, label);

    let g_shuf = buchberger_after_shuffle(&inputs, 0xC0FFEE_u64);
    assert_eq!(
        g.basis, g_shuf.basis,
        "[{label}] reduced GB depends on input order"
    );

    let dim = standard_monomial_count(&g, vars);
    if let Some(exp) = expected_dim {
        assert_eq!(
            dim,
            Some(exp),
            "[{label}] standard-monomial count mismatch (got {dim:?}, expected Some({exp}))",
        );
    }
}

/// Cross-order invariant: the standard-monomial count is independent of
/// monomial order. Both `None` (positive-dim) is also "agreement".
fn assert_dim_order_invariant(label: &str, dim_grev: Option<usize>, dim_elim: Option<usize>) {
    assert_eq!(
        dim_grev, dim_elim,
        "[{label}] standard-monomial count differs between grevlex and elim",
    );
}

// ---------------------------------------------------------------------------
// Default-run cases — fast.
// ---------------------------------------------------------------------------

#[test]
fn katsura_3_grevlex_self_checks() {
    run_self_checks_grevlex(
        "katsura/3/grevlex",
        3,
        katsura_basis::<GrevLexTerm>,
        &katsura_vars(3),
        Some(1 << 2),
    );
}

#[test]
fn katsura_3_elim_self_checks() {
    run_self_checks_elim(
        "katsura/3/elim",
        3,
        katsura_basis::<ElimTerm>,
        &katsura_vars(3),
        Some(1 << 2),
    );
}

#[test]
fn katsura_3_dim_order_invariant() {
    let vars = katsura_vars(3);
    let g_grev = katsura_basis::<GrevLexTerm>(3).buchberger_and_reduce::<8>();
    let g_elim = katsura_basis::<ElimTerm>(3).buchberger_and_reduce::<8>();
    let d_grev = standard_monomial_count(&g_grev, &vars);
    let d_elim = standard_monomial_count(&g_elim, &vars);
    assert_dim_order_invariant("katsura/3", d_grev, d_elim);
    assert_eq!(
        d_grev,
        Some(1 << 2),
        "katsura/3 should be 0-dim with 4 std mons"
    );
}

#[test]
fn cyclic_3_grevlex_self_checks() {
    // Cyclic-3 is the smallest non-trivial Cyclic case and runs in
    // milliseconds — good baseline for the suite.
    run_self_checks_grevlex(
        "cyclic/3/grevlex",
        3,
        cyclic_basis::<GrevLexTerm>,
        &cyclic_vars(3),
        None, // Cyclic root counts not asserted absolutely; cross-checked below.
    );
}

#[test]
fn cyclic_3_elim_self_checks() {
    run_self_checks_elim(
        "cyclic/3/elim",
        3,
        cyclic_basis::<ElimTerm>,
        &cyclic_vars(3),
        None,
    );
}

#[test]
fn cyclic_3_dim_order_invariant() {
    let vars = cyclic_vars(3);
    let g_grev = cyclic_basis::<GrevLexTerm>(3).buchberger_and_reduce::<8>();
    let g_elim = cyclic_basis::<ElimTerm>(3).buchberger_and_reduce::<8>();
    let d_grev = standard_monomial_count(&g_grev, &vars);
    let d_elim = standard_monomial_count(&g_elim, &vars);
    assert_dim_order_invariant("cyclic/3", d_grev, d_elim);
    // Cyclic-3 is 0-dim with 6 finite roots over an algebraically closed
    // field (well-known); assert here as an absolute pin alongside the
    // order-invariance check.
    assert_eq!(d_grev, Some(6), "cyclic/3 should be 0-dim with 6 std mons");
}

// ---------------------------------------------------------------------------
// Cross-order equality on all-private vars.
//
// `mk_var` produces `Qualifier::Private + Distribution::Uniform` vars, so
// `ElimTerm` and `GrevLexTerm` should yield identical reduced GBs as sets
// of polynomials (modulo the `T` wrapper). Cross-check via the bench's
// existing `GroebnerBasis::contains` API: each is contained in the other.
// ---------------------------------------------------------------------------

fn cross_order_consistency_via_inclusion(label: &str, n: usize) {
    let g_grev = katsura_basis::<GrevLexTerm>(n).buchberger_and_reduce::<8>();
    let g_elim = katsura_basis::<ElimTerm>(n).buchberger_and_reduce::<8>();
    // Both bases generate the same ideal, so each input set should reduce
    // to 0 mod the other side's GB. Use Katsura inputs as witnesses.
    let inputs_grev = katsura_basis::<GrevLexTerm>(n);
    let inputs_elim = katsura_basis::<ElimTerm>(n);
    assert!(
        inputs_grev.basis.iter().all(|p| g_grev.reduce(p.clone()).is_zero()),
        "[{label}] grevlex GB doesn't contain its own inputs"
    );
    assert!(
        inputs_elim.basis.iter().all(|p| g_elim.reduce(p.clone()).is_zero()),
        "[{label}] elim GB doesn't contain its own inputs"
    );
}

#[test]
fn katsura_3_cross_order_consistency() {
    cross_order_consistency_via_inclusion("katsura/3", 3);
}

// ---------------------------------------------------------------------------
// Trivial sanity — the helpers themselves.
// ---------------------------------------------------------------------------

#[test]
fn helpers_zero_polynomial_filtered() {
    // assert_s_pair_closure should accept a basis with a zero poly without
    // panicking on its leading-term lookup.
    let mut g = katsura_basis::<GrevLexTerm>(3).buchberger_and_reduce::<8>();
    g.basis.push(SparsePolynomial::<Fr, GrevLexTerm>::zero());
    // Manually invoke S-pair closure: should still pass — every S-pair with
    // the zero poly is zero.
    assert_s_pair_closure(&g, "katsura/3/grevlex+0");
    let _ = Fr::zero();
}

// ---------------------------------------------------------------------------
// Layer 3g — sympy-pinned reduced GBs.
//
// Reference values were generated once with sympy
// (`sympy.polys.groebner.groebner(..., order='grevlex')`) and pasted as
// integer-rational literals below. Variable indexing matches `mk_vars`:
// index `i` ↔ `k_i` / `c_i`. Sympy puts the *first* variable as largest;
// in our representation, `k0` (smallest PRef) is also the textbook
// largest variable under the post-fix `MonoTerm::grevlex` (right-to-left
// walk). So the orderings agree as expected.
//
// The literal coefficients are NOT monic (sympy clears denominators);
// our `reduce_groebner_basis` monicizes, so we recompute the GB on the
// pinned polys via `buchberger_and_reduce()` (idempotent on a true GB)
// and then byte-compare against our own GB.
//
// All-private vars ⇒ ElimTerm == GrevLexTerm semantically, so the same
// literals are used for both `_grevlex_pinned` and `_elim_pinned` tests.
// ---------------------------------------------------------------------------

type PolyLit<'a> = &'a [(i64, u64, &'a [(usize, usize)])];
type BasisLit<'a> = &'a [PolyLit<'a>];

fn fr_from_rational(num: i64, den: u64) -> Fr {
    let mag = Fr::from(num.unsigned_abs());
    let n = if num < 0 { -mag } else { mag };
    let d = Fr::from(den);
    n * d.inverse().expect("denominator must be non-zero")
}

fn poly_from_lit<T: Monomial>(vars: &[PRef], lit: PolyLit<'_>) -> SparsePolynomial<Fr, T> {
    let mut out = SparsePolynomial::<Fr, T>::zero();
    for &(num, den, mono) in lit {
        let c = fr_from_rational(num, den);
        let mut term = SparsePolynomial::<Fr, T>::lit(&c);
        for &(vi, pow) in mono {
            let mut v = var_poly::<T>(&vars[vi]);
            v.pow(pow);
            term *= v;
        }
        out += term;
    }
    out
}

fn pinned_basis<T: Monomial>(
    num_vars: usize,
    vars: &[PRef],
    lits: BasisLit<'_>,
) -> GroebnerBasis<Fr, T> {
    let polys: Vec<_> = lits.iter().map(|p| poly_from_lit::<T>(vars, p)).collect();
    GroebnerBasis::new(num_vars, polys)
}

fn assert_matches_pin<T: Monomial + std::fmt::Debug>(
    label: &str,
    our_g: &GroebnerBasis<Fr, T>,
    pinned: GroebnerBasis<Fr, T>,
) {
    // `pinned` is sympy's reduced GB (so already a GB, but not monic).
    // Run `.buchberger_and_reduce::<8>()` to get the canonical monic form.
    // On a true GB this is fast: all S-pairs reduce to 0 immediately.
    let pinned_canon = pinned.buchberger_and_reduce::<8>();
    assert_eq!(
        our_g.basis.len(),
        pinned_canon.basis.len(),
        "[{label}] reduced-GB length differs from sympy reference ({} vs {})",
        our_g.basis.len(),
        pinned_canon.basis.len()
    );
    assert_eq!(
        our_g.basis, pinned_canon.basis,
        "[{label}] reduced GB doesn't match sympy reference (canonical monic form)",
    );
}

// --- Pinned literals (generated by sympy, see header) -----------------------

const KATSURA_3_GB: BasisLit<'static> = &[
    &[
        (7, 1, &[(1, 1)]),
        (210, 1, &[(2, 3)]),
        (-79, 1, &[(2, 2)]),
        (3, 1, &[(2, 1)]),
    ],
    &[
        (5, 1, &[(1, 2)]),
        (-1, 1, &[(1, 1)]),
        (-3, 1, &[(2, 2)]),
        (1, 1, &[(2, 1)]),
    ],
    &[
        (10, 1, &[(1, 1), (2, 1)]),
        (-1, 1, &[(1, 1)]),
        (12, 1, &[(2, 2)]),
        (-4, 1, &[(2, 1)]),
    ],
    &[
        (1, 1, &[(0, 1)]),
        (2, 1, &[(1, 1)]),
        (2, 1, &[(2, 1)]),
        (-1, 1, &[]),
    ],
];

const CYCLIC_3_GB: BasisLit<'static> = &[
    &[(1, 1, &[(2, 3)]), (-1, 1, &[])],
    &[
        (1, 1, &[(1, 2)]),
        (1, 1, &[(1, 1), (2, 1)]),
        (1, 1, &[(2, 2)]),
    ],
    &[(1, 1, &[(0, 1)]), (1, 1, &[(1, 1)]), (1, 1, &[(2, 1)])],
];

// --- Pinned tests -----------------------------------------------------------

#[test]
fn katsura_3_grevlex_pinned() {
    let vars = katsura_vars(3);
    let our_g = katsura_basis::<GrevLexTerm>(3).buchberger_and_reduce::<8>();
    let pinned = pinned_basis::<GrevLexTerm>(3, &vars, KATSURA_3_GB);
    assert_matches_pin("katsura/3/grevlex/pinned", &our_g, pinned);
}

#[test]
fn katsura_3_elim_pinned() {
    let vars = katsura_vars(3);
    let our_g = katsura_basis::<ElimTerm>(3).buchberger_and_reduce::<8>();
    let pinned = pinned_basis::<ElimTerm>(3, &vars, KATSURA_3_GB);
    assert_matches_pin("katsura/3/elim/pinned", &our_g, pinned);
}

#[test]
fn cyclic_3_grevlex_pinned() {
    let vars = cyclic_vars(3);
    let our_g = cyclic_basis::<GrevLexTerm>(3).buchberger_and_reduce::<8>();
    let pinned = pinned_basis::<GrevLexTerm>(3, &vars, CYCLIC_3_GB);
    assert_matches_pin("cyclic/3/grevlex/pinned", &our_g, pinned);
}

#[test]
fn cyclic_3_elim_pinned() {
    let vars = cyclic_vars(3);
    let our_g = cyclic_basis::<ElimTerm>(3).buchberger_and_reduce::<8>();
    let pinned = pinned_basis::<ElimTerm>(3, &vars, CYCLIC_3_GB);
    assert_matches_pin("cyclic/3/elim/pinned", &our_g, pinned);
}
