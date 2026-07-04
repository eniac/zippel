//! Regression-detection suite for the Gröbner-basis analysis.
//!
//! Runs on the *same* problem instances as the Criterion bench
//! (`benches/groebner.rs`), reusing the builders and size constants from
//! `tests/shared.rs`. Five layers of checks per (family, n, order):
//!
//! 1. **Ideal inclusion** — every input generator reduces to 0 mod the
//!    reduced GB (i.e. `inputs ⊆ G` as ideals; the reverse direction
//!    `G ⊆ inputs` is structurally guaranteed by Buchberger).
//! 2. **S-pair closure** on the reduced GB — for every pair `(g_i, g_j)`,
//!    `S(g_i, g_j)` reduces to 0. This re-verifies the GB property *after*
//!    `compute_gb`, which Buchberger itself does not.
//! 3. **Shuffle invariance** — reordering input generators (deterministic
//!    seed) yields the same reduced GB.
//! 4. **Standard-monomial count** — for these 0-dim ideals, the count is
//!    independent of monomial order and equals `2^n` for Katsura-n.
//! 5. **Pinned reduced GBs** — Katsura-3 and Cyclic-3 under both orderings,
//!    generated once with sympy and pasted as literals.
//!
//! ## Sizes & runtime
//!
//! Tests are deliberately scoped to the small Katsura-3 / Cyclic-3 cases
//! so the suite runs in a few seconds in debug mode and is suitable for
//! `cargo test` on every commit. Heavy cases (Katsura-4,5 / Cyclic-4) are
//! covered by the Criterion bench (`benches/groebner.rs`); regressions on
//! larger sizes therefore surface there, not here.

use crate::PRef;
use crate::backend::ark_gb::ArkGb;
use crate::backend::{GbBackend, GbBasis};
use crate::frontend::{Block, BlockKind, MonoOrder, Monomial, Polynomial};
use ark_bls12_381::Fr;
use ark_ff::{Field, Zero};

use super::shared::{cyclic_polys, katsura_polys, mk_vars};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Find the leading term (monomial, coefficient) of a polynomial under an order.
/// Returns `None` for the zero polynomial.
fn leading_term(p: &Polynomial<Fr>, order: &MonoOrder) -> Option<(Monomial, Fr)> {
    p.terms
        .iter()
        .min_by(|(m1, _), (m2, _)| order.compare(m1, m2))
        .map(|(m, c)| (m.clone(), *c))
}

/// Multiply each term of `p` by `scalar` and `term`.
fn multiply_term_and_scalar(p: &Polynomial<Fr>, scalar: Fr, term: &Monomial) -> Polynomial<Fr> {
    let mut result = Polynomial::zero();
    for (mono, coeff) in &p.terms {
        let new_mono = mono.clone() * term.clone();
        let new_coeff = *coeff * scalar;
        if !new_coeff.is_zero() {
            result.terms.insert(new_mono, new_coeff);
        }
    }
    result
}

/// Compute the S-polynomial of `f` and `g` under `order`.
fn spoly(f: &Polynomial<Fr>, g: &Polynomial<Fr>, order: &MonoOrder) -> Polynomial<Fr> {
    if f.is_zero() || g.is_zero() {
        return Polynomial::zero();
    }
    let (lt_f_mono, lt_f_c) = leading_term(f, order).expect("non-zero checked above");
    let (lt_g_mono, lt_g_c) = leading_term(g, order).expect("non-zero checked above");
    let lcm = lt_f_mono.lcm(&lt_g_mono);
    let mult_f = (lcm.clone() / lt_f_mono).expect("lt_f divides lcm");
    let mult_g = (lcm / lt_g_mono).expect("lt_g divides lcm");
    let s1 = multiply_term_and_scalar(f, lt_g_c, &mult_f);
    let s2 = multiply_term_and_scalar(g, lt_f_c, &mult_g);
    s1 - s2
}

/// Verify the defining property of a Gröbner basis: every S-pair reduces to 0.
fn assert_s_pair_closure(g: &GbBasis<Fr>, label: &str) {
    let n = g.polys.len();
    for i in 0..n {
        for j in (i + 1)..n {
            let s = spoly(&g.polys[i], &g.polys[j], &g.order);
            if s.is_zero() {
                continue;
            }
            let r = crate::backend::reduce(s, &g.polys, &g.order);
            assert!(
                r.is_zero(),
                "[{label}] S(g_{i}, g_{j}) reduced to non-zero polynomial"
            );
        }
    }
}

/// Tiny deterministic shuffle (Fisher–Yates with a fixed-seed LCG).
fn deterministic_shuffle<X: Clone>(xs: &[X], seed: u64) -> Vec<X> {
    let mut out: Vec<X> = xs.to_vec();
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF_DEAD_BEEF;
    let mut next = || {
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

/// Reduced GB after shuffling the input generators with a fixed seed.
fn buchberger_after_shuffle(
    inputs: &[Polynomial<Fr>],
    seed: u64,
    order: &MonoOrder,
) -> GbBasis<Fr> {
    let shuffled = deterministic_shuffle(inputs, seed);
    ArkGb::<Fr>::default().compute_gb(shuffled, order).unwrap()
}

/// Count standard monomials of `g` (= dim_F(R/I) when I is 0-dim).
fn standard_monomial_count(g: &GbBasis<Fr>, vars: &[PRef]) -> Option<usize> {
    let lms: Vec<Monomial> = g
        .polys
        .iter()
        .filter_map(|p| leading_term(p, &g.order).map(|(m, _)| m))
        .collect();

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
        let pairs: Vec<(PRef, usize)> = (0..n)
            .filter(|i| idx[*i] > 0)
            .map(|i| (vars[i].clone(), idx[i]))
            .collect();
        let candidate: Monomial = Monomial::from(pairs);

        if !lms.iter().any(|lm| candidate.is_divided(lm)) {
            count += 1;
        }

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

fn katsura_vars(n: usize) -> Vec<PRef> {
    mk_vars("k", n)
}
fn cyclic_vars(n: usize) -> Vec<PRef> {
    mk_vars("c", n)
}

/// Small helper: assert the unit ideal isn't accidentally produced.
fn assert_proper(g: &GbBasis<Fr>, label: &str) {
    assert!(!g.is_empty(), "[{label}] empty reduced GB");
    assert!(
        !g.polys.iter().any(|p| {
            leading_term(p, &g.order)
                .map(|(m, _)| m.is_constant())
                .unwrap_or(false)
        }),
        "[{label}] reduced GB contains a constant — ideal is the whole ring",
    );
}

/// Build an elim order where all given vars are in the first (elim) block.
fn elim_order(vars: &[PRef]) -> MonoOrder {
    MonoOrder::block(vec![
        Block {
            vars: Some(vars.to_vec()),
            kind: BlockKind::GrevLex,
        },
        Block {
            vars: None,
            kind: BlockKind::GrevLex,
        },
    ])
}

// ---------------------------------------------------------------------------
// Self-checks parametrized over (family, order).
// ---------------------------------------------------------------------------

fn run_self_checks(
    label: &str,
    inputs: Vec<Polynomial<Fr>>,
    vars: &[PRef],
    expected_dim: Option<usize>,
    order: &MonoOrder,
) {
    let backend = ArkGb::<Fr>::default();
    let g = backend.compute_gb(inputs.clone(), order).unwrap();
    assert_proper(&g, label);

    assert!(
        inputs
            .iter()
            .all(|p| crate::backend::reduce(p.clone(), &g.polys, &g.order).is_zero()),
        "[{label}] some input generator does NOT reduce to 0 mod reduced GB"
    );

    assert_s_pair_closure(&g, label);

    let g_shuf = buchberger_after_shuffle(&inputs, 0xC0FFEE_u64, order);
    assert_eq!(
        g.polys, g_shuf.polys,
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

/// Cross-order invariant: the standard-monomial count is independent of order.
fn assert_dim_order_invariant(label: &str, dim_a: Option<usize>, dim_b: Option<usize>) {
    assert_eq!(
        dim_a, dim_b,
        "[{label}] standard-monomial count differs between orders",
    );
}

// ---------------------------------------------------------------------------
// Default-run cases — fast.
// ---------------------------------------------------------------------------

#[test]
fn katsura_3_grevlex_self_checks() {
    let vars = katsura_vars(3);
    run_self_checks(
        "katsura/3/grevlex",
        katsura_polys(&vars),
        &vars,
        Some(1 << 2),
        &MonoOrder::grevlex(),
    );
}

#[test]
fn katsura_3_elim_self_checks() {
    let vars = katsura_vars(3);
    run_self_checks(
        "katsura/3/elim",
        katsura_polys(&vars),
        &vars,
        Some(1 << 2),
        &elim_order(&vars),
    );
}

#[test]
fn katsura_3_dim_order_invariant() {
    let vars = katsura_vars(3);
    let inputs = katsura_polys(&vars);
    let backend = ArkGb::<Fr>::default();
    let g_grev = backend
        .compute_gb(inputs.clone(), &MonoOrder::grevlex())
        .unwrap();
    let g_elim = backend.compute_gb(inputs, &elim_order(&vars)).unwrap();
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
    let vars = cyclic_vars(3);
    run_self_checks(
        "cyclic/3/grevlex",
        cyclic_polys(&vars),
        &vars,
        None,
        &MonoOrder::grevlex(),
    );
}

#[test]
fn cyclic_3_elim_self_checks() {
    let vars = cyclic_vars(3);
    run_self_checks(
        "cyclic/3/elim",
        cyclic_polys(&vars),
        &vars,
        None,
        &elim_order(&vars),
    );
}

#[test]
fn cyclic_3_dim_order_invariant() {
    let vars = cyclic_vars(3);
    let inputs = cyclic_polys(&vars);
    let backend = ArkGb::<Fr>::default();
    let g_grev = backend
        .compute_gb(inputs.clone(), &MonoOrder::grevlex())
        .unwrap();
    let g_elim = backend.compute_gb(inputs, &elim_order(&vars)).unwrap();
    let d_grev = standard_monomial_count(&g_grev, &vars);
    let d_elim = standard_monomial_count(&g_elim, &vars);
    assert_dim_order_invariant("cyclic/3", d_grev, d_elim);
    assert_eq!(d_grev, Some(6), "cyclic/3 should be 0-dim with 6 std mons");
}

// ---------------------------------------------------------------------------
// Cross-order consistency: elim with all-private vars should match grevlex.
// ---------------------------------------------------------------------------

#[test]
fn katsura_3_cross_order_consistency() {
    let vars = katsura_vars(3);
    let inputs = katsura_polys(&vars);
    let backend = ArkGb::<Fr>::default();
    let g_grev = backend
        .compute_gb(inputs.clone(), &MonoOrder::grevlex())
        .unwrap();
    let g_elim = backend
        .compute_gb(inputs.clone(), &elim_order(&vars))
        .unwrap();

    assert!(
        inputs
            .iter()
            .all(|p| crate::backend::reduce(p.clone(), &g_grev.polys, &g_grev.order).is_zero()),
        "grevlex GB doesn't contain its own inputs"
    );
    assert!(
        inputs
            .iter()
            .all(|p| crate::backend::reduce(p.clone(), &g_elim.polys, &g_elim.order).is_zero()),
        "elim GB doesn't contain its own inputs"
    );
}

// ---------------------------------------------------------------------------
// Trivial sanity — the helpers themselves.
// ---------------------------------------------------------------------------

#[test]
fn helpers_zero_polynomial_filtered() {
    let vars = katsura_vars(3);
    let inputs = katsura_polys(&vars);
    let mut g = ArkGb::<Fr>::default()
        .compute_gb(inputs, &MonoOrder::grevlex())
        .unwrap();
    g.polys.push(Polynomial::zero());
    assert_s_pair_closure(&g, "katsura/3/grevlex+0");
}

// ---------------------------------------------------------------------------
// Layer 3g — sympy-pinned reduced GBs.
// ---------------------------------------------------------------------------

type PolyLit<'a> = &'a [(i64, u64, &'a [(usize, usize)])];
type BasisLit<'a> = &'a [PolyLit<'a>];

fn fr_from_rational(num: i64, den: u64) -> Fr {
    let mag = Fr::from(num.unsigned_abs());
    let n = if num < 0 { -mag } else { mag };
    let d = Fr::from(den);
    n * d.inverse().expect("denominator must be non-zero")
}

fn poly_from_lit(vars: &[PRef], lit: PolyLit<'_>) -> Polynomial<Fr> {
    let mut out = Polynomial::<Fr>::zero();
    for &(num, den, mono) in lit {
        let c = fr_from_rational(num, den);
        let mut term = Polynomial::<Fr>::lit(&c);
        for &(vi, pow) in mono {
            let mut v = Polynomial::<Fr>::var(&vars[vi]);
            v.pow(pow);
            term *= v;
        }
        out += term;
    }
    out
}

fn pinned_polys(vars: &[PRef], lits: BasisLit<'_>) -> Vec<Polynomial<Fr>> {
    lits.iter().map(|p| poly_from_lit(vars, p)).collect()
}

/// Normalize each polynomial to monic form (leading coefficient = 1) under
/// `order`. Non-zero polynomials only; zero polynomials are passed through.
fn monic_normalize(polys: Vec<Polynomial<Fr>>, order: &MonoOrder) -> Vec<Polynomial<Fr>> {
    polys
        .into_iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let lt = leading_term(&p, order).expect("non-zero polynomial has a leading term");
            let inv = lt.1.inverse().expect("leading coeff nonzero");
            let mut result = Polynomial::zero();
            for (m, c) in &p.terms {
                result.terms.insert(m.clone(), *c * inv);
            }
            result
        })
        .collect()
}

/// Compare our computed GB directly against the sympy-pinned reference.
/// Both sides are normalized to monic form, then compared as sorted Vecs
/// (order-independent, since `Polynomial` iteration is nondeterministic).
fn assert_matches_reference(
    label: &str,
    our_g: &GbBasis<Fr>,
    pinned: Vec<Polynomial<Fr>>,
    order: &MonoOrder,
) {
    let mut our_norm = monic_normalize(our_g.polys.clone(), &our_g.order);
    let mut pinned_norm = monic_normalize(pinned, order);
    assert_eq!(
        our_norm.len(),
        pinned_norm.len(),
        "[{label}] reduced-GB length differs from sympy reference ({} vs {})",
        our_norm.len(),
        pinned_norm.len()
    );
    // Sort by Display string for deterministic comparison.
    our_norm.sort_by_key(|a| a.to_string());
    pinned_norm.sort_by_key(|a| a.to_string());
    assert_eq!(
        our_norm, pinned_norm,
        "[{label}] reduced GB doesn't match sympy reference (monic form)",
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
    let order = MonoOrder::grevlex();
    let our_g = ArkGb::<Fr>::default()
        .compute_gb(katsura_polys(&vars), &order)
        .unwrap();
    let pinned = pinned_polys(&vars, KATSURA_3_GB);
    assert_matches_reference("katsura/3/grevlex/pinned", &our_g, pinned, &order);
}

#[test]
fn katsura_3_elim_pinned() {
    let vars = katsura_vars(3);
    let order = elim_order(&vars);
    let our_g = ArkGb::<Fr>::default()
        .compute_gb(katsura_polys(&vars), &order)
        .unwrap();
    let pinned = pinned_polys(&vars, KATSURA_3_GB);
    assert_matches_reference("katsura/3/elim/pinned", &our_g, pinned, &order);
}

#[test]
fn cyclic_3_grevlex_pinned() {
    let vars = cyclic_vars(3);
    let order = MonoOrder::grevlex();
    let our_g = ArkGb::<Fr>::default()
        .compute_gb(cyclic_polys(&vars), &order)
        .unwrap();
    let pinned = pinned_polys(&vars, CYCLIC_3_GB);
    assert_matches_reference("cyclic/3/grevlex/pinned", &our_g, pinned, &order);
}

#[test]
fn cyclic_3_elim_pinned() {
    let vars = cyclic_vars(3);
    let order = elim_order(&vars);
    let our_g = ArkGb::<Fr>::default()
        .compute_gb(cyclic_polys(&vars), &order)
        .unwrap();
    let pinned = pinned_polys(&vars, CYCLIC_3_GB);
    assert_matches_reference("cyclic/3/elim/pinned", &our_g, pinned, &order);
}
