//! Pinning tests for `Op::*::typ()` invariants.
//!
//! Locks in the Phase-17 fix: polynomial-producing ops must report
//! the correct *polynomial* type, not the underlying coefficient
//! vector's type. If any `Op::X::typ()` regresses to a passthrough
//! (`op.typ()`), `CompletenessAnalysis` and other consumers that
//! resolve `Op::Ref` (notably `TransClos::trans_clos_op`) will
//! compute wrong types and panic or produce bogus results. See
//! `backend/src/op.rs:193-256` and commit `03bee5f`.

use crate::config::ArkBls12_381;
use crate::op::{HOp, Ref, mk};
use crate::{ATyp, ArkConfig, GOp, Op, Value};
use lang::typ::range::CRange;
use petgraph::graph::NodeIndex;
use share::Ctx;

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;

/// Build a constant-valued scalar Op for test fixtures.
fn scalar(v: u64) -> GOp<C> {
    Op::Value(Value::Scalar(F::from(v)))
}

/// Hash-cons helper with the test config.
fn h(op: GOp<C>) -> HOp<C> {
    mk::<C>(op)
}

/// Build an `Op::Ref` carrying an explicit annotated type — mimics
/// how graph-builder-produced ops feed into `typ()` consumers.
fn ref_typ(t: ATyp) -> GOp<C> {
    Op::Ref(Ref::new(NodeIndex::new(0)), t)
}

// ───────── Op::Poly ─────────

#[test]
fn poly_typ_from_vec_of_k_scalars_is_uni_k_minus_1() {
    let coefs: Vec<_> = (0..4).map(|i| h(scalar(i))).collect();
    let vec4: GOp<C> = Op::Vec(coefs);
    let poly: GOp<C> = Op::Poly(h(vec4));
    assert_eq!(poly.typ(), ATyp::uni(3));
}

#[test]
fn poly_typ_of_singleton_vec_is_uni_0() {
    let vec1: GOp<C> = Op::Vec(vec![h(scalar(7))]);
    let poly: GOp<C> = Op::Poly(h(vec1));
    assert_eq!(poly.typ(), ATyp::uni(0));
}

#[test]
fn poly_typ_is_identity_on_uni() {
    // Already-a-poly child: preserve the poly type.
    let inner = ref_typ(ATyp::uni(5));
    let poly: GOp<C> = Op::Poly(h(inner));
    assert_eq!(poly.typ(), ATyp::uni(5));
}

// ───────── Op::Mle ─────────

#[test]
fn mle_typ_from_vec_of_2_to_n_is_mle_n() {
    for n in 1..=5 {
        let k = 1usize << n;
        let vals: Vec<_> = (0..k as u64).map(|i| h(scalar(i))).collect();
        let vec: GOp<C> = Op::Vec(vals);
        let mle: GOp<C> = Op::Mle(h(vec));
        assert_eq!(
            mle.typ(),
            ATyp::mle(n),
            "mle over Vec<_, {}> should be Mle({})",
            k,
            n
        );
    }
}

#[test]
fn mle_typ_is_identity_on_mle() {
    let inner = ref_typ(ATyp::mle(3));
    let mle: GOp<C> = Op::Mle(h(inner));
    assert_eq!(mle.typ(), ATyp::mle(3));
}

#[test]
fn mle_typ_fallback_on_non_power_of_two() {
    // Defensive: a non-power-of-2 vec is left as-is rather than
    // silently rounded.
    let vec3: GOp<C> = Op::Vec((0..3).map(|i| h(scalar(i))).collect());
    let mle: GOp<C> = Op::Mle(h(vec3));
    assert_eq!(mle.typ(), ATyp::vec(&ATyp::scalar(), 3));
}

// ───────── Op::Coef ─────────

#[test]
fn coef_typ_of_uni_m_is_vec_m_plus_1() {
    let inner = ref_typ(ATyp::uni(4));
    let coef: GOp<C> = Op::Coef(h(inner));
    assert_eq!(coef.typ(), ATyp::vec(&ATyp::scalar(), 5));
}

#[test]
fn coef_typ_of_mle_n_is_vec_2_to_n() {
    let inner = ref_typ(ATyp::mle(3));
    let coef: GOp<C> = Op::Coef(h(inner));
    assert_eq!(coef.typ(), ATyp::vec(&ATyp::scalar(), 8));
}

#[test]
fn coef_typ_of_vpoly_is_binomial_sized_vec() {
    // VPoly(n=2, m=2) has C(4, 2) = 6 coefficients.
    let inner = ref_typ(ATyp::vpoly(2, 2));
    let coef: GOp<C> = Op::Coef(h(inner));
    assert_eq!(coef.typ(), ATyp::vec(&ATyp::scalar(), 6));

    // VPoly(n=3, m=1) has C(4, 3) = 4 (scalar + 3 linear).
    let inner = ref_typ(ATyp::vpoly(3, 1));
    let coef: GOp<C> = Op::Coef(h(inner));
    assert_eq!(coef.typ(), ATyp::vec(&ATyp::scalar(), 4));
}

// ───────── Op::Ifft / Op::Fft ─────────

#[test]
fn ifft_typ_matches_poly_shape() {
    // Ifft and Poly both lower Vec<F, k> → Uni(k-1).
    let vec8: GOp<C> = Op::Vec((0..8).map(|i| h(scalar(i))).collect());
    let ifft: GOp<C> = Op::Ifft(h(vec8));
    assert_eq!(ifft.typ(), ATyp::uni(7));
}

#[test]
fn fft_typ_is_vec_of_coef_count() {
    let inner = ref_typ(ATyp::uni(6));
    let fft: GOp<C> = Op::Fft(h(inner));
    assert_eq!(fft.typ(), ATyp::vec(&ATyp::scalar(), 7));
}

// ───────── Regression guard: Op::Eval routes through correct poly shape ─────────

#[test]
fn eval_of_mle_full_shape_is_scalar() {
    // The Phase-17 failure mode: if Op::Mle::typ() passed through
    // its child vec type, Op::Eval would fall through to `_ => x_typ`
    // and return [Scalar; k] instead of Scalar.
    let evals: Vec<_> = (0..16).map(|i| h(scalar(i))).collect();
    let mle: GOp<C> = Op::Mle(h(Op::Vec(evals))); // Mle(4)
    let xs: Vec<_> = (0..4).map(|_| h(scalar(0))).collect();
    let xs_vec: GOp<C> = Op::Vec(xs);
    let eval: GOp<C> = Op::Evaluate(h(mle), h(xs_vec)); // full evaluation
    assert_eq!(eval.typ(), ATyp::scalar());
}

#[test]
fn eval_of_mle_partial_shape_is_residual_mle() {
    // Partial evaluation at k < n points keeps an Mle(n-k).
    let evals: Vec<_> = (0..16).map(|i| h(scalar(i))).collect();
    let mle: GOp<C> = Op::Mle(h(Op::Vec(evals))); // Mle(4)
    let xs_vec: GOp<C> = Op::Vec(vec![h(scalar(0))]); // |xs| = 1, k < n
    let eval: GOp<C> = Op::Evaluate(h(mle), h(xs_vec));
    assert_eq!(eval.typ(), ATyp::mle(3));
}

// ───────── Op::Vec heterogeneity diagnostic ─────────

#[test]
#[should_panic(expected = "Vector operands must be of the same type")]
fn vec_heterogeneous_children_panic_with_diagnostic() {
    // Locks the improved diagnostic added while tracking Phase-17
    // down. Mixing a [Scalar; 2] with a Scalar must fail loudly.
    let inner_vec: GOp<C> = Op::Vec(vec![h(scalar(1)), h(scalar(2))]);
    let outer: GOp<C> = Op::Vec(vec![h(inner_vec), h(scalar(3))]);
    let _ = outer.typ();
}

// =============================================================================
// Comprehensive Op::typ() shape pinning under the phase-14 m+1 convention.
// These tests sweep multiple sizes for each polynomial-producing or
// polynomial-consuming Op arm. See docs/poly-encoding.md (and the
// `poly_typ_from_vec` / `coef_typ_from_poly` helpers in op.rs) for the
// canonical shape rules.
// =============================================================================

// Build a `Vec<Scalar, k>` Op via the Op::Vec constructor.
fn vec_scalars(k: usize) -> GOp<C> {
    let elems: Vec<_> = (0..k as u64).map(|i| h(scalar(i))).collect();
    Op::Vec(elems)
}

// ───────── Op::Fft sweep — Uni(m) → Vec<Scalar, m+1> ─────────

#[test]
fn fft_uni_returns_vec_scalar_m_plus_1() {
    for m in [0usize, 1, 2, 3, 4, 7, 8] {
        let inner = ref_typ(ATyp::uni(m));
        let fft: GOp<C> = Op::Fft(h(inner));
        assert_eq!(
            fft.typ(),
            ATyp::vec_scalar(m + 1),
            "Op::Fft(Uni({})) should be Vec<Scalar, {}>",
            m,
            m + 1
        );
    }
}

// ───────── Op::Coef sweep — Uni / Mle / VPoly → Vec<Scalar, size> ─────────

#[test]
fn coef_uni_returns_vec_scalar_m_plus_1() {
    for m in [0usize, 1, 2, 3, 4, 7, 8] {
        let inner = ref_typ(ATyp::uni(m));
        let coef: GOp<C> = Op::Coef(h(inner));
        assert_eq!(
            coef.typ(),
            ATyp::vec_scalar(m + 1),
            "Op::Coef(Uni({})) should be Vec<Scalar, {}>",
            m,
            m + 1
        );
    }
}

#[test]
fn coef_mle_returns_vec_scalar_2_to_n() {
    for n in [0usize, 1, 2, 3, 4] {
        let inner = ref_typ(ATyp::mle(n));
        let coef: GOp<C> = Op::Coef(h(inner));
        assert_eq!(
            coef.typ(),
            ATyp::vec_scalar(1usize << n),
            "Op::Coef(Mle({})) should be Vec<Scalar, {}>",
            n,
            1usize << n
        );
    }
}

#[test]
fn coef_vpoly_returns_vec_scalar_binomial_sized() {
    // VPoly(n, m) has C(n+m, n) coefficients.
    let cases: &[(usize, usize, usize)] = &[
        (1, 2, 3),  // C(3, 1) = 3
        (2, 1, 3),  // C(3, 2) = 3
        (2, 2, 6),  // C(4, 2) = 6
        (3, 1, 4),  // C(4, 3) = 4
        (3, 2, 10), // C(5, 3) = 10
    ];
    for (n, m, expected) in cases {
        let inner = ref_typ(ATyp::vpoly(*n, *m));
        let coef: GOp<C> = Op::Coef(h(inner));
        assert_eq!(
            coef.typ(),
            ATyp::vec_scalar(*expected),
            "Op::Coef(VPoly({}, {})) should be Vec<Scalar, {}>",
            n,
            m,
            expected
        );
    }
}

// ───────── Op::Ifft sweep — Vec<Scalar, k> → Uni(k-1) ─────────

#[test]
fn ifft_vec_scalar_returns_uni_k_minus_1() {
    for k in [1usize, 2, 4, 8, 16] {
        let v = vec_scalars(k);
        let ifft: GOp<C> = Op::Ifft(h(v));
        assert_eq!(
            ifft.typ(),
            ATyp::uni(k - 1),
            "Op::Ifft(Vec<Scalar, {}>) should be Uni({})",
            k,
            k - 1
        );
    }
}

// ───────── Op::Poly sweep — Vec<Scalar, k> → Uni(k-1) ─────────

#[test]
fn poly_vec_scalar_returns_uni_k_minus_1() {
    for k in [1usize, 2, 3, 4, 5] {
        let v = vec_scalars(k);
        let poly: GOp<C> = Op::Poly(h(v));
        assert_eq!(
            poly.typ(),
            ATyp::uni(k - 1),
            "Op::Poly(Vec<Scalar, {}>) should be Uni({})",
            k,
            k - 1
        );
    }
}

// ───────── Op::Interpolate sweep — points/evals : Vec<Scalar, k> → Uni(k-1) ─────────
//
// This is the arm fixed in this PR: previously returned `Uni(k)` (one too
// large), which disagreed with both `value_interpolate` (produces a
// `DensePolynomial` with `k` coefficients = max degree `k-1`) and the
// lang-side `infer()` rule (returns `Poly<F, 1, k-1>`).

#[test]
fn interpolate_two_vec_scalars_returns_uni_k_minus_1() {
    for k in [1usize, 2, 3, 4, 5] {
        let points = vec_scalars(k);
        let evals = vec_scalars(k);
        let interp: GOp<C> = Op::Interpolate(h(points), h(evals));
        assert_eq!(
            interp.typ(),
            ATyp::uni(k - 1),
            "Op::Interpolate(Vec<Scalar, {}>, Vec<Scalar, {}>) should be Uni({})",
            k,
            k,
            k - 1
        );
    }
}

// ───────── Op::Mle sweep — Vec<Scalar, 2^n> → Mle(n) ─────────

#[test]
fn mle_vec_scalar_pow2_returns_mle_n() {
    for n in [1usize, 2, 3, 4] {
        let k = 1usize << n;
        let v = vec_scalars(k);
        let mle: GOp<C> = Op::Mle(h(v));
        assert_eq!(
            mle.typ(),
            ATyp::mle(n),
            "Op::Mle(Vec<Scalar, {}>) should be Mle({})",
            k,
            n
        );
    }
}

#[test]
fn mle_vec_scalar_non_pow2_falls_through() {
    // Non-power-of-two inputs hit the defensive `other => other` fallback
    // in `Op::Mle`'s arm of `Op::typ`. Pinned so future refactors don't
    // silently switch to panicking or rounding.
    for k in [3usize, 5, 6, 7, 9] {
        let v = vec_scalars(k);
        let mle: GOp<C> = Op::Mle(h(v));
        assert_eq!(
            mle.typ(),
            ATyp::vec_scalar(k),
            "Op::Mle(Vec<Scalar, {}>) is non-pow2: typ() should fall through to the input vec type",
            k
        );
    }
}

// ───────── Op::Evaluate sweep ─────────

#[test]
fn evaluate_uni_at_vec_k_returns_vec_scalar_k() {
    // Batched univariate evaluation: Uni(m) at Vec<Scalar, k> → Vec<Scalar, k>.
    for (m, k) in [(0usize, 1usize), (2, 3), (3, 1), (4, 4), (8, 5)] {
        let p = ref_typ(ATyp::uni(m));
        let xs = vec_scalars(k);
        let eval: GOp<C> = Op::Evaluate(h(p), h(xs));
        assert_eq!(
            eval.typ(),
            ATyp::vec_scalar(k),
            "Op::Evaluate(Uni({}), Vec<Scalar, {}>) should be Vec<Scalar, {}>",
            m,
            k,
            k
        );
    }
}

#[test]
fn evaluate_vpoly_full_returns_scalar() {
    // Full multivariate evaluation: VPoly(n, m) at Vec<Scalar, n> → Scalar.
    for (n, m) in [(2usize, 1usize), (2, 3), (3, 2), (4, 1)] {
        let p = ref_typ(ATyp::vpoly(n, m));
        let xs = vec_scalars(n);
        let eval: GOp<C> = Op::Evaluate(h(p), h(xs));
        assert_eq!(
            eval.typ(),
            ATyp::scalar(),
            "Op::Evaluate(VPoly({}, {}), Vec<Scalar, {}>) should be Scalar",
            n,
            m,
            n
        );
    }
}

#[test]
fn evaluate_vpoly_partial_returns_residual_vpoly() {
    // Partial multivariate evaluation: VPoly(n, m) at Vec<Scalar, k>, k < n
    // → VPoly(n - k, m).
    let cases: &[(usize, usize, usize)] = &[(3, 2, 1), (3, 2, 2), (4, 3, 2), (5, 1, 3)];
    for (n, m, k) in cases {
        let p = ref_typ(ATyp::vpoly(*n, *m));
        let xs = vec_scalars(*k);
        let eval: GOp<C> = Op::Evaluate(h(p), h(xs));
        assert_eq!(
            eval.typ(),
            ATyp::vpoly(*n - *k, *m),
            "Op::Evaluate(VPoly({}, {}), Vec<Scalar, {}>) should be VPoly({}, {})",
            n,
            m,
            k,
            n - k,
            m
        );
    }
}

#[test]
fn evaluate_mle_full_returns_scalar() {
    // Full MLE evaluation: Mle(n) at Vec<Scalar, n> → Scalar.
    for n in [1usize, 2, 3, 4] {
        let p = ref_typ(ATyp::mle(n));
        let xs = vec_scalars(n);
        let eval: GOp<C> = Op::Evaluate(h(p), h(xs));
        assert_eq!(
            eval.typ(),
            ATyp::scalar(),
            "Op::Evaluate(Mle({}), Vec<Scalar, {}>) should be Scalar",
            n,
            n
        );
    }
}

#[test]
fn evaluate_mle_partial_returns_residual_mle() {
    // Partial MLE evaluation: Mle(n) at Vec<Scalar, k>, k < n → Mle(n - k).
    for (n, k) in [(2usize, 1usize), (3, 1), (3, 2), (4, 1), (4, 3)] {
        let p = ref_typ(ATyp::mle(n));
        let xs = vec_scalars(k);
        let eval: GOp<C> = Op::Evaluate(h(p), h(xs));
        assert_eq!(
            eval.typ(),
            ATyp::mle(n - k),
            "Op::Evaluate(Mle({}), Vec<Scalar, {}>) should be Mle({})",
            n,
            k,
            n - k
        );
    }
}

// ───────── Op::Marginalize ─────────

#[test]
fn marginalize_uni_returns_expected_record() {
    // Marginalize(record-of-Uni(d)) → Record { evaluations: Vec<Scalar, d+1>,
    //                                          next_poly: VPoly(0, d) }.
    // (Default `out_degree` falls back to the input degree `d`.)
    for d in [0usize, 1, 2, 3] {
        let mut fields = Ctx::new();
        fields.insert(&"poly".to_string(), &ATyp::uni(d));
        let rec = ref_typ(ATyp::Record(fields));
        let marg: GOp<C> = Op::Marginalize(h(rec));

        let mut expected = Ctx::new();
        expected.insert(&"evaluations".to_string(), &ATyp::vec_scalar(d + 1));
        expected.insert(&"next_poly".to_string(), &ATyp::vpoly(0, d));
        assert_eq!(
            marg.typ(),
            ATyp::Record(expected),
            "Op::Marginalize over Uni({}) record shape",
            d
        );
    }
}

#[test]
fn marginalize_mle_returns_expected_record() {
    // Marginalize(record-of-Mle(n)) → Record { evaluations: Vec<Scalar, 2>,
    //                                          next_poly: VPoly(n-1, 1) }.
    // Mle's underlying max degree is 1 in each variable.
    for n in [1usize, 2, 3, 4] {
        let mut fields = Ctx::new();
        fields.insert(&"poly".to_string(), &ATyp::mle(n));
        let rec = ref_typ(ATyp::Record(fields));
        let marg: GOp<C> = Op::Marginalize(h(rec));

        let mut expected = Ctx::new();
        expected.insert(&"evaluations".to_string(), &ATyp::vec_scalar(2));
        expected.insert(&"next_poly".to_string(), &ATyp::vpoly(n - 1, 1));
        assert_eq!(
            marg.typ(),
            ATyp::Record(expected),
            "Op::Marginalize over Mle({}) record shape",
            n
        );
    }
}

#[test]
fn marginalize_vpoly_returns_expected_record() {
    // Marginalize(record-of-VPoly(n, m)) → Record { evaluations: Vec<Scalar, m+1>,
    //                                               next_poly: VPoly(n-1, m) }.
    for (n, m) in [(2usize, 2usize), (3, 1), (3, 2), (4, 3)] {
        let mut fields = Ctx::new();
        fields.insert(&"poly".to_string(), &ATyp::vpoly(n, m));
        let rec = ref_typ(ATyp::Record(fields));
        let marg: GOp<C> = Op::Marginalize(h(rec));

        let mut expected = Ctx::new();
        expected.insert(&"evaluations".to_string(), &ATyp::vec_scalar(m + 1));
        expected.insert(&"next_poly".to_string(), &ATyp::vpoly(n - 1, m));
        assert_eq!(
            marg.typ(),
            ATyp::Record(expected),
            "Op::Marginalize over VPoly({}, {}) record shape",
            n,
            m
        );
    }
}

#[test]
fn marginalize_respects_max_degree_singleton_field() {
    // When the input record carries a `max_degree` field encoded as a
    // singleton `Fin(d..d+1)`, the output uses that as `out_degree`.
    let out_degree = 7usize;
    let mut fields = Ctx::new();
    fields.insert(&"poly".to_string(), &ATyp::vpoly(3, 2));
    fields.insert(
        &"max_degree".to_string(),
        &ATyp::fin(CRange::singleton(out_degree)),
    );
    let rec = ref_typ(ATyp::Record(fields));
    let marg: GOp<C> = Op::Marginalize(h(rec));

    let mut expected = Ctx::new();
    expected.insert(
        &"evaluations".to_string(),
        &ATyp::vec_scalar(out_degree + 1),
    );
    expected.insert(&"next_poly".to_string(), &ATyp::vpoly(2, out_degree));
    assert_eq!(marg.typ(), ATyp::Record(expected));
}
