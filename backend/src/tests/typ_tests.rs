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
use petgraph::graph::NodeIndex;

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
    let eval = GOp::evaluate(mle, xs_vec); // full evaluation
    assert_eq!(eval.typ(), ATyp::scalar());
}

#[test]
fn eval_of_mle_partial_shape_is_residual_mle() {
    // Partial evaluation at k < n points keeps an Mle(n-k).
    let evals: Vec<_> = (0..16).map(|i| h(scalar(i))).collect();
    let mle: GOp<C> = Op::Mle(h(Op::Vec(evals))); // Mle(4)
    let xs_vec: GOp<C> = Op::Vec(vec![h(scalar(0))]); // |xs| = 1, k < n
    let eval = GOp::evaluate(mle, xs_vec);
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
