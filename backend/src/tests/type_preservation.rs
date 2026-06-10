//! Property-based tests for the type-preservation property:
//!
//!   If a Zippel expression has type `T` (per `lang/src/typ/infer.rs`),
//!   then evaluating it produces a `Value` `v` such that `v: T`.
//!
//! Phase 1 (this file) operates at the `Value` level only — exercising
//! `Value::value_*` methods directly. The DAG-level / pipeline-level
//! variants are deferred (see `plan.md`).
//!
//! ## Authority
//!
//! When `infer.rs` and the runtime disagree, **`infer.rs` is the spec**.
//! These tests therefore encode the inference rule as the *expected* output
//! ATyp; mismatches surface as test failures and are intentionally left
//! red as regression pins.
//!
//! ## Predicate: `has_atyp`
//!
//! [`has_atyp`] is a lenient structural predicate: a `Value::Poly` whose
//! univariate `degree() ≤ n` inhabits `ATyp::VPoly(1, n)` and `ATyp::Uni(n)`.
//! However it is *strict* about variant family — a `Value::VecScalar` does
//! NOT inhabit `ATyp::VPoly` or `ATyp::Uni`, even if it semantically
//! represents a polynomial in coefficient form. This is by design: the bug
//! the user flagged (`value_ifft` returning `VecScalar` when the spec says
//! `Poly(F, 1, n)`) is exactly this kind of variant mismatch.

use crate::config::ArkBls12_381;
use crate::op::{GOp, mk};
use crate::{ABase, ATyp, ArkConfig, Op, Value};
use arbitrary::{Arbitrary, Unstructured};
use ark_std::test_rng;
use lang::ast::BinOp;
use lang::typ::CRange;

type TestConfig = ArkBls12_381;
type V = Value<TestConfig>;

// =============================================================================
// has_atyp predicate
// =============================================================================

/// Does the runtime value `v` structurally inhabit the static type `t`?
///
/// Strict on variant families (a `VecScalar` is not a polynomial), lenient on
/// degree/var bounds (a degree-3 univariate inhabits `VPoly(1, 5)`).
pub fn has_atyp<C: ArkConfig>(v: &Value<C>, t: &ATyp) -> bool {
    match (v, t) {
        // --- bases ---
        (Value::Bool(_), ATyp::Base(ABase::Bool)) => true,
        (Value::Scalar(_), ATyp::Base(ABase::Scalar)) => true,
        (Value::G1(_), ATyp::Base(ABase::G1)) => true,
        (Value::G1Affine(_), ATyp::Base(ABase::G1)) => true,
        (Value::G2(_), ATyp::Base(ABase::G2)) => true,
        (Value::G2Affine(_), ATyp::Base(ABase::G2)) => true,
        (Value::GT(_), ATyp::Base(ABase::GT)) => true,
        (Value::Index(i), ATyp::Base(ABase::Fin(r))) => r.contains(*i),

        // --- vectors (specialized variants) ---
        (Value::VecBool(xs), ATyp::Vec(box ATyp::Base(ABase::Bool), n)) => xs.len() == *n,
        (Value::VecScalar(xs), ATyp::Vec(box ATyp::Base(ABase::Scalar), n)) => xs.len() == *n,
        (Value::VecG1(xs), ATyp::Vec(box ATyp::Base(ABase::G1), n)) => xs.len() == *n,
        (Value::VecG1Affine(xs), ATyp::Vec(box ATyp::Base(ABase::G1), n)) => xs.len() == *n,
        (Value::VecG2(xs), ATyp::Vec(box ATyp::Base(ABase::G2), n)) => xs.len() == *n,
        (Value::VecG2Affine(xs), ATyp::Vec(box ATyp::Base(ABase::G2), n)) => xs.len() == *n,
        (Value::VecGT(xs), ATyp::Vec(box ATyp::Base(ABase::GT), n)) => xs.len() == *n,
        (Value::VecIndex(xs), ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n)) => {
            xs.len() == *n && xs.iter().all(|i| r.contains(*i))
        }
        (Value::Vec(xs), ATyp::Vec(box inner, n)) => {
            xs.len() == *n && xs.iter().all(|x| has_atyp(x, inner))
        }

        // --- record ---
        (Value::Record(vfields), ATyp::Record(tfields)) => {
            if vfields.len() != tfields.len() {
                return false;
            }
            for (name, vt) in tfields.iter() {
                match vfields.get(name) {
                    Some(vv) => {
                        if !has_atyp(vv, vt) {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            true
        }

        // --- polynomials (lenient on degree/vars upper bound) ---
        (Value::Poly(p), ATyp::Uni(n)) => p.is_univariate() && p.degree() <= *n,
        (Value::Poly(p), ATyp::Mle(k)) => {
            p.is_multilinear() && p.num_vars().map(|v| v == *k).unwrap_or(false)
        }
        (Value::Poly(p), ATyp::VPoly(m, n)) => {
            // Univariate polys are VPoly with vars=1.
            // Multilinear polys have degree 1 in each var.
            let nv = p.num_vars().unwrap_or(1);
            nv == *m && p.degree() <= *n
        }

        _ => false,
    }
}

/// Helper: format a value's discovered ATyp via `Value::typ()` for messages.
fn vty<C: ArkConfig>(v: &Value<C>) -> ATyp {
    v.typ()
}

// =============================================================================
// Generators (Arbitrary newtypes)
// =============================================================================

/// Any "leaf" base ATyp — Scalar / Bool / Fin / G1 / G2 / GT.
#[derive(Debug, Clone)]
struct AnyBaseATyp(ATyp);

impl<'a> Arbitrary<'a> for AnyBaseATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let v: u8 = u.int_in_range(0..=5)?;
        Ok(AnyBaseATyp(match v {
            0 => ATyp::scalar(),
            1 => ATyp::bool(),
            2 => {
                let lo: usize = u.int_in_range(0..=10)?;
                let hi: usize = u.int_in_range((lo + 1)..=(lo + 10))?;
                ATyp::fin(CRange::new(lo, hi))
            }
            3 => ATyp::g1(),
            4 => ATyp::g2(),
            _ => ATyp::gt(),
        }))
    }
}

/// `Vec<Scalar>` of small length 1..=8.
#[derive(Debug, Clone)]
struct AnyVecScalarATyp {
    n: usize,
}

impl<'a> Arbitrary<'a> for AnyVecScalarATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(AnyVecScalarATyp {
            n: u.int_in_range(1..=8)?,
        })
    }
}

impl AnyVecScalarATyp {
    fn atyp(&self) -> ATyp {
        ATyp::vec_scalar(self.n)
    }
}

/// Any vector ATyp over a base element. Length 1..=6.
#[derive(Debug, Clone)]
struct AnyVecATyp(ATyp);

impl<'a> Arbitrary<'a> for AnyVecATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let elem: AnyBaseATyp = u.arbitrary()?;
        let n: usize = u.int_in_range(1..=6)?;
        Ok(AnyVecATyp(ATyp::vec(&elem.0, n)))
    }
}

/// Univariate polynomial `Uni(m)` for `m ∈ 0..=7`.
#[derive(Debug, Clone)]
struct AnyUniATyp {
    m: usize,
}

impl<'a> Arbitrary<'a> for AnyUniATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(AnyUniATyp {
            m: u.int_in_range(0..=7)?,
        })
    }
}

/// Univariate `Uni(m)` where `m+1` is a power of two (FFT-compatible).
/// Picks from the set {0, 1, 3, 7} so that `m+1 ∈ {1, 2, 4, 8}`.
#[derive(Debug, Clone)]
struct AnyPow2UniATyp {
    m: usize,
}

impl<'a> Arbitrary<'a> for AnyPow2UniATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        // m+1 ∈ {1, 2, 4, 8} ↔ m ∈ {0, 1, 3, 7}
        let candidates = [0usize, 1, 3, 7];
        let idx: usize = u.int_in_range(0..=3)?;
        Ok(AnyPow2UniATyp { m: candidates[idx] })
    }
}

/// Univariate `Uni(m)` where `m+1` is NOT a power of two (FFT-padding gap).
/// Picks from the set {2, 4, 5, 6} so that `m+1 ∈ {3, 5, 6, 7}`.
#[derive(Debug, Clone)]
struct AnyNonPow2UniATyp {
    m: usize,
}

impl<'a> Arbitrary<'a> for AnyNonPow2UniATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        // m+1 ∈ {3, 5, 6, 7} ↔ m ∈ {2, 4, 5, 6}
        let candidates = [2usize, 4, 5, 6];
        let idx: usize = u.int_in_range(0..=3)?;
        Ok(AnyNonPow2UniATyp { m: candidates[idx] })
    }
}

/// Vec(Scalar, k) where `k` is a power of two in 1..=8.
#[derive(Debug, Clone)]
struct AnyPow2VecScalarATyp {
    k: usize,
}

impl<'a> Arbitrary<'a> for AnyPow2VecScalarATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let log2: usize = u.int_in_range(0..=3)?; // k ∈ {1, 2, 4, 8}
        Ok(AnyPow2VecScalarATyp { k: 1 << log2 })
    }
}

/// Multilinear extension `Mle(n)` for `n ∈ 1..=4`.
#[derive(Debug, Clone)]
struct AnyMleATyp {
    n: usize,
}

impl<'a> Arbitrary<'a> for AnyMleATyp {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(AnyMleATyp {
            n: u.int_in_range(1..=4)?,
        })
    }
}

// =============================================================================
// Scaffolding: predicate sanity
// =============================================================================

mod scaffolding {
    use super::*;

    #[test]
    fn random_inhabits_base() {
        let mut rng = test_rng();
        for t in [
            ATyp::scalar(),
            ATyp::bool(),
            ATyp::g1(),
            ATyp::g2(),
            ATyp::gt(),
            ATyp::fin(CRange::new(0, 16)),
        ] {
            let v: V = Value::random(&mut rng, &t);
            assert!(
                has_atyp(&v, &t),
                "Value::random({t}) produced {v:?} which fails has_atyp({t}); v.typ()={}",
                vty(&v)
            );
        }
    }

    #[test]
    fn random_inhabits_vec_scalar() {
        let mut rng = test_rng();
        for n in 1..=8usize {
            let t = ATyp::vec_scalar(n);
            let v: V = Value::random(&mut rng, &t);
            assert!(has_atyp(&v, &t), "vec_scalar({n}): got {}", vty(&v));
        }
    }

    #[test]
    fn random_inhabits_uni() {
        // `Value::random(Uni(n))` must produce `Value::Poly` per spec.
        let mut rng = test_rng();
        let t = ATyp::uni(8);
        let v: V = Value::random(&mut rng, &t);
        assert!(
            has_atyp(&v, &t),
            "Value::random(Uni(8)) produced {} (expected Uni-shape, max deg 8)",
            vty(&v)
        );
    }

    #[test]
    fn random_inhabits_mle() {
        // `Value::random(Mle(k))` must respect the supplied num_vars.
        let mut rng = test_rng();
        for k in 1..=4usize {
            let t = ATyp::Mle(k);
            let v: V = Value::random(&mut rng, &t);
            assert!(
                has_atyp(&v, &t),
                "Value::random(Mle({k})) produced {} (expected Mle with {k} vars)",
                vty(&v)
            );
        }
    }

    #[test]
    fn pbt_random_inhabits_vec_atyp() {
        arbtest::arbtest(|u| {
            let t: AnyVecATyp = u.arbitrary()?;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &t.0);
            assert!(
                has_atyp(&v, &t.0),
                "random({:?}) -> {} fails has_atyp",
                t.0,
                vty(&v)
            );
            Ok(())
        });
    }
}

// =============================================================================
// Binary ops (Add/Sub/Mul/Div/Pow/And/Equ)
// =============================================================================

mod binops {
    use super::*;

    /// Spec rule for arithmetic binops on the same scalar/vec base type:
    /// (T, T) -> T.
    #[test]
    fn add_scalar_preserves() {
        let mut rng = test_rng();
        for _ in 0..32 {
            let a: V = Value::random(&mut rng, &ATyp::scalar());
            let b: V = Value::random(&mut rng, &ATyp::scalar());
            let c = a + b;
            assert!(has_atyp(&c, &ATyp::scalar()), "got {}", vty(&c));
        }
    }

    #[test]
    fn mul_scalar_preserves() {
        let mut rng = test_rng();
        for _ in 0..32 {
            let a: V = Value::random(&mut rng, &ATyp::scalar());
            let b: V = Value::random(&mut rng, &ATyp::scalar());
            let c = a * b;
            assert!(has_atyp(&c, &ATyp::scalar()), "got {}", vty(&c));
        }
    }

    #[test]
    fn pbt_add_vec_scalar_preserves() {
        arbtest::arbtest(|u| {
            let t: AnyVecScalarATyp = u.arbitrary()?;
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &t.atyp());
            let b: V = Value::random(&mut rng, &t.atyp());
            let c = a + b;
            assert!(
                has_atyp(&c, &t.atyp()),
                "vec_scalar({}) + vec_scalar({}) -> {} (expected {})",
                t.n,
                t.n,
                vty(&c),
                t.atyp()
            );
            Ok(())
        });
    }

    #[test]
    fn pbt_mul_vec_scalar_preserves() {
        arbtest::arbtest(|u| {
            let t: AnyVecScalarATyp = u.arbitrary()?;
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &t.atyp());
            let b: V = Value::random(&mut rng, &t.atyp());
            let c = a * b;
            assert!(has_atyp(&c, &t.atyp()), "got {}", vty(&c));
            Ok(())
        });
    }

    #[test]
    fn pbt_sub_vec_scalar_preserves() {
        arbtest::arbtest(|u| {
            let t: AnyVecScalarATyp = u.arbitrary()?;
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &t.atyp());
            let b: V = Value::random(&mut rng, &t.atyp());
            let c = a - b;
            assert!(has_atyp(&c, &t.atyp()), "got {}", vty(&c));
            Ok(())
        });
    }

    /// Equality: (T, T) -> Bool.
    #[test]
    fn pbt_equ_scalar_returns_bool() {
        arbtest::arbtest(|_u| {
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &ATyp::scalar());
            let b: V = Value::random(&mut rng, &ATyp::scalar());
            let c = a.value_equ(&b);
            assert!(
                has_atyp(&c, &ATyp::bool()),
                "equ produced {} (expected Bool)",
                vty(&c)
            );
            Ok(())
        });
    }

    /// Boolean and: (Bool, Bool) -> Bool.
    #[test]
    fn pbt_and_bool_returns_bool() {
        arbtest::arbtest(|_u| {
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &ATyp::bool());
            let mut b: V = Value::random(&mut rng, &ATyp::bool());
            a.value_and(&mut b);
            assert!(has_atyp(&b, &ATyp::bool()), "got {}", vty(&b));
            Ok(())
        });
    }
}

// =============================================================================
// Vector ops (Vec, Concat, Dot, Reduce, Pair, Ram)
// =============================================================================

mod vec_ops {
    use super::*;

    /// `Op::Vec(args : n × T) -> Vec(T, n)`.
    #[test]
    fn pbt_vec_constructor_preserves() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let elems: Vec<V> = (0..n)
                .map(|_| Value::random(&mut rng, &ATyp::scalar()))
                .collect();
            let v = Value::value_vec(elems);
            let expected = ATyp::vec_scalar(n);
            assert!(
                has_atyp(&v, &expected),
                "Op::Vec({n} × Scalar) -> {} (expected {expected})",
                vty(&v)
            );
            Ok(())
        });
    }

    /// `Concat: (Vec(T,n), Vec(T,m)) -> Vec(T, n+m)` per `infer.rs`.
    #[test]
    fn pbt_concat_vec_scalar_preserves() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let m: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let b: V = Value::random(&mut rng, &ATyp::vec_scalar(m));
            let c = a.value_concat(b);
            let expected = ATyp::vec_scalar(n + m);
            assert!(
                has_atyp(&c, &expected),
                "concat({n}, {m}) -> {} (expected {expected})",
                vty(&c)
            );
            Ok(())
        });
    }

    /// `Dot: (Vec(T,n), Vec(T,n)) -> T`.
    #[test]
    fn pbt_dot_vec_scalar_returns_scalar() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let b: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let c = a.dot(b);
            assert!(
                has_atyp(&c, &ATyp::scalar()),
                "dot len {n} -> {} (expected Scalar)",
                vty(&c)
            );
            Ok(())
        });
    }

    /// `Reduce(Add, Vec(F, n)) -> F`.
    #[test]
    fn pbt_reduce_add_vec_scalar_returns_scalar() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let r = v.value_reduce(BinOp::Add);
            assert!(
                has_atyp(&r, &ATyp::scalar()),
                "reduce(+, vec_scalar({n})) -> {} (expected Scalar)",
                vty(&r)
            );
            Ok(())
        });
    }

    /// `Pair: (G1, G2) -> GT`.
    #[test]
    fn pbt_pair_returns_gt() {
        arbtest::arbtest(|_u| {
            let mut rng = test_rng();
            let a: V = Value::random(&mut rng, &ATyp::g1());
            let b: V = Value::random(&mut rng, &ATyp::g2());
            let c = a.pair(b);
            assert!(
                has_atyp(&c, &ATyp::gt()),
                "pair(G1, G2) -> {} (expected GT)",
                vty(&c)
            );
            Ok(())
        });
    }

    /// `Ram: (Vec(T, n), Index) -> T`.
    #[test]
    fn pbt_ram_vec_scalar_returns_scalar() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let i: usize = u.int_in_range(0..=(n - 1))?;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let r = v.ram(Value::Index(i));
            assert!(
                has_atyp(&r, &ATyp::scalar()),
                "ram(vec_scalar({n}), {i}) -> {} (expected Scalar)",
                vty(&r)
            );
            Ok(())
        });
    }
}

// =============================================================================
// Cross-layer `Value::typ() == Op::typ()` PBT — Unit 5
//
// For each `Op::*` polynomial op, build a single-argument `Op::Value(v)` (or
// two such, for binary ops) where `v = Value::random(&input_typ)`. Then run
// the corresponding `value_*` method on `v` and assert that
// `has_atyp(&result_value, &op.typ())` holds.
//
// Tests that document known gaps between `Op::typ()` and the runtime are
// annotated `#[should_panic(expected = "...")]`: they PASS when the gap is
// present and FAIL when the gap is fixed, acting as regression pins.
// Current known gaps:
//   - FFT padding: `Op::Fft::typ()` declares `Vec(F, m+1)` but the runtime
//     pads to `next_pow2(m+1)` evaluations when `m+1` is not a power of two.
//   - `Op::Coef::typ()` accepts `Mle(n)` inputs (returns `Vec(F, 2^n)`) but
//     `value_coef` panics on multilinear polynomials.
//   - `Op::Evaluate::typ()` semantic gaps: partial-MLE / partial-VPoly evals
//     return flat `VecScalar` in the runtime instead of a `Value::Poly(Mle)`,
//     and single-point full-MLE eval returns `VecScalar([s])` instead of
//     `Scalar`; batched-uni eval pads to the next power-of-two.
// =============================================================================

mod cross_layer {
    use super::*;

    /// Concrete `Op` type used throughout this module.
    type TOp = GOp<TestConfig>;

    /// Wrap `v` as `Op::Value(v)`. The declared type is `v.typ()`.
    fn val_op(v: V) -> TOp {
        Op::Value(v)
    }

    fn fft_op(v: &V) -> TOp {
        Op::Fft(mk::<TestConfig>(val_op(v.clone())))
    }
    fn ifft_op(v: &V) -> TOp {
        Op::Ifft(mk::<TestConfig>(val_op(v.clone())))
    }
    fn interp_op(points: &V, evals: &V) -> TOp {
        Op::Interpolate(
            mk::<TestConfig>(val_op(points.clone())),
            mk::<TestConfig>(val_op(evals.clone())),
        )
    }
    fn coef_op(v: &V) -> TOp {
        Op::Coef(mk::<TestConfig>(val_op(v.clone())))
    }
    fn poly_op(v: &V) -> TOp {
        Op::Poly(mk::<TestConfig>(val_op(v.clone())))
    }
    fn eval_op(p: &V, x: &V) -> TOp {
        Op::Evaluate(
            mk::<TestConfig>(val_op(p.clone())),
            None,
            Some(mk::<TestConfig>(val_op(x.clone()))),
        )
    }
    fn mle_op(v: &V) -> TOp {
        Op::Mle(mk::<TestConfig>(val_op(v.clone())))
    }

    // -------------------------------------------------------------------------
    // `value_fft`
    //
    // `Op::Fft::typ()` returns `Vec(F, m+1)` for `Uni(m)` (coefficient count).
    // The runtime pads to `next_pow2(m+1)`. When `m+1` is already a power of
    // two the declared size and the runtime size agree; otherwise they disagree.
    // -------------------------------------------------------------------------

    /// FFT on `Uni(m)` where `m+1` is a power of two — passes cleanly.
    #[test]
    fn pbt_fft_pow2_coef_count() {
        arbtest::arbtest(|u| {
            let t: AnyPow2UniATyp = u.arbitrary()?;
            let m = t.m;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::uni(m));
            let op = fft_op(&v);
            let expected = op.typ();
            let actual = v.value_fft();
            assert!(
                has_atyp(&actual, &expected),
                "value_fft(Uni({m})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// FFT on `Uni(m)` where `m+1` is NOT a power of two — runtime pads,
    /// declared type disagrees. Gap pinned with `#[should_panic]`.
    #[test]
    #[should_panic(expected = "value_fft(Uni(")]
    fn pbt_fft_non_pow2_coef_count() {
        arbtest::arbtest(|u| {
            let t: AnyNonPow2UniATyp = u.arbitrary()?;
            let m = t.m;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::uni(m));
            let op = fft_op(&v);
            let expected = op.typ();
            let actual = v.value_fft();
            assert!(
                has_atyp(&actual, &expected),
                "value_fft(Uni({m})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    // -------------------------------------------------------------------------
    // `value_interpolate(None, _)` — unary IFFT / FFT-grid interpolation.
    // Input: `Vec(F, k)`. `Op::Ifft::typ()` returns `Uni(k-1)`.
    // Same FFT-padding gap: when `k` is not a power of two the runtime pads
    // to `next_pow2(k)` evaluations, producing a higher-degree poly than declared.
    // -------------------------------------------------------------------------

    /// IFFT on `Vec(F, k)` where `k` is a power of two — passes cleanly.
    #[test]
    fn pbt_ifft_pow2() {
        arbtest::arbtest(|u| {
            let t: AnyPow2VecScalarATyp = u.arbitrary()?;
            let k = t.k;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = ifft_op(&v);
            let expected = op.typ();
            let actual = v.value_interpolate(None);
            assert!(
                has_atyp(&actual, &expected),
                "value_interpolate(Vec(F,{k}), None) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// IFFT on `Vec(F, k)` where `k` is NOT a power of two — runtime pads,
    /// declaring type disagrees. Gap pinned with `#[should_panic]`.
    #[test]
    #[should_panic(expected = "value_interpolate(Vec(F,")]
    fn pbt_ifft_non_pow2() {
        arbtest::arbtest(|u| {
            // k ∈ {3, 5, 6, 7} — not powers of two
            let candidates = [3usize, 5, 6, 7];
            let idx: usize = u.int_in_range(0..=3)?;
            let k = candidates[idx];
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = ifft_op(&v);
            let expected = op.typ();
            let actual = v.value_interpolate(None);
            assert!(
                has_atyp(&actual, &expected),
                "value_interpolate(Vec(F,{k}), None) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    // -------------------------------------------------------------------------
    // `value_interpolate(Some(points), evals)` — binary Lagrange interpolation.
    // Input: two `Vec(F, k)`. `Op::Interpolate::typ()` returns `Uni(k-1)`.
    // -------------------------------------------------------------------------

    /// Binary interpolation at arbitrary `k ∈ 1..=8` distinct points.
    #[test]
    fn pbt_interpolate_binary() {
        arbtest::arbtest(|u| {
            let t: AnyVecScalarATyp = u.arbitrary()?;
            let k = t.n;
            let mut rng = test_rng();
            let points: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let evals: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = interp_op(&points, &evals);
            let expected = op.typ();
            let actual = evals.value_interpolate(Some(&points));
            assert!(
                has_atyp(&actual, &expected),
                "value_interpolate(Vec(F,{k}), Some(Vec(F,{k}))) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    // -------------------------------------------------------------------------
    // `value_coef`
    // -------------------------------------------------------------------------

    /// `value_coef` on `Uni(m)` for arbitrary `m ∈ 0..=7`.
    #[test]
    fn pbt_coef_uni() {
        arbtest::arbtest(|u| {
            let t: AnyUniATyp = u.arbitrary()?;
            let m = t.m;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::uni(m));
            let op = coef_op(&v);
            let expected = op.typ();
            let actual = v.value_coef();
            assert!(
                has_atyp(&actual, &expected),
                "value_coef(Uni({m})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// `value_coef` on `Mle(n)` for `n ∈ 1..=4`.
    /// `Op::Coef::typ()` accepts MLE inputs (returns `Vec(F, 2^n)`) but the
    /// runtime panics. This gap is pinned with `#[should_panic]`.
    #[test]
    #[should_panic(expected = "Op::Coef::typ() accepted Mle(")]
    fn pbt_coef_mle() {
        arbtest::arbtest(|u| {
            let t: AnyMleATyp = u.arbitrary()?;
            let n = t.n;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::Mle(n));

            let v_for_op = v.clone();
            let op_typ_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let op = coef_op(&v_for_op);
                op.typ()
            }));

            let v_for_val = v.clone();
            let actual_result =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| v_for_val.value_coef()));

            match (op_typ_result, actual_result) {
                (Ok(expected), Ok(actual)) => {
                    assert!(
                        has_atyp(&actual, &expected),
                        "value_coef(Mle({n})) -> {} fails has_atyp(_, {expected})",
                        vty(&actual)
                    );
                }
                (Err(_), Err(_)) => {}
                (Ok(expected), Err(_)) => {
                    panic!(
                        "value_coef panicked: Op::Coef::typ() accepted Mle({n}) \
                         with declared ATyp {expected}, but value_coef panicked"
                    );
                }
                (Err(_), Ok(actual)) => {
                    panic!(
                        "Op::Coef::typ() rejected Mle({n}) (panicked), \
                         but value_coef produced {actual:?} (typ {})",
                        vty(&actual)
                    );
                }
            }
            Ok(())
        });
    }

    // -------------------------------------------------------------------------
    // `value_poly`
    // -------------------------------------------------------------------------

    /// `value_poly` on `Vec(F, k)` for arbitrary `k ∈ 1..=8`.
    #[test]
    fn pbt_poly() {
        arbtest::arbtest(|u| {
            let t: AnyVecScalarATyp = u.arbitrary()?;
            let k = t.n;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = poly_op(&v);
            let expected = op.typ();
            let actual = v.value_poly();
            assert!(
                has_atyp(&actual, &expected),
                "value_poly(Vec(F,{k})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    // -------------------------------------------------------------------------
    // `value_eval`
    //
    // `Op::Evaluate(p, x)::typ()` handles four cases:
    //   Uni(_)/VPoly(1,_) × Vec → Vec  (batched)
    //   VPoly(n,_)/Mle(n) × Vec(n)  → Scalar  (full)
    //   VPoly(n,m) × Vec(k<n) → VPoly(n-k, m)  (partial)
    //   Mle(n) × Vec(k<n) → Mle(n-k)  (partial)
    //
    // Gaps: FFT-padding on batched uni eval; runtime returns VecScalar for
    // partial/full Mle where the spec says Mle/Scalar; n=1 Mle full eval
    // returns VecScalar([s]) instead of Scalar.
    // -------------------------------------------------------------------------

    /// Batched univariate eval at a single point `k=1`: both layers agree.
    #[test]
    fn pbt_eval_uni_batched_single_point() {
        arbtest::arbtest(|u| {
            let t: AnyUniATyp = u.arbitrary()?;
            let m = t.m;
            let mut rng = test_rng();
            let p: V = Value::random(&mut rng, &ATyp::uni(m));
            let x: V = Value::random(&mut rng, &ATyp::vec_scalar(1));
            let op = eval_op(&p, &x);
            let expected = op.typ();
            let actual = p.value_eval(x);
            assert!(
                has_atyp(&actual, &expected),
                "value_eval(Uni({m}), Vec(F,1)) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// Batched univariate eval at `k > 1` points now returns an exact
    /// `VecScalar(k)` (the explicit-eval migration replaced the old FFT-padded
    /// MLE output), so type preservation holds. Gap closed.
    #[test]
    fn pbt_eval_uni_batched_multi_point() {
        arbtest::arbtest(|u| {
            let tm: AnyUniATyp = u.arbitrary()?;
            let m = tm.m;
            // k ∈ 2..=5 — never a pow2-aligned single eval
            let k: usize = u.int_in_range(2..=5)?;
            let mut rng = test_rng();
            let p: V = Value::random(&mut rng, &ATyp::uni(m));
            let x: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = eval_op(&p, &x);
            let expected = op.typ();
            let actual = p.value_eval(x);
            assert!(
                has_atyp(&actual, &expected),
                "value_eval(Uni({m}), Vec(F,{k})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// Full VPoly eval for `n ∈ 1..=4` vars: `Value::random` produces a
    /// univariate (n=1) or DenseMle (n>=2), both collapse correctly to Scalar.
    #[test]
    fn pbt_eval_vpoly_full() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let mut rng = test_rng();
            let p: V = Value::random(&mut rng, &ATyp::vpoly(n, 2));
            let x: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let op = eval_op(&p, &x);
            let expected = op.typ();
            let actual = p.value_eval(x);
            assert!(
                has_atyp(&actual, &expected),
                "value_eval(VPoly({n}, 2), Vec(F,{n})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// Partial VPoly eval `k < n` now returns a `VecScalar` that satisfies
    /// the op's declared type after the explicit-eval migration. Gap closed.
    #[test]
    fn pbt_eval_vpoly_partial() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(2..=4)?;
            let k: usize = u.int_in_range(1..=(n - 1))?;
            let mut rng = test_rng();
            let p: V = Value::random(&mut rng, &ATyp::vpoly(n, 2));
            let x: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = eval_op(&p, &x);
            let expected = op.typ();
            let actual = p.value_eval(x);
            assert!(
                has_atyp(&actual, &expected),
                "value_eval(VPoly({n}, 2), Vec(F,{k})) [partial] -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// Full MLE eval for `n >= 2` vars: runtime returns `Scalar` as expected.
    #[test]
    fn pbt_eval_mle_full_multi_var() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(2..=4)?;
            let mut rng = test_rng();
            let p: V = Value::random(&mut rng, &ATyp::Mle(n));
            let x: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let op = eval_op(&p, &x);
            let expected = op.typ();
            let actual = p.value_eval(x);
            assert!(
                has_atyp(&actual, &expected),
                "value_eval(Mle({n}), Vec(F,{n})) [full] -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    /// Full MLE eval for `n=1` (single point): runtime returns `VecScalar([s])`
    /// instead of `Scalar`. Gap pinned with `#[should_panic]`.
    #[test]
    #[should_panic(expected = "value_eval(Mle(1), Vec(F,1))")]
    fn pbt_eval_mle_full_single_var() {
        let n = 1usize;
        let mut rng = test_rng();
        let p: V = Value::random(&mut rng, &ATyp::Mle(n));
        let x: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
        let op = eval_op(&p, &x);
        let expected = op.typ();
        let actual = p.value_eval(x);
        assert!(
            has_atyp(&actual, &expected),
            "value_eval(Mle(1), Vec(F,1)) [full] -> {} fails has_atyp(_, {expected})",
            vty(&actual)
        );
    }

    /// Partial MLE eval now returns a `VecScalar` that satisfies the op's
    /// declared type after the explicit-eval migration. Gap closed.
    #[test]
    fn pbt_eval_mle_partial() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(2..=4)?;
            let k: usize = u.int_in_range(1..=(n - 1))?;
            let mut rng = test_rng();
            let p: V = Value::random(&mut rng, &ATyp::Mle(n));
            let x: V = Value::random(&mut rng, &ATyp::vec_scalar(k));
            let op = eval_op(&p, &x);
            let expected = op.typ();
            let actual = p.value_eval(x);
            assert!(
                has_atyp(&actual, &expected),
                "value_eval(Mle({n}), Vec(F,{k})) [partial] -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }

    // -------------------------------------------------------------------------
    // `value_mle`: `Vec(F, 2^n)` -> `Mle(n)`. Both layers agree on lengths.
    // -------------------------------------------------------------------------

    /// MLE construction from `Vec(F, 2^n)` for `n ∈ 0..=4`.
    #[test]
    fn pbt_mle() {
        arbtest::arbtest(|u| {
            let log2: usize = u.int_in_range(0..=4)?;
            let len = 1usize << log2;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(len));
            let op = mle_op(&v);
            let expected = op.typ();
            let actual = v.value_mle();
            assert!(
                has_atyp(&actual, &expected),
                "value_mle(Vec(F,{len})) -> {} fails has_atyp(_, {expected})",
                vty(&actual)
            );
            Ok(())
        });
    }
}
