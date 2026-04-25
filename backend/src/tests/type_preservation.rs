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
use crate::poly_variant::PolyVariant;
use crate::virtual_polynomial::VirtualPolynomial;
use crate::{ABase, ATyp, ArkConfig, ArkScalarOps, Value};
use arbitrary::{Arbitrary, Unstructured};
use ark_poly::DenseUVPolynomial;
use ark_poly::univariate::DensePolynomial;
use ark_std::test_rng;
use lang::ast::BinOp;
use lang::typ::CRange;

type TestConfig = ArkBls12_381;
type V = Value<TestConfig>;
type F = <TestConfig as ArkConfig>::F;

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
        // The generator currently uses degree 2; ensure it inhabits Uni(n) for n>=2.
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
// Polynomial ops (Ifft, Fft, Poly, Coef, Mle, Eval)
//
// These are the prime suspects: `infer.rs` types Ifft/Poly as
// `Poly(F, 1, n)` (lowering to `VPoly(1, n)`), but the runtime returns
// `VecScalar`. Tests stay red as documented regression pins.
// =============================================================================

mod poly_ops {
    use super::*;

    /// **EXPECTED FAILURE** — bug pinned by user.
    ///
    /// Spec: `Ifft : Vec(F, n) -> Poly(F, 1, n)` (`infer.rs:342`).
    /// Lowering: `Poly(F, 1, n)` -> `ATyp::VPoly(1, n)` (`types.rs:169`).
    /// Runtime: `Value::value_ifft` returns `Value::VecScalar` (`values.rs:2508`).
    /// Mismatch: variant family — `VecScalar` does not inhabit `VPoly`.
    #[test]
    fn pbt_ifft_returns_poly_per_spec() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let r = v.value_ifft();
            let expected = ATyp::vpoly(1, n);
            assert!(
                has_atyp(&r, &expected),
                "BUG (infer.rs:342 vs values.rs:2508): \
                 ifft(vec_scalar({n})) -> {} (expected {expected})",
                vty(&r)
            );
            Ok(())
        });
    }

    /// **EXPECTED FAILURE** — same pattern as Ifft. `Op::Fft` typing in
    /// `infer.rs` (audit pending in this test suite); the runtime
    /// (`values.rs:2524`) returns `VecScalar`. The most defensible spec for
    /// FFT is `Vec(F, n) -> Vec(F, n)` (it's an evaluation rebasis) — if so,
    /// this test should PASS. But if `infer.rs` types it differently, this
    /// test will surface that. We assert the runtime-shape (Vec → Vec) here
    /// and add a TODO to cross-check with `infer.rs`.
    #[test]
    fn pbt_fft_returns_vec_runtime_shape() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let r = v.value_fft();
            let expected = ATyp::vec_scalar(n);
            assert!(
                has_atyp(&r, &expected),
                "fft(vec_scalar({n})) -> {} (runtime expected {expected}; \
                 cross-check with infer.rs)",
                vty(&r)
            );
            Ok(())
        });
    }

    /// Spec: `Poly : Vec(F, n) -> Poly(F, 1, n-1)` (`infer.rs:358`).
    /// Lowering: `VPoly(1, n-1)`.
    /// Runtime: `value_poly` returns `Value::Poly(uni)`. Should PASS — degree
    /// of a poly built from n coeffs is ≤ n-1, which is what `has_atyp`
    /// against `VPoly(1, n-1)` requires.
    #[test]
    fn pbt_poly_returns_uni_per_spec() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=6)?;
            let mut rng = test_rng();
            let v: V = Value::random(&mut rng, &ATyp::vec_scalar(n));
            let r = v.value_poly();
            let expected = ATyp::vpoly(1, n.saturating_sub(1));
            assert!(
                has_atyp(&r, &expected),
                "poly(vec_scalar({n})) -> {} (expected {expected})",
                vty(&r)
            );
            Ok(())
        });
    }

    /// Spec (best reading): `Coef : Poly(F, 1, n) -> Vec(F, n+1)`.
    /// Runtime: `value_coef` on `Poly` returns `VecScalar` of length =
    /// number of coefficients. Length agreement depends on degree of the
    /// generated poly; we assert the variant-family shape only.
    #[test]
    fn pbt_coef_returns_vec_scalar() {
        let mut rng = test_rng();
        // Use a known-degree univariate poly so we can check the length.
        let coeffs: Vec<F> = (0..4)
            .map(|_| <TestConfig as ArkConfig>::FOps::rand(&mut rng))
            .collect();
        let p = DensePolynomial::from_coefficients_vec(coeffs);
        let val: V = Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(p)));
        let r = val.value_coef();
        // Spec lower bound: at least Vec(Scalar, _). We don't pin the exact
        // length because `value_coef` may strip leading zeros; the variant
        // family is the bug-finding check.
        assert!(
            matches!(&r, Value::VecScalar(_)),
            "coef(Poly) -> {} (expected VecScalar variant)",
            vty(&r)
        );
        let len = match &r {
            Value::VecScalar(v) => v.len(),
            _ => unreachable!(),
        };
        let expected = ATyp::vec_scalar(len);
        assert!(has_atyp(&r, &expected), "coef shape mismatch: {}", vty(&r));
    }
}

// =============================================================================
// Pinned regression: the user-flagged Ifft case
// =============================================================================

mod regression {
    use super::*;

    /// **EXPECTED FAILURE**.
    ///
    /// Per `lang/src/typ/infer.rs:342`, the type rule for `Ifft` is
    /// `Vec(F, n) -> Poly(F, 1, n)`. Per `backend/src/types.rs:169`,
    /// `Poly(F, 1, n)` lowers to `ATyp::VPoly(1, n)`. Per
    /// `backend/src/values.rs:2508`, `value_ifft` on a `Vec(F, 4)` returns
    /// `Value::VecScalar(_)` of length 4, whose runtime ATyp is
    /// `Vec(Scalar, 4)`. These do not agree.
    ///
    /// This test pins that disagreement. Fixing it requires *either*
    /// changing `value_ifft` to return `Value::Poly(univariate_from_coeffs)`
    /// (matching the spec) *or* changing `infer.rs` to type Ifft as
    /// `Vec(F, n)` (matching the runtime). The user's preference is to
    /// trust `infer.rs`, so the runtime is the buggy side.
    #[test]
    fn ifft_returns_poly_per_spec_fixed_size_4() {
        let mut rng = test_rng();
        let v: V = Value::random(&mut rng, &ATyp::vec_scalar(4));
        let r = v.value_ifft();
        let expected = ATyp::vpoly(1, 4);
        let actual = vty(&r);
        assert!(
            has_atyp(&r, &expected),
            "BUG: ifft(Vec(F, 4)) should produce a value of type {expected} \
             per infer.rs:342, but got value of type {actual}. \
             value_ifft (values.rs:2508) returns VecScalar; spec says Poly. \
             Fix one of: value_ifft returns Value::Poly(univariate), or \
             infer.rs:342 returns CTyp::Vec(_, n) instead of CTyp::Poly(_,1,n)."
        );
    }
}
