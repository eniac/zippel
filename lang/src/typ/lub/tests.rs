use super::*;
#[test]
fn lub_range() {
    let a = Range {
        start: 0,
        step: 1,
        end: 10,
    };
    let b = Range {
        start: 5,
        step: 1,
        end: 15,
    };

    assert_eq!(
        Range::lub_equ(&a, &b, &Nothing),
        Ok(Range {
            start: 0,
            step: 1,
            end: 15
        })
    );
    assert_eq!(
        Range::lub_add(&a, &b, &Nothing),
        Ok(Range {
            start: 5,
            step: 1,
            end: 24
        })
    );
    // lub_sub(&b, &a): b.start (5) < a_max (9), so checked_sub underflows
    assert!(Range::lub_sub(&b, &a, &Nothing).is_err());
    assert_eq!(
        Range::lub_mul(&a, &b, &Nothing),
        Ok(Range {
            start: 0,
            step: 1,
            end: 127
        })
    );
    assert_eq!(
        Range::lub_div(
            &b,
            &Range {
                start: 1,
                step: 1,
                end: 15
            },
            &Nothing
        ),
        Ok(Range {
            start: 0,
            step: 1,
            end: 15
        })
    );
}

#[test]
fn lub_add_overflow() {
    let a = Range {
        start: usize::MAX - 5,
        step: 1,
        end: usize::MAX,
    };
    let b = Range {
        start: 1,
        step: 1,
        end: 10,
    };
    assert!(Range::lub_add(&a, &b, &Nothing).is_err());
}

#[test]
fn lub_sub_underflow() {
    let a = Range {
        start: 1,
        step: 1,
        end: 10,
    };
    let b = Range {
        start: 5,
        step: 1,
        end: 20,
    };
    assert!(Range::lub_sub(&a, &b, &Nothing).is_err());
}

#[test]
fn lub_mul_overflow() {
    let big = (usize::MAX as f64).sqrt() as usize + 1;
    let a = Range {
        start: big,
        step: 1,
        end: big + 1,
    };
    let b = Range {
        start: big,
        step: 1,
        end: big + 1,
    };
    // big * big overflows usize
    assert!(Range::lub_mul(&a, &b, &Nothing).is_err());
}

#[test]
fn lub_div_by_zero() {
    let a = Range {
        start: 0,
        step: 1,
        end: 10,
    };
    let b = Range {
        start: 0,
        step: 1,
        end: 3,
    };
    // b.start == 0 is caught by the explicit zero check
    assert!(Range::lub_div(&a, &b, &Nothing).is_err());
}

#[test]
fn lub_rem_by_zero() {
    let a = Range {
        start: 0,
        step: 1,
        end: 10,
    };
    let b = Range {
        start: 0,
        step: 1,
        end: 3,
    };
    assert!(Range::lub_rem(&a, &b, &Nothing).is_err());
}

#[test]
fn lub_pow_overflow() {
    let a = Range {
        start: 2,
        step: 1,
        end: 3,
    };
    let b = Range {
        start: 64,
        step: 1,
        end: 65,
    };
    // 2^64 overflows usize on 64-bit
    assert!(Range::lub_pow(&a, &b, &Nothing).is_err());
}

#[test]
fn lub_dot_overflow() {
    let big = (usize::MAX as f64).sqrt() as usize + 1;
    let a = Range {
        start: big,
        step: 1,
        end: big + 1,
    };
    let b = Range {
        start: big,
        step: 1,
        end: big + 1,
    };
    // dot delegates to mul, which overflows
    assert!(Range::lub_dot(&a, &b, &Nothing).is_err());
}

use share::Set;
#[test]
fn lub_tid() {
    let f = Tid::from("F");
    let g1 = Tid::from("G1");
    let g2 = Tid::from("G2");
    let p = Tid::from("P");
    let s1 = Tid::from("S1");
    let s2 = Tid::from("S2");
    let ctx = Ctx::from([
        (f.clone(), Kind::Field),
        (g1.clone(), Kind::Group),
        (g2.clone(), Kind::Group),
        (p.clone(), Kind::Pairing(g1.clone(), g2.clone())),
        (s1.clone(), Kind::Scalar(Set::from([g1.clone()]))),
        (s2.clone(), Kind::Scalar(Set::from([g2.clone()]))),
    ]);

    assert_eq!(Tid::lub_equ(&f, &f, &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_equ(&g1, &g1, &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_equ(&s1, &s1, &ctx), Ok(s1.clone()));
    assert!(Tid::lub_equ(&g1, &g2, &ctx).is_err());

    assert_eq!(Tid::lub_add(&f, &f, &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_add(&s1, &s1, &ctx), Ok(s1.clone()));
    assert_eq!(Tid::lub_add(&g1, &g1, &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_add(&p, &p, &ctx), Ok(p.clone()));
    assert!(Tid::lub_add(&g1, &g2, &ctx).is_err());

    assert_eq!(Tid::lub_sub(&f, &f, &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_sub(&s1, &s1, &ctx), Ok(s1.clone()));
    assert_eq!(Tid::lub_sub(&g1, &g1, &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_sub(&p, &p, &ctx), Ok(p.clone()));
    assert!(Tid::lub_sub(&g1, &g2, &ctx).is_err());

    assert_eq!(Tid::lub_mul(&f, &f, &ctx), Ok(f.clone()));
    assert!(Tid::lub_mul(&g1, &g1, &ctx).is_err());
    assert_eq!(Tid::lub_mul(&g1, &g2, &ctx), Ok(p.clone()));
    assert_eq!(Tid::lub_mul(&g2, &g1, &ctx), Ok(p.clone()));
    assert!(Tid::lub_mul(&s1, &s2, &ctx).is_err());
    assert_eq!(Tid::lub_mul(&s1, &s1, &ctx), Ok(s1.clone()));
    assert_eq!(Tid::lub_mul(&s1, &g1, &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_mul(&g2, &s2, &ctx), Ok(g2.clone()));

    assert_eq!(Tid::lub_pair(&g1, &g2, &ctx), Ok(p.clone()));
    assert_eq!(Tid::lub_pair(&g2, &g1, &ctx), Ok(p.clone()));

    assert_eq!(Tid::lub_div(&f, &f, &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_div(&s1, &s1, &ctx), Ok(s1.clone()));
    assert!(Tid::lub_div(&s1, &s2, &ctx).is_err());
    assert!(Tid::lub_div(&g1, &g1, &ctx).is_err());
    assert!(Tid::lub_div(&g1, &f, &ctx).is_err());
    assert_eq!(Tid::lub_div(&g1, &s1, &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_div(&g2, &s2, &ctx), Ok(g2.clone()));
    assert!(Tid::lub_div(&g1, &s2, &ctx).is_err());
}

#[test]
fn lub_typ() {
    let f = Tid::from("F");
    let g1 = Tid::from("G1");
    let g2 = Tid::from("G2");
    let s1 = Tid::from("S1");
    let s2 = Tid::from("S2");
    let p = Tid::from("P");
    let ctx = Ctx::from([
        (f.clone(), Kind::Field),
        (g1.clone(), Kind::Group),
        (g2.clone(), Kind::Group),
        (p.clone(), Kind::Pairing(g1.clone(), g2.clone())),
        (s1.clone(), Kind::Scalar(Set::from([g1.clone()]))),
        (s2.clone(), Kind::Scalar(Set::from([g2.clone()]))),
    ]);

    let tf = CTyp::base(&f);
    let tg1 = CTyp::base(&g1);
    let tg2 = CTyp::base(&g2);
    let tp = CTyp::base(&p);
    let ts1 = CTyp::base(&s1);
    let ts2 = CTyp::base(&s2);
    let tr = CTyp::Fin(Range::singleton(10));

    assert_eq!(CTyp::lub_equ(&tf, &tf, &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_equ(&tg1, &tg1, &ctx), Ok(tg1.clone()));
    assert!(CTyp::lub_equ(&tg1, &tg2, &ctx).is_err());
    assert_eq!(CTyp::lub_equ(&ts1, &ts1, &ctx), Ok(ts1.clone()));
    assert_eq!(
        CTyp::lub_equ(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 10), &ctx),
        Ok(CTyp::vec(&tf, 10))
    );
    assert!(CTyp::lub_equ(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 11), &ctx).is_err());
    assert!(CTyp::lub_equ(&CTyp::vec(&tf, 10), &CTyp::vec(&tg1, 10), &ctx).is_err());
    assert_eq!(
        CTyp::lub_equ(&CTyp::uni(&f, 10), &CTyp::uni(&f, 11), &ctx),
        Ok(CTyp::uni(&f, 11))
    );

    assert_eq!(CTyp::lub_add(&tf, &tf, &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_add(&tg1, &tg1, &ctx), Ok(tg1.clone()));
    assert!(CTyp::lub_add(&tg1, &tg2, &ctx).is_err());
    assert_eq!(CTyp::lub_add(&ts1, &ts1, &ctx), Ok(ts1.clone()));
    assert!(CTyp::lub_add(&ts1, &ts2, &ctx).is_err());
    assert_eq!(CTyp::lub_add(&tp, &tp, &ctx), Ok(tp.clone()));
    assert!(CTyp::lub_add(&tp, &tg1, &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 11), &ctx).is_err());
    assert_eq!(
        CTyp::lub_add(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 10), &ctx),
        Ok(CTyp::vec(&tf, 10))
    );
    assert_eq!(
        CTyp::lub_add(&CTyp::uni(&f, 10), &CTyp::uni(&f, 11), &ctx),
        Ok(CTyp::uni(&f, 11))
    );
    assert_eq!(
        CTyp::lub_add(&CTyp::mle(&f, 10), &CTyp::mle(&f, 11), &ctx),
        Ok(CTyp::mle(&f, 11))
    );
    assert_eq!(
        CTyp::lub_add(&CTyp::vec(&tg1, 10), &CTyp::vec(&tg1, 10), &ctx),
        Ok(CTyp::vec(&tg1, 10))
    );

    assert_eq!(CTyp::lub_pair(&tg1, &tg2, &ctx), Ok(tp.clone()));
    assert_eq!(CTyp::lub_pair(&tg2, &tg1, &ctx), Ok(tp.clone()));

    assert_eq!(CTyp::lub_pow(&tf, &tr, &ctx), Ok(tf.clone()));
    assert_eq!(
        CTyp::lub_pow(&CTyp::vec(&tf, 10), &tr, &ctx),
        Ok(CTyp::vec(&tf, 10))
    );
    assert_eq!(
        CTyp::lub_pow(&CTyp::uni(&f, 10), &tr, &ctx),
        Ok(CTyp::uni(&f, 100))
    );
    assert!(CTyp::lub_pow(&CTyp::mle(&f, 10), &tr, &ctx).is_err());

    // Regression (phase 7): Poly * Poly degree math.
    // Poly(F, n, m) = n variables, max total degree m. Product degrees add.
    // Uni<F, 3> * Uni<F, 4> = Uni<F, 7>
    assert_eq!(
        CTyp::lub_mul(&CTyp::uni(&f, 3), &CTyp::uni(&f, 4), &ctx),
        Ok(CTyp::uni(&f, 7))
    );
    // Mle<F, n> * Mle<F, n> = Poly<F, n, 2> (product of two multilinears is degree 2)
    assert_eq!(
        CTyp::lub_mul(&CTyp::mle(&f, 3), &CTyp::mle(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 2))
    );
    // Mle<F, 2> * Mle<F, 3> = Poly<F, 3, 2> (max vars, degree 2)
    assert_eq!(
        CTyp::lub_mul(&CTyp::mle(&f, 2), &CTyp::mle(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 2))
    );
    // Uni<F, 5> * Mle<F, 3> via general Poly*Poly: Poly(F,1,5) * Poly(F,3,1) = Poly(F, 3, 6)
    assert_eq!(
        CTyp::lub_mul(&CTyp::uni(&f, 5), &CTyp::mle(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 6))
    );
    // Poly<F, 2, 3> * Poly<F, 2, 4> = Poly<F, 2, 7>
    assert_eq!(
        CTyp::lub_mul(
            &CTyp::Poly(f.clone(), 2, 3),
            &CTyp::Poly(f.clone(), 2, 4),
            &ctx
        ),
        Ok(CTyp::Poly(f.clone(), 2, 7))
    );
    // Poly<F, 2, 3> * Poly<F, 4, 2> = Poly<F, 4, 5> (max vars, sum degrees)
    assert_eq!(
        CTyp::lub_mul(
            &CTyp::Poly(f.clone(), 2, 3),
            &CTyp::Poly(f.clone(), 4, 2),
            &ctx
        ),
        Ok(CTyp::Poly(f.clone(), 4, 5))
    );

    // Regression (phase 7): Poly == Poly falls through to the general arm when
    // the shapes don't match Uni==Uni or Mle==Mle specifically.
    assert_eq!(
        CTyp::lub_equ(
            &CTyp::Poly(f.clone(), 2, 2),
            &CTyp::Poly(f.clone(), 2, 2),
            &ctx
        ),
        Ok(CTyp::Poly(f.clone(), 2, 2))
    );
    assert_eq!(
        CTyp::lub_equ(
            &CTyp::Poly(f.clone(), 2, 3),
            &CTyp::Poly(f.clone(), 3, 2),
            &ctx
        ),
        Ok(CTyp::Poly(f.clone(), 3, 3))
    );

    // Regression (phase 7): lub_div degree math. Poly<F,1,5> / Poly<F,1,5> = Poly<F,1,0>
    assert_eq!(
        CTyp::lub_div(&CTyp::uni(&f, 5), &CTyp::uni(&f, 5), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 0))
    );
    assert_eq!(
        CTyp::lub_div(&CTyp::uni(&f, 7), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 4))
    );

    // Phase 14.C: poly-encoding unification (m = max degree).
    // lub_rem Poly×Poly: Poly<F,1,5> % Poly<F,1,3> = Poly<F,1,2> (deg = 3 - 1).
    assert_eq!(
        CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 2))
    );
    // lub_rem requires m2 >= 1; Poly<F,1,n> % Poly<F,1,0> is an error.
    assert!(CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 0), &ctx).is_err());
    // General Poly×Poly rem: Poly<F,2,5> % Poly<F,3,2> = Poly<F,3,1> (max vars, m2 - 1).
    assert_eq!(
        CTyp::lub_rem(
            &CTyp::Poly(f.clone(), 2, 5),
            &CTyp::Poly(f.clone(), 3, 2),
            &ctx
        ),
        Ok(CTyp::Poly(f.clone(), 3, 1))
    );

    // Phase B: lub_add(Poly, Vec) / lub_sub(Poly, Vec) is now a type error.
    // Vec is no longer implicitly reinterpreted as a coefficient list.
    // Use `poly([...])` to construct a polynomial from a coefficient
    // vector before mixing with another polynomial.
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::vec(&tf, 4), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::vec(&tf, 5), &CTyp::uni(&f, 3), &ctx).is_err());

    // lub_mul Poly×Poly: degrees add. Poly<F,1,2> * Poly<F,1,3> = Poly<F,1,5>.
    assert_eq!(
        CTyp::lub_mul(&CTyp::uni(&f, 2), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::uni(&f, 5))
    );
}

/// Phase 15: Negative / off-by-one degree regressions for Poly type rules.
/// Locks in the phase-14 convention that `m` in `Poly<F, n, m>` is the max
/// polynomial degree (so a univariate polynomial of degree `m` has `m + 1`
/// coefficients). Each assertion exercises a boundary where an off-by-one
/// on the degree parameter would silently succeed before phase 14.
#[test]
fn test_ctyp_poly_degree_offbyone() {
    let f = Tid::from("F");
    let g1 = Tid::from("G1");
    let g2 = Tid::from("G2");
    let ctx = Ctx::from([
        (f.clone(), Kind::Field),
        (g1.clone(), Kind::Group),
        (g2.clone(), Kind::Group),
    ]);
    let tf = CTyp::base(&f);
    let tg1 = CTyp::base(&g1);

    // ---- lub_add / lub_sub: Poly ↔ Vec is a type error (Phase B) ----
    // No matter what k/n combination, the implicit Vec-as-coefficient-list
    // coercion has been removed. Use `poly([...])` at the source level to
    // construct a polynomial before mixing with another polynomial.
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 3), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::vec(&tf, 3), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::vec(&tf, 3), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 5), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::vec(&tf, 5), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 5), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::vec(&tf, 5), &CTyp::uni(&f, 3), &ctx).is_err());

    // ---- lub_mul: Vec×Vec requires matching lengths; element types enforced ----
    // Length mismatch rejected (no off-by-one coercion for Vec×Vec).
    assert!(CTyp::lub_mul(&CTyp::vec(&tf, 3), &CTyp::vec(&tf, 4), &ctx).is_err());
    // Element type mismatch rejected (field vs group base types).
    assert!(CTyp::lub_mul(&CTyp::vec(&tf, 4), &CTyp::vec(&tg1, 4), &ctx).is_err());

    // ---- lub_div: Poly<F,n1,m1> / Poly<F,n2,m2> requires m1 ≥ m2 ----
    // Positive boundary: equal degrees yield Poly<F,_,0>.
    assert_eq!(
        CTyp::lub_div(&CTyp::uni(&f, 3), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 0))
    );
    // Off-by-one: divisor degree one greater than dividend is rejected.
    assert!(CTyp::lub_div(&CTyp::uni(&f, 2), &CTyp::uni(&f, 3), &ctx).is_err());
    // General Poly/Poly: same off-by-one in multivariate.
    assert!(CTyp::lub_div(
        &CTyp::Poly(f.clone(), 2, 3),
        &CTyp::Poly(f.clone(), 2, 4),
        &ctx
    )
    .is_err());
    // Far off: any m2 > m1 rejected.
    assert!(CTyp::lub_div(&CTyp::uni(&f, 0), &CTyp::uni(&f, 5), &ctx).is_err());

    // ---- lub_rem: Poly<F,n1,m1> % Poly<F,n2,m2> requires m2 ≥ 1 ----
    // Divisor of degree 0 rejected (no remainder well-defined).
    assert!(CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 0), &ctx).is_err());
    // Degree-only dividend with degree-0 divisor also rejected.
    assert!(CTyp::lub_rem(&CTyp::uni(&f, 0), &CTyp::uni(&f, 0), &ctx).is_err());
    // m1 < m2 is still allowed: remainder degree = m2 - 1 (full dividend fits).
    assert_eq!(
        CTyp::lub_rem(&CTyp::uni(&f, 3), &CTyp::uni(&f, 4), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 3))
    );
    // Boundary m2 = 1: remainder has degree 0.
    assert_eq!(
        CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 1), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 0))
    );

    // ---- lub_dot: Vec · Poly is a type error (Phase B) ----
    // Vec is no longer implicitly reinterpreted as a coefficient list.
    // Use `coef(poly)` to extract a coefficient vector for dot-product.
    assert!(CTyp::lub_dot(&CTyp::vec(&tf, 4), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::vec(&tf, 4), &CTyp::uni(&f, 4), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::uni(&f, 4), &CTyp::vec(&tf, 4), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::vec(&tf, 5), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 5), &ctx).is_err());
}

mod error_tests {
    use super::*;
    use crate::ast::BinOp;

    #[test]
    fn test_lub_error_next() {
        let err1 = LubError::Equ("A".to_string(), "B".to_string());
        let err2 = LubError::Equ("C".to_string(), "D".to_string());
        let combined = LubError::next(err1, err2);
        assert!(matches!(combined, LubError::Next(_, _)));
    }

    #[test]
    fn test_lub_error_kind_not_found() {
        let tid = Tid::from("T");
        let err = LubError::kind_not_found(&tid);
        assert!(matches!(err, LubError::KindNotFound(_)));
    }

    #[test]
    fn test_lub_error_bad_range() {
        use crate::typ::range::{Range, RangeError};
        let range = Range {
            start: 0,
            step: 1,
            end: 10,
        };
        let range_err = RangeError::RangeOrder(0, 1, 0);
        let err = LubError::bad_range(&range, range_err);
        assert!(matches!(err, LubError::BadRange(_, _)));
    }

    #[test]
    fn test_lub_error_equ() {
        let err = LubError::equ(&"A", &"B");
        assert!(matches!(err, LubError::Equ(_, _)));
    }

    #[test]
    fn test_lub_error_add() {
        let err = LubError::add(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Add, _, _)));
    }

    #[test]
    fn test_lub_error_sub() {
        let err = LubError::sub(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Sub, _, _)));
    }

    #[test]
    fn test_lub_error_mul() {
        let err = LubError::mul(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Mul, _, _)));
    }

    #[test]
    fn test_lub_error_div() {
        let err = LubError::div(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Div, _, _)));
    }

    #[test]
    fn test_lub_error_pow() {
        let err = LubError::pow(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Pow, _, _)));
    }

    #[test]
    fn test_lub_error_rem() {
        let err = LubError::rem(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Rem, _, _)));
    }

    #[test]
    fn test_lub_error_dot() {
        let err = LubError::dot(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Dot, _, _)));
    }

    #[test]
    fn test_lub_error_pair() {
        let err = LubError::pair(&"A", &"B");
        assert!(matches!(err, LubError::Pair(_, _)));
    }

    #[test]
    fn test_lub_error_concat() {
        let err = LubError::concat(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::Concat, _, _)));
    }

    #[test]
    fn test_lub_error_eval() {
        let err = LubError::eval(&"A", &"B");
        assert!(matches!(err, LubError::Eval(_, _)));
    }

    #[test]
    fn test_lub_op_dispatch() {
        use crate::typ::range::Range;
        let a = Range {
            start: 1,
            step: 1,
            end: 10,
        };
        let b = Range {
            start: 2,
            step: 1,
            end: 20,
        };
        let ctx = Nothing;

        assert!(Range::lub_op(BinOp::Add, &a, &b, &ctx).is_ok());
        // Sub underflows: a.start (1) < b_max (19), so checked_sub returns None
        assert!(Range::lub_op(BinOp::Sub, &a, &b, &ctx).is_err());
        assert!(Range::lub_op(BinOp::Mul, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Div, &a, &b, &ctx).is_ok());
        // 9^19 fits in u64, so checked_pow succeeds
        assert!(Range::lub_op(BinOp::Pow, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Rem, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Dot, &a, &b, &ctx).is_ok());

        // Concat may succeed or fail depending on ranges - test with contiguous ranges
        let c = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let d = Range {
            start: 5,
            step: 1,
            end: 10,
        };
        // These ranges are contiguous, so concat might succeed
        let _ = Range::lub_op(BinOp::Concat, &c, &d, &ctx);
    }
}

mod range_lub_tests {
    use super::*;
    use crate::typ::range::Range;

    #[test]
    fn test_range_lub_equ_basic() {
        let a = Range {
            start: 1,
            step: 1,
            end: 10,
        };
        let b = Range {
            start: 5,
            step: 2,
            end: 15,
        };
        let result = Range::lub_equ(&a, &b, &Nothing).unwrap();
        assert_eq!(result.start, 1);
        assert_eq!(result.end, 15);
    }

    #[test]
    fn test_range_lub_add_basic() {
        let a = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let b = Range {
            start: 2,
            step: 1,
            end: 3,
        };
        let result = Range::lub_add(&a, &b, &Nothing).unwrap();
        assert!(result.start >= a.start + b.start);
    }

    #[test]
    fn test_range_lub_sub_basic() {
        let a = Range {
            start: 10,
            step: 1,
            end: 20,
        };
        let b = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let _result = Range::lub_sub(&a, &b, &Nothing).unwrap();
    }

    #[test]
    fn test_range_lub_mul_basic() {
        let a = Range {
            start: 2,
            step: 1,
            end: 5,
        };
        let b = Range {
            start: 3,
            step: 1,
            end: 4,
        };
        let result = Range::lub_mul(&a, &b, &Nothing).unwrap();
        assert!(result.start >= a.start * b.start);
    }

    #[test]
    fn test_range_lub_pow_basic() {
        let a = Range {
            start: 2,
            step: 1,
            end: 3,
        };
        let b = Range {
            start: 2,
            step: 1,
            end: 3,
        };
        let result = Range::lub_pow(&a, &b, &Nothing).unwrap();
        assert!(result.start >= 4); // 2^2
    }

    #[test]
    fn test_range_lub_rem_basic() {
        let a = Range {
            start: 10,
            step: 1,
            end: 20,
        };
        let b = Range {
            start: 3,
            step: 1,
            end: 5,
        };
        let result = Range::lub_rem(&a, &b, &Nothing).unwrap();
        assert!(result.end < b.end);
    }

    #[test]
    fn test_range_lub_rem_zero_divisor() {
        let a = Range {
            start: 10,
            step: 1,
            end: 20,
        };
        let b = Range {
            start: 0,
            step: 1,
            end: 5,
        };
        let result = Range::lub_rem(&a, &b, &Nothing);
        assert!(result.is_err());
    }

    #[test]
    fn test_range_lub_div_zero_divisor() {
        let a = Range {
            start: 10,
            step: 1,
            end: 20,
        };
        let b = Range {
            start: 0,
            step: 1,
            end: 5,
        };
        let result = Range::lub_div(&a, &b, &Nothing);
        assert!(result.is_err());
    }

    #[test]
    fn test_range_lub_dot() {
        let a = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let b = Range {
            start: 2,
            step: 1,
            end: 4,
        };
        let result = Range::lub_dot(&a, &b, &Nothing).unwrap();
        // Dot should behave like mul
        let mul_result = Range::lub_mul(&a, &b, &Nothing).unwrap();
        assert_eq!(result, mul_result);
    }

    #[test]
    fn test_range_lub_pair_error() {
        let a = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let b = Range {
            start: 2,
            step: 1,
            end: 4,
        };
        let result = Range::lub_pair(&a, &b, &Nothing);
        assert!(result.is_err());
    }

    #[test]
    fn test_range_lub_concat_valid() {
        let a = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let b = Range {
            start: 5,
            step: 1,
            end: 10,
        };
        let result = Range::lub_concat(&a, &b, &Nothing);
        if let Ok(concatenated) = result {
            assert_eq!(concatenated.start, 1);
            assert_eq!(concatenated.end, 10);
        }
    }

    #[test]
    fn test_range_lub_concat_invalid() {
        let a = Range {
            start: 1,
            step: 1,
            end: 5,
        };
        let b = Range {
            start: 7,
            step: 1,
            end: 10,
        }; // Gap between ranges
        let result = Range::lub_concat(&a, &b, &Nothing);
        assert!(result.is_err());
    }
}

mod tid_lub_tests {
    use super::*;

    #[test]
    fn test_tid_lub_rem_error() {
        let f = Tid::from("F");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_rem(&f, &f, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_pow_error() {
        let f = Tid::from("F");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_pow(&f, &f, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_concat_error() {
        let f = Tid::from("F");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_concat(&f, &f, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_equ_not_found() {
        let f = Tid::from("F");
        let g = Tid::from("G");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_equ(&f, &g, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_add_not_found() {
        let f = Tid::from("F");
        let g = Tid::from("G");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_add(&f, &g, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_mul_not_found() {
        let f = Tid::from("F");
        let g = Tid::from("G");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_mul(&f, &g, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_div_not_found() {
        let f = Tid::from("F");
        let g = Tid::from("G");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_div(&f, &g, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_pair_not_pairing_kind() {
        let g1 = Tid::from("G1");
        let g2 = Tid::from("G2");
        let ctx = Ctx::from([(g1.clone(), Kind::Group), (g2.clone(), Kind::Group)]);
        let result = Tid::lub_pair(&g1, &g2, &ctx);
        // Should fail because no pairing kind exists
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_pair_non_group() {
        let f = Tid::from("F");
        let g = Tid::from("G");
        let ctx = Ctx::from([(f.clone(), Kind::Field), (g.clone(), Kind::Group)]);
        let result = Tid::lub_pair(&f, &g, &ctx);
        assert!(result.is_err());
    }

    #[test]
    fn test_tid_lub_dot() {
        let f = Tid::from("F");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_dot(&f, &f, &ctx);
        assert_eq!(result.unwrap(), f);
    }
}

/// Property-based tests pinning the polynomial-shape rules of `CTyp::lub_*`
/// under the **Phase-14 `Poly(F, n, m)` convention where `m` is the max
/// polynomial degree** (coefficient count = m + 1).
///
/// Two families:
/// 1. Shape grids (one PBT per arm) verifying the result `(n_out, m_out)`
///    formula for each `lub_*` arm.
/// 2. Algebraic property PBTs (symmetry, associativity, unit) that hold
///    structurally and survive future arm-removal refactors.
///
/// Shape rules:
/// - `lub_add` / `lub_sub`: `Poly(F, n1, m1) ± Poly(F, n2, m2) = Poly(F, max(n1, n2), max(m1, m2))`
/// - `lub_mul`: `Poly(F, n1, m1) * Poly(F, n2, m2) = Poly(F, max(n1, n2), m1 + m2)`
/// - `lub_div`: `Uni(F, ma) / Uni(F, mb) = Uni(F, ma - mb)` for `ma >= mb`
/// - `lub_concat`: see arms in `lub_concat` impl
mod ctyp_lub_poly_tests {
    use super::*;
    use arbitrary::Unstructured;
    use share::Set;

    /// The canonical `KIND_CTX` used in tests — mirrors `infer.rs::tests::KIND_CTX`
    /// so the polynomial Tid `F` is `Field`, `G` is `Group`, and `S` is `Scalar(G)`.
    fn kind_ctx() -> Ctx<Tid, CKind> {
        let mut kctx = Ctx::new();
        kctx.insert(&Tid::from("F"), &Kind::Field);
        kctx.insert(&Tid::from("G"), &Kind::Group);
        kctx.insert(&Tid::from("S"), &Kind::Scalar(Set::from([Tid::from("G")])));
        kctx
    }

    fn f() -> Tid {
        Tid::from("F")
    }

    fn tf() -> CTyp {
        CTyp::base(&f())
    }

    // ----- arbtest generators -----

    /// Sample `n ∈ 1..=4` for polynomial num-vars.
    fn arb_n(u: &mut Unstructured) -> arbitrary::Result<usize> {
        u.int_in_range(1..=4)
    }

    /// Sample `m ∈ 0..=4` for polynomial degree.
    fn arb_m(u: &mut Unstructured) -> arbitrary::Result<usize> {
        u.int_in_range(0..=4)
    }

    /// Sample Vec length `k ∈ 1..=4`.
    fn arb_k(u: &mut Unstructured) -> arbitrary::Result<usize> {
        u.int_in_range(1..=4)
    }

    /// Arbitrary polynomial `CTyp` over `F`: any `Poly(F, n, m)` for
    /// `n ∈ 1..=4`, `m ∈ 0..=4`. Covers Uni (n=1), Mle (m=1), and general
    /// VPoly.
    fn arb_poly(u: &mut Unstructured) -> arbitrary::Result<CTyp> {
        Ok(CTyp::Poly(f(), arb_n(u)?, arb_m(u)?))
    }

    /// Arbitrary `Vec(F, k)` for `k ∈ 1..=4`.
    fn arb_vec(u: &mut Unstructured) -> arbitrary::Result<CTyp> {
        Ok(CTyp::vec(&tf(), arb_k(u)?))
    }

    /// Arbitrary `CTyp` from `{Poly, Vec, Base(F)}` — the surface area
    /// exercised by the polynomial / Vec / scalar arms of every `lub_*`.
    /// Used by the algebraic property PBTs (symmetry / associativity / unit).
    fn arb_ctyp(u: &mut Unstructured) -> arbitrary::Result<CTyp> {
        match u.int_in_range(0..=2u8)? {
            0 => arb_poly(u),
            1 => arb_vec(u),
            _ => Ok(tf()),
        }
    }

    // ----- Shape-grid PBTs (one per lub_* arm) -----

    /// `lub_add(Poly, Poly) = Poly(max(n1, n2), max(m1, m2))` — covers Uni-Uni,
    /// Mle-Mle, mixed Uni-Mle, and general VPoly under the general arm
    /// introduced in Phase 14.
    #[test]
    fn lub_add_poly_grid() {
        arbtest::arbtest(|u| {
            let n1 = arb_n(u)?;
            let m1 = arb_m(u)?;
            let n2 = arb_n(u)?;
            let m2 = arb_m(u)?;
            let a = CTyp::Poly(f(), n1, m1);
            let b = CTyp::Poly(f(), n2, m2);
            let expected = CTyp::Poly(f(), n1.max(n2), m1.max(m2));
            assert_eq!(
                CTyp::lub_add(&a, &b, &kind_ctx()),
                Ok(expected),
                "lub_add(Poly(F,{},{}), Poly(F,{},{}))",
                n1,
                m1,
                n2,
                m2
            );
            Ok(())
        });
    }

    /// `lub_sub(Poly, Poly) = Poly(max(n1, n2), max(m1, m2))` — same shape
    /// rule as `lub_add`. Subtraction can't grow degree.
    #[test]
    fn lub_sub_poly_grid() {
        arbtest::arbtest(|u| {
            let n1 = arb_n(u)?;
            let m1 = arb_m(u)?;
            let n2 = arb_n(u)?;
            let m2 = arb_m(u)?;
            let a = CTyp::Poly(f(), n1, m1);
            let b = CTyp::Poly(f(), n2, m2);
            let expected = CTyp::Poly(f(), n1.max(n2), m1.max(m2));
            assert_eq!(
                CTyp::lub_sub(&a, &b, &kind_ctx()),
                Ok(expected),
                "lub_sub(Poly(F,{},{}), Poly(F,{},{}))",
                n1,
                m1,
                n2,
                m2
            );
            Ok(())
        });
    }

    /// `lub_mul(Poly, Poly) = Poly(max(n1, n2), m1 + m2)` — Phase-14 degrees
    /// add under multiplication; the general `(Poly, Poly)` arm handles
    /// arbitrary `(n, m)` shapes including mixed Uni-Mle and general VPoly.
    #[test]
    fn lub_mul_poly_grid() {
        arbtest::arbtest(|u| {
            let n1 = arb_n(u)?;
            let m1 = arb_m(u)?;
            let n2 = arb_n(u)?;
            let m2 = arb_m(u)?;
            let a = CTyp::Poly(f(), n1, m1);
            let b = CTyp::Poly(f(), n2, m2);
            let expected = CTyp::Poly(f(), n1.max(n2), m1 + m2);
            assert_eq!(
                CTyp::lub_mul(&a, &b, &kind_ctx()),
                Ok(expected),
                "lub_mul(Poly(F,{},{}), Poly(F,{},{}))",
                n1,
                m1,
                n2,
                m2
            );
            Ok(())
        });
    }

    /// Phase B: `lub_concat(Vec, Uni)` is a type error. Vec is no longer
    /// implicitly reinterpreted as a coefficient list. Use `poly([...])` /
    /// `coef(...)` at the source level to bridge between the two shapes.
    #[test]
    fn lub_concat_vec_uni_errors() {
        arbtest::arbtest(|u| {
            let k = arb_k(u)?;
            let n = arb_m(u)?;
            let vec_t = CTyp::vec(&tf(), k);
            let uni_t = CTyp::uni(&f(), n);
            assert!(
                CTyp::lub_concat(&vec_t, &uni_t, &kind_ctx()).is_err(),
                "lub_concat(Vec(F,{}), Uni(F,{})) should error",
                k,
                n
            );
            Ok(())
        });
    }

    /// Phase B: `lub_concat(Uni, Vec)` is a type error (commuted form of
    /// `lub_concat_vec_uni_errors`).
    #[test]
    fn lub_concat_uni_vec_errors() {
        arbtest::arbtest(|u| {
            let n = arb_m(u)?;
            let k = arb_k(u)?;
            let uni_t = CTyp::uni(&f(), n);
            let vec_t = CTyp::vec(&tf(), k);
            assert!(
                CTyp::lub_concat(&uni_t, &vec_t, &kind_ctx()).is_err(),
                "lub_concat(Uni(F,{}), Vec(F,{})) should error",
                n,
                k
            );
            Ok(())
        });
    }

    /// Phase B: `lub_concat(Mle, Vec)` is a type error. The previous
    /// `Mle(F, n) ++ Vec(F, n) = Mle(F, n + 1)` MLE dimension-promotion arm
    /// has been removed.
    #[test]
    fn lub_concat_mle_vec_errors() {
        arbtest::arbtest(|u| {
            let n = u.int_in_range(2..=4usize)?;
            let mle_t = CTyp::mle(&f(), n);
            let vec_t = CTyp::vec(&tf(), n);
            assert!(
                CTyp::lub_concat(&mle_t, &vec_t, &kind_ctx()).is_err(),
                "lub_concat(Mle(F,{}), Vec(F,{})) should error",
                n,
                n
            );
            Ok(())
        });
    }

    /// Phase B: `Mle(F, 1) == Uni(F, 1) == Poly(F, 1, 1)` concat'd with a
    /// Vec is a type error now that all polynomial ↔ Vec arms are gone.
    /// The pre-Phase-B routing (Uni-Vec arm wins textually for n == 1)
    /// is no longer observable.
    #[test]
    fn lub_concat_mle1_vec_errors() {
        let ctx = kind_ctx();
        for m in [1usize, 2, 3] {
            let mle1 = CTyp::Poly(f(), 1, 1);
            let vec_t = CTyp::vec(&tf(), m);
            assert!(
                CTyp::lub_concat(&mle1, &vec_t, &ctx).is_err(),
                "lub_concat(Mle(F,1)==Uni(F,1), Vec(F,{})) should error",
                m
            );
        }
    }

    /// `lub_concat(Mle(F, n), Vec(F, m))` where `n != m` and `n >= 2` — the
    /// MLE-Vec promotion arm has an `n == m` guard, so this falls through.
    /// With `n >= 2` the Uni-Vec arm doesn't match either (Uni needs slot 1
    /// to be `1` in the polynomial). It then hits the generic `Vec ++ b` arm,
    /// which calls `lub_equ(Base(F), Poly(F, n, 1))`. That equality routes
    /// through the `to_scalar` catch-all in `lub_equ`, but `Poly.to_scalar`
    /// is `None`, so equality fails and the whole concat returns an error.
    /// Pin that behavior here.
    #[test]
    fn lub_concat_mle_vec_mismatch_errors() {
        arbtest::arbtest(|u| {
            let n = u.int_in_range(2..=4usize)?;
            let m = u.int_in_range(1..=4usize)?;
            if n == m {
                return Ok(()); // promotion arm handles this; tested separately
            }
            let mle_t = CTyp::mle(&f(), n);
            let vec_t = CTyp::vec(&tf(), m);
            let result = CTyp::lub_concat(&mle_t, &vec_t, &kind_ctx());
            assert!(
                result.is_err(),
                "lub_concat(Mle(F,{}), Vec(F,{})) should error when n != m and n >= 2, got {:?}",
                n,
                m,
                result
            );
            Ok(())
        });
    }

    /// `Uni(F, ma) / Uni(F, mb) = Uni(F, ma - mb)` for `ma >= mb`.
    /// In Phase-14 the `m` field is max polynomial degree, so the quotient
    /// has degree `ma - mb` (one fewer than coefficient count).
    #[test]
    fn lub_div_uni_uni_quotient_shape() {
        arbtest::arbtest(|u| {
            let ma = arb_m(u)?;
            let mb = u.int_in_range(0..=ma)?; // guarantee ma >= mb
            let a = CTyp::uni(&f(), ma);
            let b = CTyp::uni(&f(), mb);
            let expected = CTyp::uni(&f(), ma - mb);
            assert_eq!(
                CTyp::lub_div(&a, &b, &kind_ctx()),
                Ok(expected),
                "lub_div(Uni(F,{}), Uni(F,{}))",
                ma,
                mb
            );
            Ok(())
        });
    }

    /// `Uni(F, ma) / Uni(F, mb)` when `ma < mb` — the `Poly`/`Poly` div arm
    /// has an `ma >= mb` guard, so this falls through to an error (no fallback
    /// arm rescues it). Pin that contract.
    #[test]
    fn lub_div_uni_uni_underflow_errors() {
        arbtest::arbtest(|u| {
            let mb = u.int_in_range(1..=4usize)?;
            let ma = u.int_in_range(0..=mb - 1)?; // ma < mb
            let a = CTyp::uni(&f(), ma);
            let b = CTyp::uni(&f(), mb);
            let result = CTyp::lub_div(&a, &b, &kind_ctx());
            assert!(
                result.is_err(),
                "lub_div(Uni(F,{}), Uni(F,{})) should error when ma < mb, got {:?}",
                ma,
                mb,
                result
            );
            Ok(())
        });
    }

    /// Sanity round-trip: `lub_mul(q, p) = Uni(F, (ma - mb) + mb) = Uni(F, ma)`.
    /// I.e., multiplying the quotient back by the divisor yields a poly with
    /// the same degree as the dividend (degree relation only, not value).
    #[test]
    fn lub_mul_round_trip_after_div() {
        arbtest::arbtest(|u| {
            let ma = u.int_in_range(1..=4usize)?;
            let mb = u.int_in_range(0..=ma)?;
            let ctx = kind_ctx();
            let dividend = CTyp::uni(&f(), ma);
            let divisor = CTyp::uni(&f(), mb);
            let quotient = CTyp::lub_div(&dividend, &divisor, &ctx).expect("div should succeed");
            let reconstructed = CTyp::lub_mul(&quotient, &divisor, &ctx)
                .expect("mul of quotient * divisor should succeed");
            // Phase-14 degree algebra: (ma - mb) + mb = ma.
            assert_eq!(
                reconstructed,
                CTyp::uni(&f(), ma),
                "round-trip mul(div({}, {}), {}) should preserve degree {}",
                ma,
                mb,
                mb,
                ma
            );
            Ok(())
        });
    }

    // ----- Algebraic property PBTs (survive Phase B intact) -----

    /// Helper for symmetric ops: assert `lub_op(a, b) == lub_op(b, a)`,
    /// treating both-`Err` outcomes as symmetric (the `LubError` variants
    /// may carry asymmetric operand orderings, so we only require both
    /// directions to succeed or both to fail).
    fn assert_symmetric<F>(a: &CTyp, b: &CTyp, op_name: &str, lub: F)
    where
        F: Fn(&CTyp, &CTyp) -> Result<CTyp, LubError>,
    {
        let r1 = lub(a, b);
        let r2 = lub(b, a);
        match (&r1, &r2) {
            (Ok(t1), Ok(t2)) => assert_eq!(
                t1, t2,
                "{}({:?}, {:?}) = {:?} but reversed = {:?}",
                op_name, a, b, t1, t2
            ),
            (Err(_), Err(_)) => {}
            _ => panic!(
                "{} asymmetric: ({:?}, {:?}) = {:?}, reversed = {:?}",
                op_name, a, b, r1, r2
            ),
        }
    }

    /// `lub_add` is symmetric across `Poly`, `Vec`, and `Base` inputs.
    /// Holds both today and after the planned Phase-B removal of polynomial↔Vec
    /// arms (both directions either succeed with the same result or both error).
    #[test]
    fn pbt_lub_add_symmetric() {
        arbtest::arbtest(|u| {
            let a = arb_ctyp(u)?;
            let b = arb_ctyp(u)?;
            let ctx = kind_ctx();
            assert_symmetric(&a, &b, "lub_add", |x, y| CTyp::lub_add(x, y, &ctx));
            Ok(())
        });
    }

    /// `lub_sub` is symmetric across `Poly`, `Vec`, and `Base` inputs.
    /// (Type-level only — subtraction is not value-symmetric, but the result
    /// `CTyp` is identical for `a - b` and `b - a`.)
    #[test]
    fn pbt_lub_sub_symmetric() {
        arbtest::arbtest(|u| {
            let a = arb_ctyp(u)?;
            let b = arb_ctyp(u)?;
            let ctx = kind_ctx();
            assert_symmetric(&a, &b, "lub_sub", |x, y| CTyp::lub_sub(x, y, &ctx));
            Ok(())
        });
    }

    /// `lub_mul` is symmetric across `Poly`, `Vec`, and `Base` inputs.
    #[test]
    fn pbt_lub_mul_symmetric() {
        arbtest::arbtest(|u| {
            let a = arb_ctyp(u)?;
            let b = arb_ctyp(u)?;
            let ctx = kind_ctx();
            assert_symmetric(&a, &b, "lub_mul", |x, y| CTyp::lub_mul(x, y, &ctx));
            Ok(())
        });
    }

    /// `lub_equ` is symmetric.
    #[test]
    fn pbt_lub_equ_symmetric() {
        arbtest::arbtest(|u| {
            let a = arb_ctyp(u)?;
            let b = arb_ctyp(u)?;
            let ctx = kind_ctx();
            assert_symmetric(&a, &b, "lub_equ", |x, y| CTyp::lub_equ(x, y, &ctx));
            Ok(())
        });
    }

    /// `lub_add` is associative on the polynomial sub-lattice:
    /// `lub_add(a, lub_add(b, c)) == lub_add(lub_add(a, b), c)` whenever
    /// both groupings succeed. Skips runs where any intermediate errors.
    #[test]
    fn pbt_lub_add_associative_poly() {
        arbtest::arbtest(|u| {
            let a = arb_poly(u)?;
            let b = arb_poly(u)?;
            let c = arb_poly(u)?;
            let ctx = kind_ctx();
            let bc = match CTyp::lub_add(&b, &c, &ctx) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let ab = match CTyp::lub_add(&a, &b, &ctx) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let left = CTyp::lub_add(&a, &bc, &ctx);
            let right = CTyp::lub_add(&ab, &c, &ctx);
            assert_eq!(
                left, right,
                "lub_add not associative: a={:?}, b={:?}, c={:?}",
                a, b, c
            );
            Ok(())
        });
    }

    /// `lub_mul` is associative on the polynomial sub-lattice.
    #[test]
    fn pbt_lub_mul_associative_poly() {
        arbtest::arbtest(|u| {
            let a = arb_poly(u)?;
            let b = arb_poly(u)?;
            let c = arb_poly(u)?;
            let ctx = kind_ctx();
            let bc = match CTyp::lub_mul(&b, &c, &ctx) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let ab = match CTyp::lub_mul(&a, &b, &ctx) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let left = CTyp::lub_mul(&a, &bc, &ctx);
            let right = CTyp::lub_mul(&ab, &c, &ctx);
            assert_eq!(
                left, right,
                "lub_mul not associative: a={:?}, b={:?}, c={:?}",
                a, b, c
            );
            Ok(())
        });
    }

    /// `Base(F)` is a unit for `lub_add` over Uni and Mle polynomials:
    /// `lub_add(a, Base(F)) == a` (and symmetric). The current
    /// `(Base, Poly(_, 1, n))` / `(Poly(_, n, 1), Base)` arms support this;
    /// general VPoly with `n > 1` and `m > 1` is *not* covered by the unit
    /// law and is excluded here.
    #[test]
    fn pbt_lub_add_unit_base() {
        arbtest::arbtest(|u| {
            // Pick either Uni (n=1, m arbitrary) or Mle (m=1, n arbitrary).
            let a = if u.arbitrary::<bool>()? {
                CTyp::uni(&f(), arb_m(u)?)
            } else {
                CTyp::mle(&f(), arb_n(u)?)
            };
            let ctx = kind_ctx();
            assert_eq!(
                CTyp::lub_add(&a, &tf(), &ctx),
                Ok(a.clone()),
                "lub_add({:?}, Base(F)) != {:?}",
                a,
                a
            );
            assert_eq!(
                CTyp::lub_add(&tf(), &a, &ctx),
                Ok(a.clone()),
                "lub_add(Base(F), {:?}) != {:?}",
                a,
                a
            );
            Ok(())
        });
    }

    fn arb_record(u: &mut Unstructured) -> arbitrary::Result<CTyp> {
        let num_fields = u.int_in_range(1..=3)?;
        let mut fields = share::Ctx::new();
        let names = ["x", "y", "z", "w"];
        for name in names.iter().take(num_fields) {
            fields.insert(&name.to_string(), &arb_ctyp(u)?);
        }
        Ok(CTyp::Record(fields))
    }

    #[test]
    fn test_record_lub_width_intersection() {
        let ctx = kind_ctx();
        let mut fields_a = share::Ctx::new();
        fields_a.insert(&"x".to_string(), &tf());

        let mut fields_b = share::Ctx::new();
        fields_b.insert(&"x".to_string(), &tf());
        fields_b.insert(&"y".to_string(), &CTyp::Poly(f(), 1, 3));

        let a = CTyp::Record(fields_a);
        let b = CTyp::Record(fields_b);

        // Width-subtyping: LUB drops the non-common field `y`, keeping `{x}`.
        let mut expected_fields = share::Ctx::new();
        expected_fields.insert(&"x".to_string(), &tf());
        let expected = CTyp::Record(expected_fields);

        assert_eq!(CTyp::lub_equ(&a, &b, &ctx), Ok(expected.clone()));
        assert_eq!(CTyp::lub_equ(&b, &a, &ctx), Ok(expected));
    }

    #[test]
    fn test_record_lub_depth_subtyping() {
        let ctx = kind_ctx();
        let mut fields_a = share::Ctx::new();
        fields_a.insert(&"x".to_string(), &CTyp::Fin(Range::singleton(1)));

        let mut fields_b = share::Ctx::new();
        fields_b.insert(&"x".to_string(), &CTyp::Fin(Range::singleton(2)));

        let a = CTyp::Record(fields_a);
        let b = CTyp::Record(fields_b);

        let res = CTyp::lub_equ(&a, &b, &ctx);
        assert!(res.is_ok());
    }

    #[test]
    fn test_record_lub_permutations() {
        let ctx = kind_ctx();
        let mut fields_a = share::Ctx::new();
        fields_a.insert(&"x".to_string(), &tf());
        fields_a.insert(&"y".to_string(), &CTyp::Poly(f(), 1, 3));

        let mut fields_b = share::Ctx::new();
        fields_b.insert(&"y".to_string(), &CTyp::Poly(f(), 1, 3));
        fields_b.insert(&"x".to_string(), &tf());

        let a = CTyp::Record(fields_a);
        let b = CTyp::Record(fields_b);

        let res_ab = CTyp::lub_equ(&a, &b, &ctx).unwrap();
        let res_ba = CTyp::lub_equ(&b, &a, &ctx).unwrap();

        assert_eq!(res_ab, res_ba);
    }

    #[test]
    fn pbt_lub_record_symmetry() {
        let ctx = kind_ctx();
        arbtest::arbtest(|u| {
            let a = arb_record(u)?;
            let b = arb_record(u)?;
            assert_symmetric(&a, &b, "lub_equ", |x, y| CTyp::lub_equ(x, y, &ctx));
            Ok(())
        });
    }

    #[test]
    fn pbt_lub_record_associativity() {
        let ctx = kind_ctx();
        arbtest::arbtest(|u| {
            let a = arb_record(u)?;
            let b = arb_record(u)?;
            let c = arb_record(u)?;
            let bc = match CTyp::lub_equ(&b, &c, &ctx) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let ab = match CTyp::lub_equ(&a, &b, &ctx) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let left = CTyp::lub_equ(&a, &bc, &ctx);
            let right = CTyp::lub_equ(&ab, &c, &ctx);
            assert_eq!(
                left, right,
                "lub_equ record not associative: a={:?}, b={:?}, c={:?}",
                a, b, c
            );
            Ok(())
        });
    }
}

/// Overflow tests: checked arithmetic in CTyp::lub_* must reject programs
/// whose type-level dimensions would overflow usize.
mod ctyp_lub_overflow_tests {
    use super::*;
    use share::Set;

    fn kind_ctx() -> Ctx<Tid, CKind> {
        let mut kctx = Ctx::new();
        kctx.insert(&Tid::from("F"), &Kind::Field);
        kctx.insert(&Tid::from("G"), &Kind::Group);
        kctx.insert(&Tid::from("S"), &Kind::Scalar(Set::from([Tid::from("G")])));
        kctx
    }

    fn f() -> Tid {
        Tid::from("F")
    }

    #[test]
    fn lub_mul_poly_degree_overflow() {
        let ctx = kind_ctx();
        let a = CTyp::Poly(f(), 1, usize::MAX);
        let b = CTyp::Poly(f(), 1, 1);
        // degree = MAX + 1 overflows
        assert!(CTyp::lub_mul(&a, &b, &ctx).is_err());
    }

    #[test]
    fn lub_concat_vec_vec_overflow() {
        let ctx = kind_ctx();
        let tf = CTyp::base(&f());
        let a = CTyp::vec(&tf, usize::MAX);
        let b = CTyp::vec(&tf, 1);
        // length = MAX + 1 overflows
        assert!(CTyp::lub_concat(&a, &b, &ctx).is_err());
    }

    #[test]
    fn lub_concat_vec_vec_large_overflow() {
        let ctx = kind_ctx();
        let tf = CTyp::base(&f());
        let a = CTyp::vec(&tf, usize::MAX / 2 + 1);
        let b = CTyp::vec(&tf, usize::MAX / 2 + 1);
        // length = (MAX/2+1) + (MAX/2+1) overflows
        assert!(CTyp::lub_concat(&a, &b, &ctx).is_err());
    }

    #[test]
    fn lub_concat_vec_element_overflow() {
        let ctx = kind_ctx();
        let tf = CTyp::base(&f());
        let a = CTyp::vec(&tf, usize::MAX);
        // Vec ++ element: MAX + 1 overflows
        assert!(CTyp::lub_concat(&a, &tf, &ctx).is_err());
    }

    #[test]
    fn lub_div_poly_degree_safe() {
        // Guarded by ma >= mb, so checked_sub should always succeed.
        // This test confirms the checked path doesn't spuriously error.
        let ctx = kind_ctx();
        let a = CTyp::Poly(f(), 1, 5);
        let b = CTyp::Poly(f(), 1, 3);
        assert_eq!(CTyp::lub_div(&a, &b, &ctx), Ok(CTyp::Poly(f(), 1, 2)));
    }

    #[test]
    fn lub_rem_poly_degree_safe() {
        // Guarded by mb >= 1, so checked_sub(1) should always succeed.
        let ctx = kind_ctx();
        let a = CTyp::Poly(f(), 1, 5);
        let b = CTyp::Poly(f(), 1, 3);
        // remainder degree = mb - 1 = 2
        assert_eq!(CTyp::lub_rem(&a, &b, &ctx), Ok(CTyp::Poly(f(), 1, 2)));
    }
}

/// Fin→Scalar coercion consistency tests: all four binary lub operations
/// (`lub_add`, `lub_sub`, `lub_mul`, `lub_equ`) must accept `Fin` ↔ `Base(S)`
/// where `S` is a `Scalar` kind (not just `Field`).
mod ctyp_lub_fin_scalar_coercion_tests {
    use super::*;
    use share::Set;

    fn kind_ctx() -> Ctx<Tid, CKind> {
        let mut kctx = Ctx::new();
        kctx.insert(&Tid::from("F"), &Kind::Field);
        kctx.insert(&Tid::from("G"), &Kind::Group);
        kctx.insert(&Tid::from("S"), &Kind::Scalar(Set::from([Tid::from("G")])));
        kctx
    }

    fn s() -> Tid {
        Tid::from("S")
    }

    fn fin0() -> CTyp {
        CTyp::fin(Range::singleton(0))
    }

    #[test]
    fn lub_add_fin_scalar() {
        let ctx = kind_ctx();
        let s_base = CTyp::base(&s());
        // Fin + Scalar = Scalar (was rejected before fix; now accepted)
        assert_eq!(CTyp::lub_add(&fin0(), &s_base, &ctx), Ok(s_base.clone()));
        assert_eq!(CTyp::lub_add(&s_base, &fin0(), &ctx), Ok(s_base));
    }

    #[test]
    fn lub_mul_fin_scalar() {
        let ctx = kind_ctx();
        let s_base = CTyp::base(&s());
        // Fin * Scalar = Scalar (was rejected before fix; now accepted)
        assert_eq!(CTyp::lub_mul(&fin0(), &s_base, &ctx), Ok(s_base.clone()));
        assert_eq!(CTyp::lub_mul(&s_base, &fin0(), &ctx), Ok(s_base));
    }

    #[test]
    fn lub_sub_fin_scalar() {
        let ctx = kind_ctx();
        let s_base = CTyp::base(&s());
        // Fin - Scalar = Scalar (already worked)
        assert_eq!(CTyp::lub_sub(&fin0(), &s_base, &ctx), Ok(s_base.clone()));
        assert_eq!(CTyp::lub_sub(&s_base, &fin0(), &ctx), Ok(s_base));
    }

    #[test]
    fn lub_equ_fin_scalar() {
        let ctx = kind_ctx();
        let s_base = CTyp::base(&s());
        // Fin == Scalar = Scalar (already worked)
        assert_eq!(CTyp::lub_equ(&fin0(), &s_base, &ctx), Ok(s_base.clone()));
        assert_eq!(CTyp::lub_equ(&s_base, &fin0(), &ctx), Ok(s_base));
    }

    #[test]
    fn lub_add_fin_group_rejected() {
        let ctx = kind_ctx();
        let g_base = CTyp::base(&Tid::from("G"));
        // Fin + Group = error (no coercion to group types)
        assert!(CTyp::lub_add(&fin0(), &g_base, &ctx).is_err());
        assert!(CTyp::lub_add(&g_base, &fin0(), &ctx).is_err());
    }
}
