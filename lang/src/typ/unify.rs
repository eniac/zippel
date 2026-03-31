use crate::typ::{Nothing, Kind, CKind, CTyp, AliasSubsts};
use crate::typ::lub::{Lub, LubError};
use crate::typ::range::Range;
use crate::id::Tid;
use share::Ctx;
use thiserror::Error;

#[derive(Error, PartialEq, Debug)]
pub enum UnifyError {
    #[error("UnifyError: While unifying types {0} ~ {1}\n\n{2}")]
    Typ(CTyp, CTyp, Box<UnifyError>),
    #[error(transparent)]
    Lub(LubError),
    #[error("UnifyError: Kind not found {0}")]
    KindNotFound(Tid),
    #[error("UnifyError: Type variable {0}: {1} does not match {2}: {3}")]
    KindMismatch(Tid, CKind, Tid, CKind),
    #[error("UnifyError: Type mismatch {0} ~ {1}")]
    TypMismatch(CTyp, CTyp),
}

impl UnifyError {
    pub fn kind_not_found(a: &Tid) -> Self {
        UnifyError::KindNotFound(a.clone())
    }
    pub fn typ(a: &CTyp, b: &CTyp, e: UnifyError) -> Self {
        UnifyError::Typ(a.clone(), b.clone(), Box::new(e))
    }
    pub fn kind_mismatch(a: &Tid, ka: &CKind, b: &Tid, kb: &CKind) -> Self {
        UnifyError::KindMismatch(a.clone(), ka.clone(), b.clone(), kb.clone())
    }
    pub fn typ_mismatch(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::TypMismatch(a.clone(), b.clone())
    }
}

/// Instances of this trait can be equated with substitutions
pub trait Unify where Self: Sized {
    type Error;
    fn unify(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>, subs: &mut AliasSubsts) -> Result<Self, Self::Error>;
}

/// Unify type variables by equating their kinds
impl Unify for Tid {
    type Error = UnifyError;

    /// Can the two kinds be unified into one kind that describes both?
    fn unify(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        let ka = ctx.get(&a)
            .ok_or(UnifyError::kind_not_found(&a))?;

        let kb = ctx.get(&b)
            .ok_or(UnifyError::kind_not_found(&a))?;

        match (ka, kb) {
            // Both kinds are defined
            (Kind::Field, Kind::Field) => Ok(subs.add_equ(&a, &b)),
            (Kind::Group, Kind::Group) => Ok(subs.add_equ(&a, &b)),
            (Kind::Scalar(x), Kind::Scalar(y)) if x.len() == y.len() => {
                x.iter().zip(y.iter()).for_each(|(x, y)| {
                    subs.add_equ(x, y);
                });
                Ok(subs.add_equ(&a, &b))
            },
            (Kind::Pairing(k1, k2), Kind::Pairing(k3, k4)) => {
                subs.add_equ(k1, k3);
                subs.add_equ(k2, k4);
                Ok(subs.add_equ(&a, &b))
            },
            // Ranges and SizeVars should be concretized already, if not its a bug
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (Kind::SizeVar, _) | (_, Kind::SizeVar) => unreachable!(),
            (_, _) => Err(UnifyError::kind_mismatch(&a, &ka, &b, &kb))
        }
    }
}

impl Unify for CTyp {
    type Error = UnifyError;
    fn unify(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?)),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_equ(a, b, &Nothing).map_err(UnifyError::Lub)?)),
            // Uni<A> == Uni<B>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) =>
                Ok(CTyp::Poly(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, 1, *n.max(m))),
            // Mle<A> == Mle<B>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, *n.max(m), 1)),
            // Virtual / multivariate polynomials with tracked degree (>1): sizes must agree.
            (CTyp::Poly(a, n, d), CTyp::Poly(b, m, e)) if *n > 1 && *d > 1 && *m > 1 && *e > 1 => {
                if n != m || d != e {
                    Err(UnifyError::typ_mismatch(&x, &y))
                } else {
                    Ok(CTyp::Poly(
                        Tid::unify(a, b, ctx, subs).map_err(|e| UnifyError::typ(&x, &y, e))?,
                        *n,
                        *d,
                    ))
                }
            },
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(&CTyp::unify(a, b, ctx, subs)
                        .map_err(|e| UnifyError::typ(&x, &y, e))?, *n))
                } else {
                    Err(UnifyError::typ_mismatch(&x, &y))
                },
            // Record types: unify each field
            (CTyp::Record(fields_a), CTyp::Record(fields_b)) => {
                let mut unified_fields = share::Ctx::new();
                for (field_name, typ_a) in fields_a.iter() {
                    if let Some(typ_b) = fields_b.get(field_name) {
                        let unified_typ = CTyp::unify(typ_a, typ_b, ctx, subs)
                            .map_err(|e| UnifyError::typ(&x, &y, e))?;
                        unified_fields.insert(field_name, &unified_typ);
                    } else {
                        return Err(UnifyError::typ_mismatch(&x, &y));
                    }
                }
                Ok(CTyp::Record(unified_fields))
            },
            // Finite fields can act like 0 degree polynomals
            (CTyp::Poly(a, 1, n), b) | (b, CTyp::Poly(a, 1, n)) => {
                let t = b.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(&x, &y))?;
                Ok(CTyp::Poly(Tid::unify(a, &t, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, 1, *n))
            },
            // Finite fields can act like 0 variable MLEs
            (CTyp::Poly(a, n, 1), b) | (b, CTyp::Poly(a, n, 1)) => {
                let t = b.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(&x, &y))?;
                Ok(CTyp::Poly(Tid::unify(a, &t, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, *n, 1))
            },
            // Indices can act like finite fields
            (a, b) => {
                let ta = a.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(&x, &y))?;
                let tb = b.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(&x, &y))?;
                Ok(CTyp::Base(Tid::unify(&ta, &tb, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?))
            }
        }
    }
}

#[cfg(test)] use share::Set;
#[test]
fn unify_poly_f_2_2_self() {
    let f = Tid::from("F");
    let ctx = Ctx::from([(f.clone(), Kind::Field)]);
    let mut subs = AliasSubsts::new();
    let t = CTyp::Poly(f.clone(), 2, 2);
    assert_eq!(CTyp::unify(&t, &t, &ctx, &mut subs), Ok(t));
}
#[test]
fn unify_typ() {
    let f1 = Tid::from("F1");
    let f2 = Tid::from("F2");
    let g1 = Tid::from("G1");
    let g2 = Tid::from("G2");
    let s1 = Tid::from("S1");
    let p = Tid::from("P");
    let pp = Tid::from("P2");

    let ctx = Ctx::from([
        (f1.clone(), Kind::Field),
        (f2.clone(), Kind::Field),
        (g1.clone(), Kind::Group),
        (g2.clone(), Kind::Group),
        (s1.clone(), Kind::Scalar(Set::singleton(f1.clone()))),
        (p.clone(), Kind::Pairing(g1.clone(), g2.clone())),
        (pp.clone(), Kind::Pairing(g1.clone(), g1.clone())),
    ]);

    let mut subs = AliasSubsts::new();

    let tf1 = CTyp::Base(f1.clone());
    let tf2 = CTyp::Base(f2.clone());
    let tg1 = CTyp::Base(g1.clone());
    let ts1 = CTyp::Base(s1.clone());
    let tp = CTyp::Base(p.clone());
    let tp2 = CTyp::Base(pp.clone());

    // Unify base types
    assert_eq!(CTyp::unify(&tg1, &tg1, &ctx, &mut subs), Ok(tg1.clone()));
    assert_eq!(CTyp::unify(&ts1, &ts1, &ctx, &mut subs), Ok(ts1.clone()));
    assert!(subs.is_empty()); // same field M ~ F and group G1 ~ G2 no substitution needed

    assert_eq!(CTyp::unify(&tf1, &tf2, &ctx, &mut subs), Ok(tf1.clone()));
    assert_eq!(subs.get(&f1), Some(&Set::from([f1.clone(), f2.clone()])));
    assert_eq!(subs.get(&f2), Some(&Set::from([f1.clone(), f2.clone()])));
    subs.clear();            // different fields, unify them

    assert_eq!(CTyp::unify(&CTyp::vec(&tf1, 10), &CTyp::vec(&tf1, 10), &ctx, &mut subs), Ok(CTyp::vec(&tf1, 10)));
    assert!(subs.is_empty()); // same field M ~ F and group G1 ~ G2 no substitution needed

    // Different sizes and base fields do not unify
    assert!(CTyp::unify(&CTyp::vec(&tf1, 10), &CTyp::vec(&tf1, 11), &ctx, &mut subs).is_err());
    assert!(CTyp::unify(&CTyp::vec(&tf1, 10), &CTyp::vec(&tg1, 10), &ctx, &mut subs).is_err());
    assert!(subs.is_empty());

    // Univariate polynomial unification
    assert_eq!(CTyp::unify(&CTyp::uni(&f1, 10), &CTyp::uni(&f2, 11), &ctx, &mut subs), Ok(CTyp::uni(&f1, 11)));
    assert_eq!(subs.get(&f1), Some(&Set::from([f1.clone(), f2.clone()])));
    assert_eq!(subs.get(&f2), Some(&Set::from([f1.clone(), f2.clone()])));
    subs.clear();

    // Multivariate polynomial unification
    assert_eq!(CTyp::unify(&CTyp::mle(&s1, 10), &CTyp::mle(&s1, 11), &ctx, &mut subs), Ok(CTyp::mle(&s1, 11)));
    assert!(subs.is_empty()); // same field M ~ F no substitution needed

    // Fin type unification
    assert_eq!(CTyp::unify(&CTyp::fin(Range::new(0, 2)), &CTyp::fin(Range::new(1, 10)), &ctx, &mut subs), Ok(CTyp::fin(Range::new(0, 10))));
    assert!(subs.is_empty()); // no substitution needed

    // Bad pairing
    assert_eq!(CTyp::unify(&tp, &tp2, &ctx, &mut subs),
        Ok(CTyp::Base(Tid::from("P"))));
    assert_eq!(subs.get(&g1), Some(&Set::from([g1.clone(), g2.clone()])));
    assert_eq!(subs.get(&g2), Some(&Set::from([g1.clone(), g2.clone()])));
}
