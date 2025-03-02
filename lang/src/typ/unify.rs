use crate::typ::{Nothing, Kind, CTyp, AliasSubsts};
use crate::typ::lub::{Lub, LubError};
use crate::range::Range;
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
    KindMismatch(Tid, Kind, Tid, Kind),
    #[error("UnifyError: Group types {0} ~ {1} cannot be unified as they belong in pairing friendly curve {2}")]
    PairingMismatch(Tid, Tid, Tid),
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
    pub fn kind_mismatch(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::KindMismatch(a.clone(), ka.clone(), b.clone(), kb.clone())
    }
    pub fn pairing_mismatch(a: &Tid, b: &Tid, p: &Tid) -> Self {
        UnifyError::PairingMismatch(a.clone(), b.clone(), p.clone())
    }
    pub fn typ_mismatch(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::TypMismatch(a.clone(), b.clone())
    }
}

/// Instances of this trait can be equated with substitutions
pub trait Unify where Self: Sized {
    type Error;
    fn unify(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, Self::Error>;
}

/// Unify type variables by equating their kinds
impl Unify for Tid {
    type Error = UnifyError;

    /// Can the two kinds be unified into one kind that describes both?
    fn unify(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        let ka = ctx.get(&a)
            .ok_or(UnifyError::kind_not_found(&a))?;

        let kb = ctx.get(&b)
            .ok_or(UnifyError::kind_not_found(&a))?;

        match (ka, kb) {
            // Both kinds are defined
            (Kind::Field, Kind::Field) => Ok(subs.add_equ(&a, &b)),
            (Kind::Scalar(x), Kind::Scalar(y)) => {
                subs.add_equ(x, y);
                Ok(subs.add_equ(&a, &b))
            },
            (Kind::Multiplicative(x), Kind::Multiplicative(y)) => {
                subs.add_equ(x, y);
                Ok(subs.add_equ(&a, &b))
            },
            (Kind::Group, Kind::Group) =>
                if let Some((p, _)) = ctx.find(|_, k| k == &Kind::Pairing(a.clone(), b.clone())) {
                    Err(UnifyError::pairing_mismatch(&a, &b, &p))
                } else {
                    Ok(subs.add_equ(&a, &b))
                }
            (Kind::Pairing(k1, k2), Kind::Pairing(k3, k4)) => {
                subs.add_equ(k1, k3);
                subs.add_equ(k2, k4);
                Ok(subs.add_equ(&a, &b))
            },
            // Ranges in kinds should be concretized already, if not its a bug
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(UnifyError::kind_mismatch(&a, &ka, &b, &kb))
        }
    }
}

impl Unify for CTyp {
    type Error = UnifyError;
    fn unify(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?)),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_equ(a, b, &Nothing).map_err(UnifyError::Lub)?)),
            // Uni<A> == Uni<B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, n.max(m))),
            // Mle<A> == Mle<B>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, n.max(m))),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, n)),
            // Finite fields can act like 0 degree polynomals
            (CTyp::Uni(a, n), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Uni(a, n)) =>
                Ok(CTyp::Uni(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, n)),
            // Finite fields can act like 0 variable MLEs
            (CTyp::Mle(a, n), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Mle(a, n)) =>
                Ok(CTyp::Mle(Tid::unify(a, b, ctx, subs)
                    .map_err(|e| UnifyError::typ(&x, &y, e))?, n)),
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::typ(&x, &y, UnifyError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_mismatch(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_mismatch(&x, &y))
        }
    }
}

#[cfg(test)] use share::Set;
#[test]
fn unify_typ() {
    let f1 = Tid::from("F1");
    let f2 = Tid::from("F2");
    let g1 = Tid::from("G1");
    let g2 = Tid::from("G2");
    let p = Tid::from("P");

    let ctx = Ctx::from([
        (f1.clone(), Kind::Field),
        (f2.clone(), Kind::Field),
        (g1.clone(), Kind::Group),
        (g2.clone(), Kind::Group),
        (p.clone(), Kind::Pairing(g1.clone(), g2.clone()))
    ]);

    let mut subs = AliasSubsts::new();

    let tf1 = CTyp::Base(f1.clone());
    let tf2 = CTyp::Base(f2.clone());
    let tg1 = CTyp::Base(g1.clone());
    let tg2 = CTyp::Base(g2.clone());
    let tp = CTyp::Base(p.clone());

    assert_eq!(CTyp::unify(tf1.clone(), tf2.clone(), &ctx, &mut subs).unwrap(), CTyp::Base(f1.clone()));
    assert_eq!(subs.get(&f1), Some(&Set::from([f1.clone(), f2.clone()])));
    assert_eq!(subs.get(&f2), Some(&Set::from([f1.clone(), f2.clone()])));
}
