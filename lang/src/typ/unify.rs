use crate::ast::range::Range;
use crate::ast::spanned::Spanned;
use crate::id::Tid;
use crate::typ::lub::{Lub, LubError};
use crate::typ::{AliasSubsts, CKind, CTyp, Kind, Nothing};
use share::Ctx;
use thiserror::Error;

/// Failure raised while unifying two concrete types or two type variables.
#[derive(Error, PartialEq, Debug)]
pub enum UnifyError {
    /// Wraps the failure that occurred while unifying the two given types; displays that
    /// failure.
    #[error("{2}")]
    Typ(CTyp, CTyp, Box<UnifyError>),
    /// A least-upper-bound computation on a nested size range failed.
    #[error(transparent)]
    Lub(LubError),
    /// A type variable has no entry in the kind context `kctx`.
    #[error("Unknown type variable `{0}`")]
    KindNotFound(Tid),
    /// Two type variables were equated but their kinds describe different sorts of
    /// arkworks elements.
    #[error("Type {0} ({1}) does not match {2} ({3})")]
    KindMismatch(Tid, CKind, Tid, CKind),
    /// The two type shapes have no common unifier at all.
    #[error("Type {0} does not match {1}")]
    TypMismatch(CTyp, CTyp),
}

impl UnifyError {
    /// Builds a [`UnifyError::KindNotFound`] for a type variable missing from `kctx`.
    pub fn kind_not_found(a: &Tid) -> Self {
        UnifyError::KindNotFound(a.clone())
    }
    /// Wraps `e` with the pair of types whose unification produced it.
    pub fn typ(a: &CTyp, b: &CTyp, e: UnifyError) -> Self {
        UnifyError::Typ(a.clone(), b.clone(), Box::new(e))
    }
    /// Builds a [`UnifyError::KindMismatch`] recording both variables and their kinds.
    pub fn kind_mismatch(a: &Tid, ka: &CKind, b: &Tid, kb: &CKind) -> Self {
        UnifyError::KindMismatch(a.clone(), ka.clone(), b.clone(), kb.clone())
    }
    /// Builds a [`UnifyError::TypMismatch`] for two irreconcilable type shapes.
    pub fn typ_mismatch(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::TypMismatch(a.clone(), b.clone())
    }
}

/// Instances of this trait can be equated with substitutions
pub trait Unify
where
    Self: Sized,
{
    /// Failure reported when the two values have no common unifier.
    type Error;
    /// Unifies `a` and `b` under the kind context `ctx`, recording the type-variable
    /// aliases discovered along the way in `subs`.
    ///
    /// The returned value is the unified type, with size arguments widened where the
    /// two sides differ in degree or variable count.
    ///
    /// # Errors
    /// Returns `Self::Error` when the two values have incompatible kinds or shapes.
    fn unify(
        a: &Self,
        b: &Self,
        ctx: &Ctx<Tid, CKind>,
        subs: &mut AliasSubsts,
    ) -> Result<Self, Self::Error>;
}

/// Unify type variables by equating their kinds
impl Unify for Tid {
    type Error = UnifyError;

    /// Can the two kinds be unified into one kind that describes both?
    fn unify(
        a: &Self,
        b: &Self,
        ctx: &Ctx<Tid, CKind>,
        subs: &mut AliasSubsts,
    ) -> Result<Tid, UnifyError> {
        let ka = ctx.get(a).ok_or(UnifyError::kind_not_found(a))?;

        let kb = ctx.get(b).ok_or(UnifyError::kind_not_found(b))?;

        match (ka, kb) {
            // Both kinds are defined
            (Kind::Field, Kind::Field) => Ok(subs.add_equ(a, b)),
            (Kind::Group, Kind::Group) => Ok(subs.add_equ(a, b)),
            (Kind::Scalar(x), Kind::Scalar(y)) if x.len() == y.len() => {
                x.iter().zip(y.iter()).for_each(|(x, y)| {
                    subs.add_equ(&x.node, &y.node);
                });
                Ok(subs.add_equ(a, b))
            }
            (Kind::Pairing(k1, k2), Kind::Pairing(k3, k4)) => {
                subs.add_equ(&k1.node, &k3.node);
                subs.add_equ(&k2.node, &k4.node);
                Ok(subs.add_equ(a, b))
            }
            // Ranges and SizeVars should be concretized already, if not its a bug
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (Kind::SizeVar, _) | (_, Kind::SizeVar) => unreachable!(),
            (_, _) => Err(UnifyError::kind_mismatch(a, ka, b, kb)),
        }
    }
}

impl Unify for CTyp {
    type Error = UnifyError;
    fn unify(
        x: &Self,
        y: &Self,
        ctx: &Ctx<Tid, CKind>,
        subs: &mut AliasSubsts,
    ) -> Result<Self, UnifyError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::unify(a, b, ctx, subs).map_err(|e| UnifyError::typ(x, y, e))?,
            )),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_equ(a, b, &Nothing).map_err(UnifyError::Lub)?,
            )),
            // Uni<A> == Uni<B>
            (CTyp::Poly(a, na, n), CTyp::Poly(b, nb, m)) if na.node == 1 && nb.node == 1 => {
                let t = Tid::unify(a, b, ctx, subs).map_err(|e| UnifyError::typ(x, y, e))?;
                Ok(CTyp::uni(&t, n.max(m).node))
            }
            // Mle<A> == Mle<B>
            (CTyp::Poly(a, n, d), CTyp::Poly(b, m, de)) if d.node == 1 && de.node == 1 => {
                let t = Tid::unify(a, b, ctx, subs).map_err(|err| UnifyError::typ(x, y, err))?;
                Ok(CTyp::mle(&t, n.max(m).node))
            }
            // Virtual / multivariate polynomials with tracked degree (>1): sizes must agree.
            (CTyp::Poly(a, n, d), CTyp::Poly(b, m, de))
                if n.node > 1 && d.node > 1 && m.node > 1 && de.node > 1 =>
            {
                if n != m || d != de {
                    Err(UnifyError::typ_mismatch(x, y))
                } else {
                    Ok(CTyp::Poly(
                        Tid::unify(a, b, ctx, subs).map_err(|e| UnifyError::typ(x, y, e))?,
                        n.clone(),
                        d.clone(),
                    ))
                }
            }
            // [A; N] == [B; M]
            (CTyp::Vec(a, n), CTyp::Vec(b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::unify(&a.node, &b.node, ctx, subs)
                            .map_err(|e| UnifyError::typ(x, y, e))?,
                        n.node,
                    ))
                } else {
                    Err(UnifyError::typ_mismatch(x, y))
                }
            }
            // Record types: unify each field
            (CTyp::Record(fields_a), CTyp::Record(fields_b)) => {
                let mut unified_fields = share::Ctx::new();
                for (field_name, typ_a) in fields_a.iter() {
                    if let Some(typ_b) = fields_b.get(field_name) {
                        let unified_typ = CTyp::unify(&typ_a.node, &typ_b.node, ctx, subs)
                            .map_err(|e| UnifyError::typ(x, y, e))?;
                        unified_fields.insert(field_name, &Spanned::dummy(unified_typ));
                    } else {
                        return Err(UnifyError::typ_mismatch(x, y));
                    }
                }
                Ok(CTyp::Record(unified_fields))
            }
            // Finite fields can act like 0 degree polynomals
            (CTyp::Poly(a, d, n), b) | (b, CTyp::Poly(a, d, n)) if d.node == 1 => {
                let t = match b {
                    CTyp::Fin(_) => {
                        let ka = ctx.get(a).ok_or(UnifyError::typ_mismatch(x, y))?;
                        if ka.is_scalar() {
                            a.clone()
                        } else {
                            return Err(UnifyError::typ_mismatch(x, y));
                        }
                    }
                    _ => b.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(x, y))?,
                };
                let t2 = Tid::unify(a, &t, ctx, subs).map_err(|e| UnifyError::typ(x, y, e))?;
                Ok(CTyp::uni(&t2, n.node))
            }
            // Finite fields can act like 0 variable MLEs
            (CTyp::Poly(a, n, d), b) | (b, CTyp::Poly(a, n, d)) if d.node == 1 => {
                let t = match b {
                    CTyp::Fin(_) => {
                        let ka = ctx.get(a).ok_or(UnifyError::typ_mismatch(x, y))?;
                        if ka.is_scalar() {
                            a.clone()
                        } else {
                            return Err(UnifyError::typ_mismatch(x, y));
                        }
                    }
                    _ => b.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(x, y))?,
                };
                let t2 = Tid::unify(a, &t, ctx, subs).map_err(|e| UnifyError::typ(x, y, e))?;
                Ok(CTyp::mle(&t2, n.node))
            }
            // Target-driven unification for Base and Fin
            (CTyp::Base(b), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(b)) => {
                let kb = ctx.get(b).ok_or(UnifyError::typ_mismatch(x, y))?;
                if kb.is_scalar() {
                    Ok(CTyp::Base(b.clone()))
                } else {
                    Err(UnifyError::typ_mismatch(x, y))
                }
            }
            // Indices can act like finite fields
            (a, b) => {
                let ta = a.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(x, y))?;
                let tb = b.to_scalar(ctx).ok_or(UnifyError::typ_mismatch(x, y))?;
                Ok(CTyp::Base(
                    Tid::unify(&ta, &tb, ctx, subs).map_err(|e| UnifyError::typ(x, y, e))?,
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::range::CRange;
    use share::Set;

    #[test]
    fn unify_poly_f_2_2_self() {
        let f = Tid::from("F");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let mut subs = AliasSubsts::new();
        let t = CTyp::Poly(f.clone(), Spanned::dummy(2), Spanned::dummy(2));
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
            (
                s1.clone(),
                Kind::Scalar(Set::singleton(Spanned::dummy(f1.clone()))),
            ),
            (
                p.clone(),
                Kind::Pairing(Spanned::dummy(g1.clone()), Spanned::dummy(g2.clone())),
            ),
            (
                pp.clone(),
                Kind::Pairing(Spanned::dummy(g1.clone()), Spanned::dummy(g1.clone())),
            ),
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
        subs.clear(); // different fields, unify them

        assert_eq!(
            CTyp::unify(&CTyp::vec(&tf1, 10), &CTyp::vec(&tf1, 10), &ctx, &mut subs),
            Ok(CTyp::vec(&tf1, 10))
        );
        assert!(subs.is_empty()); // same field M ~ F and group G1 ~ G2 no substitution needed

        // Different sizes and base fields do not unify
        assert!(CTyp::unify(&CTyp::vec(&tf1, 10), &CTyp::vec(&tf1, 11), &ctx, &mut subs).is_err());
        assert!(CTyp::unify(&CTyp::vec(&tf1, 10), &CTyp::vec(&tg1, 10), &ctx, &mut subs).is_err());
        assert!(subs.is_empty());

        // Univariate polynomial unification
        assert_eq!(
            CTyp::unify(&CTyp::uni(&f1, 10), &CTyp::uni(&f2, 11), &ctx, &mut subs),
            Ok(CTyp::uni(&f1, 11))
        );
        assert_eq!(subs.get(&f1), Some(&Set::from([f1.clone(), f2.clone()])));
        assert_eq!(subs.get(&f2), Some(&Set::from([f1.clone(), f2.clone()])));
        subs.clear();

        // Multivariate polynomial unification
        assert_eq!(
            CTyp::unify(&CTyp::mle(&s1, 10), &CTyp::mle(&s1, 11), &ctx, &mut subs),
            Ok(CTyp::mle(&s1, 11))
        );
        assert!(subs.is_empty()); // same field M ~ F no substitution needed

        // Fin type unification
        let r02 = Range {
            start: Spanned::dummy(0),
            step: None,
            end: Some(Spanned::dummy(2)),
        };
        let r110 = Range {
            start: Spanned::dummy(1),
            step: None,
            end: Some(Spanned::dummy(10)),
        };
        assert_eq!(
            CTyp::unify(&CTyp::fin(r02), &CTyp::fin(r110), &ctx, &mut subs),
            Ok(CTyp::fin(CRange::from_raw(0, 1, 10)))
        );
        assert!(subs.is_empty()); // no substitution needed

        // Bad pairing
        assert_eq!(
            CTyp::unify(&tp, &tp2, &ctx, &mut subs),
            Ok(CTyp::Base(Tid::from("P")))
        );
        assert_eq!(subs.get(&g1), Some(&Set::from([g1.clone(), g2.clone()])));
        assert_eq!(subs.get(&g2), Some(&Set::from([g1.clone(), g2.clone()])));
    }
}
