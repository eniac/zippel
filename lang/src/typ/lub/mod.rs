mod error;
#[cfg(test)]
mod tests;

pub use error::LubError;

use crate::ast::BinOp;
use crate::id::Tid;
use crate::typ::range::Range;
use crate::typ::{CKind, CTyp, CTypeVar, Kind, Nothing};
use share::Ctx;

/// Instances of this trait can be added, multiplied, divided, exp'd and dot product'd together, generating constraints and type errors
pub trait Lub
where
    Self: Sized,
{
    type Context;
    fn lub_equ(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_add(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_sub(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_mul(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_div(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_pow(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_dot(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_pair(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_rem(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_and(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_concat(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;

    fn lub_op(op: BinOp, a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match op {
            BinOp::Equ => Self::lub_equ(a, b, ctx),
            BinOp::Add => Self::lub_add(a, b, ctx),
            BinOp::Sub => Self::lub_sub(a, b, ctx),
            BinOp::Mul => Self::lub_mul(a, b, ctx),
            BinOp::Div => Self::lub_div(a, b, ctx),
            BinOp::Pow => Self::lub_pow(a, b, ctx),
            BinOp::Rem => Self::lub_rem(a, b, ctx),
            BinOp::Dot => Self::lub_dot(a, b, ctx),
            BinOp::And => Self::lub_and(a, b, ctx),
            BinOp::Concat => Self::lub_concat(a, b, ctx),
        }
    }
}

/// Least-upper bounds for [Range] overapproximate sets of integers
impl Lub for Range<usize> {
    type Context = Nothing;
    fn lub_equ(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::equ(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::equ(&a, &b), LubError::bad_range(b, e)))?;

        // Find the minimum of the starts and maximum of the ends
        let new_start = std::cmp::min(a.start, b.start);
        let new_end = std::cmp::max(a.end, b.end);
        let new_step = num::integer::gcd(a.step, b.step);

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn lub_add(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(b, e)))?;

        Ok(*a + *b)
    }

    fn lub_sub(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::sub(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::sub(&a, &b), LubError::bad_range(b, e)))?;

        Ok(*a - *b)
    }

    fn lub_mul(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::mul(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::mul(&a, &b), LubError::bad_range(b, e)))?;

        Ok(*a * *b)
    }

    fn lub_div(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check()
            .map_err(|e| LubError::next(LubError::div(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::div(&a, &b), LubError::bad_range(b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::div(&a, &b)); // Division by zero is undefined
        }

        Ok(*a / *b)
    }

    fn lub_pow(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check()
            .map_err(|e| LubError::next(LubError::pow(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::pow(&a, &b), LubError::bad_range(b, e)))?;

        Ok(*a ^ *b)
    }

    fn lub_rem(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check()
            .map_err(|e| LubError::next(LubError::rem(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::rem(&a, &b), LubError::bad_range(b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::rem(&a, &b)); // Division by zero is undefined
        }

        Ok(*a % *b)
    }

    fn lub_dot(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        Self::lub_mul(a, b, &Nothing).map_err(|e| LubError::next(LubError::dot(&a, &b), e))
    }

    fn lub_concat(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::concat(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::concat(&a, &b), LubError::bad_range(b, e)))?;

        if let Some(c) = a.concat(b) {
            Ok(c)
        } else {
            Err(LubError::concat(&a, &b))
        }
    }
    fn lub_and(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(b, e)))?;

        Err(LubError::and(&a, &b))
    }
    fn lub_pair(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        Err(LubError::pair(&a, &b))
    }
}

/// Least-upper bound of type variables
impl Lub for Tid {
    type Context = Ctx<Tid, CKind>;
    /// Can the two kinds be unified into one kind that describes both?
    fn lub_equ(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Group, Kind::Group) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => {
                Ok(a.clone())
            }
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::equ(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb))),
        }
    }

    /// Least-upper-bound for addition of different kinds
    fn lub_add(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Group, Kind::Group) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => {
                Ok(a.clone())
            }
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::add(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb))),
        }
    }

    /// Least-upper-bound for subtraction same as addition
    fn lub_sub(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Group, Kind::Group) if a == b => Ok(a.clone()),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => {
                Ok(a.clone())
            }
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::sub(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb))),
        }
    }

    /// Least-upper-bound for multiplication of different kinds
    fn lub_mul(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            // Scalar multiplication: Scalar * Group = Group * Scalar = Group
            (Kind::Scalar(g), Kind::Group) if g.contains(b) => Ok(b.clone()),
            (Kind::Group, Kind::Scalar(g)) if g.contains(a) => Ok(a.clone()),
            // Scalar multiplication: Scalar * Pairing Target = Pairing Target * Scalar = Pairing Target
            // The scalar F ranges over G1, G2, so we ensure g contains g1 or g2
            (Kind::Pairing(g1, g2), Kind::Scalar(g)) if g.contains(g1) || g.contains(g2) => {
                Ok(a.clone())
            }
            (Kind::Scalar(g), Kind::Pairing(g1, g2)) if g.contains(g1) || g.contains(g2) => {
                Ok(b.clone())
            }
            // Bilinear pairing: G1 * G2 => Pairing(G1, G2) and G2 * G1 => Pairing(G2, G1)
            (Kind::Group, Kind::Group) => {
                if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(a, b)) {
                    Ok(pid.clone())
                } else {
                    Err(LubError::mul(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)))
                }
            }
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::mul(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb))),
        }
    }

    fn lub_pair(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        match (ka, kb) {
            // Group multiplication is only allowed for pairing friendly curves
            // G1 * G2 => Pairing(G1, G2)
            // forces G1: Group, G2: Group
            (Kind::Group, Kind::Group) => {
                if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(a, b)) {
                    Ok(pid.clone())
                } else {
                    Err(LubError::pair(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)))
                }
            }
            (_, _) => Err(LubError::pair(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb))),
        }
    }

    /// Least-upper-bound for division of different kinds
    fn lub_div(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Group, Kind::Scalar(g)) if g.contains(a) => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::div(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb))),
        }
    }

    /// Least-upper-bound for remainder of different kinds
    fn lub_rem(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;
        Err(LubError::rem(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)))
    }

    /// Least-upper-bound for exponentiation of different kinds
    fn lub_pow(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;
        Err(LubError::pow(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)))
    }

    /// Least-upper-bound for dot product is multiplication (for kinds) with one
    /// extra: `dot(VecG1, VecG2) -> GT` is allowed and resolves the same way as
    /// `pair(G1, G2)` does. The runtime arm in `value_dot` routes this to
    /// `multi_pairing`, which is how every native SNARK verifier batches its
    /// pairing check (one final exponentiation across all summands).
    fn lub_dot(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        if let (Kind::Group, Kind::Group) = (ka, kb) {
            if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(a, b)) {
                return Ok(pid.clone());
            }
        }

        Self::lub_mul(a, b, ctx).map_err(|e| {
            LubError::next(
                LubError::dot(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)),
                e,
            )
        })
    }

    /// Least-upper-bound for Concatenation is always an error
    fn lub_concat(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        Err(LubError::concat(
            &CTypeVar::new(a, ka),
            &CTypeVar::new(b, kb),
        ))
    }

    fn lub_and(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(b))?;

        Err(LubError::and(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)))
    }
}

impl Lub for CTyp {
    type Context = Ctx<Tid, CKind>;
    fn lub_equ(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Bool, CTyp::Bool) => Ok(CTyp::Bool),
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_equ(a, b, ctx).map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
            )),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_equ(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
            )),
            // Poly<A, na, ma> == Poly<B, nb, mb>: coerce to wider type
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) => Ok(CTyp::Poly(
                Tid::lub_equ(a, b, ctx).map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
                *na.max(nb),
                *ma.max(mb),
            )),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m => Ok(CTyp::vec(
                &CTyp::lub_equ(a, b, ctx).map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
                *n,
            )),
            // Record types: width-subtyping. LUB is the intersection of common fields,
            // each common field's type lub'd; fields present on only one side are dropped.
            (CTyp::Record(fields_a), CTyp::Record(fields_b)) => {
                let mut result_fields = share::Ctx::new();
                for (name, typ_a) in fields_a.iter() {
                    if let Some(typ_b) = fields_b.get(name) {
                        let lub_typ = CTyp::lub_equ(typ_a, typ_b, ctx)
                            .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?;
                        result_fields.insert(name, &lub_typ);
                    }
                }
                Ok(CTyp::Record(result_fields))
            }
            // Target-driven equality for Base and Fin
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(a).ok_or(LubError::equ(&x, &y))?;
                if ka.is_scalar() {
                    Ok(CTyp::Base(a.clone()))
                } else {
                    Err(LubError::equ(&x, &y))
                }
            }
            // Indices can act like finite fields
            (a, b) => {
                let ta = a.to_scalar(ctx).ok_or(LubError::equ(&x, &y))?;
                let tb = b.to_scalar(ctx).ok_or(LubError::equ(&x, &y))?;
                Ok(CTyp::Base(
                    Tid::lub_equ(&ta, &tb, ctx)
                        .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
                ))
            }
        }
    }

    fn lub_add(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_add(a, b, ctx).map_err(|e| LubError::next(LubError::add(&x, &y), e))?,
            )),
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_add(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?,
            )),
            // Uni<A> + Uni<B> = Uni<max(A, B)>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) => Ok(CTyp::Poly(
                Tid::lub_add(a, b, ctx).map_err(|e| LubError::next(LubError::add(&x, &y), e))?,
                1,
                *n.max(m),
            )),
            // Mle<A> + Mle<B> = Mle<max(A, B)>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) => Ok(CTyp::Poly(
                Tid::lub_add(a, b, ctx).map_err(|e| LubError::next(LubError::add(&x, &y), e))?,
                *n.max(m),
                1,
            )),
            // General Poly + Poly: vars and degree both take max.
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) => Ok(CTyp::Poly(
                Tid::lub_add(a, b, ctx).map_err(|e| LubError::next(LubError::add(&x, &y), e))?,
                *na.max(nb),
                *ma.max(mb),
            )),
            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_add(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::add(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::add(&x, &y))
                }
            }
            // Phase B: polynomial ↔ Vec is now a type error. Vec must be
            // explicitly converted via `poly([...])` / `coef(...)` at the
            // source level before mixing with a polynomial. The (Poly, Vec)
            // and (Vec, Poly) arms previously here implicitly reinterpreted
            // a Vec as a coefficient list — semantically opaque, removed.
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(a).ok_or(LubError::next(
                    LubError::add(&x, &y),
                    LubError::kind_not_found(a),
                ))?;
                if ka == &Kind::Field {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::add(&x, &y))
                }
            }
            // Finite fields can act like univariate polynomials
            (CTyp::Base(a), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Base(a)) => {
                let t = Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                Ok(CTyp::Poly(t, 1, *n))
            }
            // Indices can act like univariate polynomials
            (CTyp::Fin(_), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Fin(_)) => {
                Ok(CTyp::uni(b, *n))
            }
            (CTyp::Poly(a, n, 1), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Poly(a, n, 1)) => {
                let t = Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                Ok(CTyp::Poly(t, *n, 1))
            }
            (CTyp::Poly(a, n, 1), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Poly(a, n, 1)) => {
                Ok(CTyp::Poly(a.clone(), *n, 1))
            }
            (_, _) => Err(LubError::add(&x, &y)),
        }
    }

    fn lub_sub(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_sub(a, b, ctx).map_err(|e| LubError::next(LubError::sub(&x, &y), e))?,
            )),
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_sub(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?,
            )),
            // Uni<A> - Uni<B> = Uni<max(A, B)>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) => Ok(CTyp::Poly(
                Tid::lub_sub(a, b, ctx).map_err(|e| LubError::next(LubError::sub(&x, &y), e))?,
                1,
                *n.max(m),
            )),
            // Mle<A> - Mle<B> = Mle<max(A, B)>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) => Ok(CTyp::Poly(
                Tid::lub_sub(a, b, ctx).map_err(|e| LubError::next(LubError::sub(&x, &y), e))?,
                *n.max(m),
                1,
            )),
            // General Poly - Poly: vars and degree both take max.
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) => Ok(CTyp::Poly(
                Tid::lub_sub(a, b, ctx).map_err(|e| LubError::next(LubError::sub(&x, &y), e))?,
                *na.max(nb),
                *ma.max(mb),
            )),
            // Vec<A> - Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_sub(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::sub(&x, &y))
                }
            }
            // Phase B: polynomial ↔ Vec is now a type error (see lub_add).
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(a).ok_or(LubError::next(
                    LubError::sub(&x, &y),
                    LubError::kind_not_found(a),
                ))?;
                if ka.is_scalar() {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::sub(&x, &y))
                }
            }
            // Finite fields can act like univariate polynomials
            (CTyp::Base(a), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Base(a)) => {
                let t = Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                Ok(CTyp::Poly(t, 1, *n))
            }
            // Indices can act like univariate polynomials
            (CTyp::Fin(_), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Fin(_)) => {
                Ok(CTyp::uni(b, *n))
            }
            (CTyp::Poly(a, n, 1), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Poly(a, n, 1)) => {
                let t = Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                Ok(CTyp::Poly(t, *n, 1))
            }
            (CTyp::Poly(a, n, 1), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Poly(a, n, 1)) => {
                Ok(CTyp::Poly(a.clone(), *n, 1))
            }
            (_, _) => Err(LubError::sub(&x, &y)),
        }
    }

    fn lub_mul(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_mul(a, b, ctx).map_err(|e| LubError::next(LubError::mul(&x, &y), e))?,
            )),
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_mul(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?,
            )),
            // General rule: Poly(F, n, m) * Poly(F, n', m') = Poly(F, max(n,n'), m+m')
            // (N is the max total degree per Typ::Poly docs; degrees add under multiplication)
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) => {
                let num_vars = *na.max(nb);
                let degree = ma.saturating_add(*mb);
                Ok(CTyp::Poly(
                    Tid::lub_mul(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?,
                    num_vars,
                    degree,
                ))
            }
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_mul(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::mul(&x, &y))
                }
            }
            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) => Ok(CTyp::vec(
                &CTyp::lub_mul(a, b, ctx).map_err(|e| LubError::next(LubError::mul(&x, &y), e))?,
                *n,
            )),
            // Uni<A> * c = Uni<A> if c is a finite field
            (a, CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), a) => {
                let t = CTyp::lub_mul(a, &CTyp::base(b), ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Poly(c, 1, *n))
                } else {
                    Err(LubError::mul(&x, &y))
                }
            }
            // Mle<A> * c = Mle<A> if c is a finite field
            (a, CTyp::Poly(b, n, 1)) | (CTyp::Poly(b, n, 1), a) => {
                let t = CTyp::lub_mul(a, &CTyp::base(b), ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Poly(c, *n, 1))
                } else {
                    Err(LubError::mul(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(a).ok_or(LubError::next(
                    LubError::mul(&x, &y),
                    LubError::kind_not_found(a),
                ))?;
                if ka == &Kind::Field {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::mul(&x, &y))
                }
            }
            (_, _) => Err(LubError::mul(&x, &y)),
        }
    }

    fn lub_pair(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_pair(a, b, ctx).map_err(|e| LubError::next(LubError::pair(&x, &y), e))?,
            )),
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_pair(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::pair(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::pair(&x, &y))
                }
            }
            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) => Ok(CTyp::vec(
                &CTyp::lub_pair(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::pair(&x, &y), e))?,
                *n,
            )),
            (_, _) => Err(LubError::pair(&x, &y)),
        }
    }

    fn lub_div(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_div(a, b, ctx).map_err(|e| LubError::next(LubError::div(&x, &y), e))?,
            )),
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_div(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?,
            )),
            // General rule: Poly(F, n, m) / Poly(F, n', m') = Poly(F, max(n,n'), m-m') if m >= m'
            // (N is the max total degree; polynomial quotient degree is m - m'.)
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) if ma >= mb => {
                let num_vars = *na.max(nb);
                let degree = *ma - *mb;
                Ok(CTyp::Poly(
                    Tid::lub_div(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::div(&x, &y), e))?,
                    num_vars,
                    degree,
                ))
            }
            // Vec<A> / Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_div(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::div(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::div(&x, &y))
                }
            }
            // Vec<A> / c or c / Vec<A> = Vec<lub_div(A, c)>
            (CTyp::Vec(box a, n), b) | (b, CTyp::Vec(box a, n)) => Ok(CTyp::vec(
                &CTyp::lub_div(a, b, ctx).map_err(|e| LubError::next(LubError::div(&x, &y), e))?,
                *n,
            )),

            // Poly(F, n, m) / c = Poly(F, n, m) if c is a finite field (scalar division)
            (CTyp::Poly(b, n, m), a) => {
                let t = CTyp::lub_div(&CTyp::base(b), a, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Poly(c, *n, *m))
                } else {
                    Err(LubError::div(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => Ok(CTyp::base(a)),
            (_, _) => Err(LubError::div(&x, &y)),
        }
    }

    fn lub_rem(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => Ok(CTyp::Base(
                Tid::lub_rem(a, b, ctx).map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
            )),
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_rem(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
            )),
            // General Poly<F,n1,m1> % Poly<F,n2,m2> = Poly<F, max(n1,n2), m2 - 1> if m2 >= 1.
            // (Per poly-encoding spec: remainder has degree strictly less than divisor.)
            (CTyp::Poly(a, na, _ma), CTyp::Poly(b, nb, mb)) if *mb >= 1 => {
                let num_vars = *na.max(nb);
                Ok(CTyp::Poly(
                    Tid::lub_equ(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
                    num_vars,
                    *mb - 1,
                ))
            }
            // Vec<A> % Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_rem(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::rem(&x, &y))
                }
            }
            // Vec<B> % A or A % Vec<B> = Vec<lub_rem(A, B)>
            (CTyp::Vec(box b, n), a) | (a, CTyp::Vec(box b, n)) => Ok(CTyp::vec(
                &CTyp::lub_rem(a, b, ctx).map_err(|e| LubError::next(LubError::rem(&x, &y), e))?,
                *n,
            )),

            (_, _) => Err(LubError::rem(&x, &y)),
        }
    }

    fn lub_pow(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Fin(a), CTyp::Fin(b)) => Ok(CTyp::Fin(
                Range::lub_pow(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?,
            )),
            (CTyp::Base(a), CTyp::Fin(_)) => {
                let ka = ctx.get(a).ok_or(LubError::next(
                    LubError::pow(&x, &y),
                    LubError::kind_not_found(a),
                ))?;
                if ka.is_scalar() {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::pow(&x, &y))
                }
            }
            // Vec<A> ^ Vec<B> = Vec<C>
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::vec(
                        &CTyp::lub_pow(a, b, ctx)
                            .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?,
                        *n,
                    ))
                } else {
                    Err(LubError::pow(&x, &y))
                }
            }
            // Vec<B> ^ A or A ^ Vec<B> = Vec<lub_pow(B, A)>
            (CTyp::Vec(box a, n), b) | (b, CTyp::Vec(box a, n)) => Ok(CTyp::vec(
                &CTyp::lub_pow(a, b, ctx).map_err(|e| LubError::next(LubError::pow(&x, &y), e))?,
                *n,
            )),

            // Uni<B> ^ Fin<i..j> = Uni<B*j>
            (CTyp::Poly(a, 1, n), CTyp::Fin(r)) => {
                Ok(CTyp::uni(a, n.saturating_mul(r.end.saturating_sub(1))))
            }

            (_, _) => Err(LubError::pow(&x, &y)),
        }
    }

    fn lub_dot(x: &Self, y: &Self, ctx: &Self::Context) -> Result<Self, LubError> {
        match (x, y) {
            // Vec<A> . Vec<B> = C where C is the element-wise result of
            // multiplication or pairing, determined by lub_mul.
            // dot(VecG1, VecG2) -> GT works because lub_mul(G1, G2)
            // resolves the pairing kind rule, and dot(VecG1, VecScalar) -> G1
            // works because lub_mul(G1, Scalar) = G1 (scalar multiplication).
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    Ok(CTyp::lub_mul(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?)
                } else {
                    Err(LubError::dot(&x, &y))
                }
            }
            // Phase B: Vec . Uni is now a type error (Vec is no longer
            // implicitly reinterpreted as a coefficient list). Use
            // `coef(poly)` to extract coefficients before dot-product.
            (_, _) => Err(LubError::dot(&x, &y)),
        }
    }

    fn lub_concat(ta: &Self, tb: &Self, kctx: &Self::Context) -> Result<Self, LubError> {
        match (ta, tb) {
            // Vec<A> ++ Vec<B> = Vec<C> if A = B = C
            (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                // Try to concatenate them first
                if let Ok(t) = CTyp::lub_equ(a, b, kctx) {
                    Ok(CTyp::vec(&t, x.saturating_add(*y)))
                } else if let Ok(t) = CTyp::lub_equ(a, tb, kctx) {
                    // Treating tb as an element of ta (appending)
                    Ok(CTyp::vec(&t, x.saturating_add(1)))
                } else if let Ok(t) = CTyp::lub_equ(b, ta, kctx) {
                    // Treating ta as an element of tb (prepending)
                    Ok(CTyp::vec(&t, y.saturating_add(1)))
                } else {
                    Err(LubError::concat(ta, tb))
                }
            }
            // Phase B: polynomial ++ Vec is now a type error. Use
            // `coef(poly)` to extract a coefficient vector first, then
            // concatenate as Vec ++ Vec.
            // Vec<A, n> ++ B = Vec<C, n+1> if A = B = C
            (CTyp::Vec(box a, n), b) | (b, CTyp::Vec(box a, n)) => {
                // Type [a] and [b] should be the same ([t])
                let t = CTyp::lub_equ(a, b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                // Add an element to the vector
                Ok(CTyp::vec(&t, n.saturating_add(1)))
            }

            (ta, tb) => Err(LubError::concat(&ta, &tb)),
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn lub_and(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Bool, CTyp::Bool) => Ok(CTyp::Bool),
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m => {
                let t = CTyp::lub_and(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?;
                Ok(CTyp::vec(&t, *n))
            }
            (_, _) => Err(LubError::and(&x, &y)),
        }
    }
}
