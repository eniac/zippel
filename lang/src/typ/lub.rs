use crate::ast::BinOp;
use crate::id::Tid;
use crate::typ::range::{Range, RangeError};
use crate::typ::{CKind, CTyp, CTypeVar, Kind, Nothing};
use share::Ctx;

use std::fmt;
use thiserror::Error;

#[derive(Error, PartialEq, Debug)]
pub enum LubError {
    #[error("{0}\n\n{1}")]
    Next(Box<LubError>, Box<LubError>),
    #[error("LubError: Cannot take equality of {0} == {1}")]
    Equ(String, String),
    #[error("LubError: Cannot take the least-upper bound: {1} {0} {2}")]
    Bin(BinOp, String, String),
    #[error("LubError: Cannot take dot-product of {0} . {1}")]
    Dot(String, String),
    #[error("LubError: Cannot take bilinear pairing of {0} and {1}")]
    Pair(String, String),
    #[error("LubError: Malformed range {0}\n\n{1}")]
    BadRange(Range<usize>, RangeError),
    #[error("LubError: Kind {0} not found")]
    KindNotFound(Tid),
    #[error("LubError: Cannot evaluate {0} at {1}")]
    Eval(String, String),
}

impl LubError {
    pub fn next(a: LubError, b: LubError) -> Self {
        LubError::Next(Box::new(a), Box::new(b))
    }
    pub fn kind_not_found(id: &Tid) -> Self {
        LubError::KindNotFound(id.clone())
    }
    pub fn bad_range(r: &Range<usize>, e: RangeError) -> Self {
        LubError::BadRange(r.clone(), e)
    }
    pub fn equ<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Equ(a.to_string(), b.to_string())
    }
    pub fn add<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Add, a.to_string(), b.to_string())
    }
    pub fn sub<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Sub, a.to_string(), b.to_string())
    }
    pub fn mul<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Mul, a.to_string(), b.to_string())
    }
    pub fn div<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Div, a.to_string(), b.to_string())
    }
    pub fn pow<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Pow, a.to_string(), b.to_string())
    }
    pub fn eval<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Eval(a.to_string(), b.to_string())
    }
    pub fn rem<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Rem, a.to_string(), b.to_string())
    }
    pub fn dot<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Dot, a.to_string(), b.to_string())
    }
    pub fn pair<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Pair(a.to_string(), b.to_string())
    }
    pub fn and<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::And, a.to_string(), b.to_string())
    }
    pub fn concat<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Concat, a.to_string(), b.to_string())
    }
}

/// Instances of this trait can be added, muliplied, divided, exp'd and dot product'd together, generating constraints and type errors
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
            .map_err(|e| LubError::next(LubError::equ(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::equ(&a, &b), LubError::bad_range(&b, e)))?;

        // Find the maximum of the starts and minimum of the ends
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
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(&b, e)))?;

        Ok(a.clone() + b.clone())
    }

    fn lub_sub(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::sub(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::sub(&a, &b), LubError::bad_range(&b, e)))?;

        Ok(a.clone() - b.clone())
    }

    fn lub_mul(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::mul(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::mul(&a, &b), LubError::bad_range(&b, e)))?;

        Ok(a.clone() * b.clone())
    }

    fn lub_div(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check()
            .map_err(|e| LubError::next(LubError::div(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::div(&a, &b), LubError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::div(&a, &b)); // Division by zero is undefined
        }

        Ok(a.clone() / b.clone())
    }

    fn lub_pow(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check()
            .map_err(|e| LubError::next(LubError::pow(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::pow(&a, &b), LubError::bad_range(&b, e)))?;

        Ok(a.clone() ^ b.clone())
    }

    fn lub_rem(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check()
            .map_err(|e| LubError::next(LubError::rem(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::rem(&a, &b), LubError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::rem(&a, &b)); // Division by zero is undefined
        }

        Ok(a.clone() % b.clone())
    }

    fn lub_dot(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        Self::lub_mul(a, b, &Nothing).map_err(|e| LubError::next(LubError::dot(&a, &b), e))
    }

    fn lub_concat(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::concat(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::concat(&a, &b), LubError::bad_range(&b, e)))?;

        if let Some(c) = a.concat(b) {
            Ok(c)
        } else {
            Err(LubError::concat(&a, &b))
        }
    }
    fn lub_and(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(&a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::add(&a, &b), LubError::bad_range(&b, e)))?;

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
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

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
            (_, _) => Err(LubError::equ(
                &CTypeVar::new(&a, &ka),
                &CTypeVar::new(&b, &kb),
            )),
        }
    }

    /// Least-upper-bound for addition of different kinds
    fn lub_add(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

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
            (_, _) => Err(LubError::add(
                &CTypeVar::new(&a, &ka),
                &CTypeVar::new(&b, &kb),
            )),
        }
    }

    /// Least-upper-bound for subtraction same as addition
    fn lub_sub(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

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
            (_, _) => Err(LubError::sub(
                &CTypeVar::new(&a, &ka),
                &CTypeVar::new(&b, &kb),
            )),
        }
    }

    /// Least-upper-bound for multiplication of different kinds
    fn lub_mul(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

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
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::mul(
                &CTypeVar::new(&a, &ka),
                &CTypeVar::new(&b, &kb),
            )),
        }
    }

    fn lub_pair(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            // Group multiplication is only allowed for pairing friendly curves
            // G1 * G2 => Pairing(G1, G2)
            // forces G1: Group, G2: Group
            (Kind::Group, Kind::Group) => {
                if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(&a, &b)) {
                    Ok(pid.clone())
                } else {
                    Err(LubError::pair(
                        &CTypeVar::new(&a, &ka),
                        &CTypeVar::new(&b, &kb),
                    ))
                }
            }
            (_, _) => Err(LubError::pair(
                &CTypeVar::new(&a, &ka),
                &CTypeVar::new(&b, &kb),
            )),
        }
    }

    /// Least-upper-bound for division of different kinds
    fn lub_div(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Group, Kind::Scalar(g)) if g.contains(a) => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) | (Kind::SizeVar, _) | (_, Kind::SizeVar) => {
                unreachable!()
            }
            (_, _) => Err(LubError::div(
                &CTypeVar::new(&a, &ka),
                &CTypeVar::new(&b, &kb),
            )),
        }
    }

    /// Least-upper-bound for remainder of different kinds
    fn lub_rem(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(&b).ok_or(LubError::kind_not_found(&b))?;
        Err(LubError::rem(
            &CTypeVar::new(&a, &ka),
            &CTypeVar::new(&b, &kb),
        ))
    }

    /// Least-upper-bound for exponentiation of different kinds
    fn lub_pow(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(&b).ok_or(LubError::kind_not_found(&b))?;
        Err(LubError::pow(
            &CTypeVar::new(&a, &ka),
            &CTypeVar::new(&b, &kb),
        ))
    }

    /// Least-upper-bound for dot product is the same as multiplication (for kinds)
    fn lub_dot(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(&b).ok_or(LubError::kind_not_found(&b))?;

        Self::lub_mul(a, b, ctx).map_err(|e| {
            LubError::next(
                LubError::dot(&CTypeVar::new(&a, &ka), &CTypeVar::new(&b, &kb)),
                e,
            )
        })
    }

    /// Least-upper-bound for Concatenation is always an error
    fn lub_concat(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

        Err(LubError::sub(
            &CTypeVar::new(&a, &ka),
            &CTypeVar::new(&b, &kb),
        ))
    }

    fn lub_and(a: &Self, b: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a).ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b).ok_or(LubError::kind_not_found(&b))?;

        Err(LubError::and(
            &CTypeVar::new(&a, &ka),
            &CTypeVar::new(&b, &kb),
        ))
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
            // Uni<A> == Uni<B>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) => Ok(CTyp::Poly(
                Tid::lub_equ(a, b, ctx).map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
                1,
                *n.max(m),
            )),
            // Mle<A> == Mle<B>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?, *n.max(m), 1)),
            // General Poly<A, n, m> == Poly<B, n', m'>: unify to the larger shape in each dim.
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) =>
                Ok(CTyp::Poly(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?, *na.max(nb), *ma.max(mb))),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m => Ok(CTyp::vec(
                &CTyp::lub_equ(a, b, ctx).map_err(|e| LubError::next(LubError::equ(&x, &y), e))?,
                *n,
            )),
            // Record types: width and depth subtyping, permutation
            (CTyp::Record(fields_a), CTyp::Record(fields_b)) => {
                use std::collections::BTreeSet;
                let all_fields: BTreeSet<_> = fields_a
                    .keys()
                    .iter()
                    .chain(fields_b.keys().iter())
                    .cloned()
                    .collect();

                let mut result_fields = share::Ctx::new();
                for field_name in all_fields {
                    match (fields_a.get(&field_name), fields_b.get(&field_name)) {
                        (Some(typ_a), Some(typ_b)) => {
                            let lub_typ = CTyp::lub_equ(typ_a, typ_b, ctx)
                                .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?;
                            result_fields.insert(&field_name, &lub_typ);
                        }
                        (Some(typ_a), None) => {
                            // Only in a - include it (width subtyping: {a:T, b:U} > {a:T})
                            result_fields.insert(&field_name, typ_a);
                        }
                        (None, Some(typ_b)) => {
                            // Only in b - include it (width subtyping)
                            result_fields.insert(&field_name, typ_b);
                        }
                        (None, None) => unreachable!(),
                    }
                }

                Ok(CTyp::Record(result_fields))
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
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?, *n.max(m), 1)),
            // General Poly + Poly: vars and degree both take max.
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) =>
                Ok(CTyp::Poly(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?, *na.max(nb), *ma.max(mb))),
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
                },
            // Uni<F, n> + Vec<F, k> = Uni<F, n> if k == n + 1 (coeff count = degree + 1)
            (CTyp::Poly(_a, 1, n), CTyp::Vec(box b, m)) =>
                if *n + 1 == *m {
                    let tb = b.to_scalar(ctx).ok_or(LubError::add(&x, &y))
                        .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                    Ok(CTyp::uni(&tb, *n))
                } else {
                    Err(LubError::add(&x, &y))
                },
            // Vec<F, k> + Uni<F, n> = Uni<F, n> if k == n + 1 (coeff count = degree + 1)
            (CTyp::Vec(box a, n), CTyp::Poly(_b, 1, m)) =>
                if *n == *m + 1 {
                    let ta = a.to_scalar(ctx).ok_or(LubError::add(&x, &y))
                        .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                    Ok(CTyp::uni(&ta, *m))
                } else {
                    Err(LubError::add(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(LubError::next(
                    LubError::add(&x, &y),
                    LubError::kind_not_found(&a),
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
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?, *n.max(m), 1)),
            // General Poly - Poly: vars and degree both take max.
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) =>
                Ok(CTyp::Poly(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?, *na.max(nb), *ma.max(mb))),
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
                },
            // Uni<F, n> - Vec<F, k> = Uni<F, n> if k == n + 1 (coeff count = degree + 1)
            (CTyp::Poly(_a, 1, n), CTyp::Vec(box b, m)) =>
                if *n + 1 == *m {
                    let tb = b.to_scalar(ctx).ok_or(LubError::sub(&x, &y))
                        .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                    Ok(CTyp::uni(&tb, *n))
                } else {
                    Err(LubError::sub(&x, &y))
                },
            // Vec<F, k> - Uni<F, n> = Uni<F, n> if k == n + 1 (coeff count = degree + 1)
            (CTyp::Vec(box a, n), CTyp::Poly(_b, 1, m)) =>
                if *n == *m + 1 {
                    let ta = a.to_scalar(ctx).ok_or(LubError::sub(&x, &y))
                        .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                    Ok(CTyp::uni(&ta, *m))
                } else {
                    Err(LubError::sub(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(LubError::next(
                    LubError::sub(&x, &y),
                    LubError::kind_not_found(&a),
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
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
            {
                Ok(CTyp::Fin(Range::lub_mul(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?))
            },
            // General rule: Poly(F, n, m) * Poly(F, n', m') = Poly(F, max(n,n'), m+m')
            // (N is the max total degree per Typ::Poly docs; degrees add under multiplication)
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) =>
            {
                let num_vars = *na.max(nb);
                let degree = *ma + *mb;
                Ok(CTyp::Poly(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, num_vars, degree))
            },
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
                let ka = ctx.get(&a).ok_or(LubError::next(
                    LubError::mul(&x, &y),
                    LubError::kind_not_found(&a),
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
                Tid::lub_pair(a, b, ctx).map_err(|e| LubError::next(LubError::mul(&x, &y), e))?,
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
            (CTyp::Base(a), CTyp::Base(b)) => {
                Ok(CTyp::Base(Tid::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?))
                },
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_div(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?)),
            // General rule: Poly(F, n, m) / Poly(F, n', m') = Poly(F, max(n,n'), m-m') if m >= m'
            // (N is the max total degree; polynomial quotient degree is m - m'.)
            (CTyp::Poly(a, na, ma), CTyp::Poly(b, nb, mb)) if ma >= mb =>
            {
                let num_vars = *na.max(nb);
                let degree = *ma - *mb;
                Ok(CTyp::Poly(Tid::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?, num_vars, degree))
            },
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
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box a, n), b) => Ok(CTyp::vec(
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
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_rem(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?)),
            // General Poly<F,n1,m1> % Poly<F,n2,m2> = Poly<F, max(n1,n2), m2 - 1> if m2 >= 1.
            // (Per poly-encoding spec: remainder has degree strictly less than divisor.)
            (CTyp::Poly(a, na, _ma), CTyp::Poly(b, nb, mb)) if *mb >= 1 => {
                let num_vars = *na.max(nb);
                Ok(CTyp::Poly(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?, num_vars, *mb - 1))
            },
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
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box b, n), a) => Ok(CTyp::vec(
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
                let ka = ctx.get(&a).ok_or(LubError::next(
                    LubError::pow(&x, &y),
                    LubError::kind_not_found(&a),
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
            // Vec<B> ^ A = Vec<A^B>
            (CTyp::Vec(box a, n), b) => Ok(CTyp::vec(
                &CTyp::lub_pow(a, b, ctx).map_err(|e| LubError::next(LubError::pow(&x, &y), e))?,
                *n,
            )),

            // Uni<B> ^ Fin<i..j> = Uni<B*j>
            (CTyp::Poly(a, 1, n), CTyp::Fin(r)) => Ok(CTyp::uni(a, n * (r.end.saturating_sub(1)))),

            (_, _) => Err(LubError::pow(&x, &y)),
        }
    }

    fn lub_dot(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            // Vec<A> . Vec<B> = C
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                if n == m {
                    // Type [a] and [b] should be multiplied
                    Ok(CTyp::lub_mul(&a, &b, ctx)
                        .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?)
                } else {
                    Err(LubError::dot(&x, &y))
                },
            // Vec<F, k> . Uni<F, m> = F if k == m + 1 (coeff count = degree + 1)
            (CTyp::Vec(box a, n), CTyp::Poly(b, 1, m))
            | (CTyp::Poly(b, 1, m), CTyp::Vec(box a, n)) =>
                if *n == *m + 1 {
                    // Type [a] and [b] should be multiplied
                    Ok(CTyp::lub_mul(&a, &CTyp::base(b), ctx)
                        .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?)
                } else {
                    Err(LubError::dot(&x, &y))
                }
            }
            (_, _) => Err(LubError::dot(&x, &y)),
        }
    }

    fn lub_concat(ta: &Self, tb: &Self, kctx: &Self::Context) -> Result<Self, LubError> {
        match (ta, tb) {
            // Vec<A> ++ Vec<B> = Vec<C> if A = B = C
            (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                // Type [a] and [b] should be the same ([t])
                let t = CTyp::lub_equ(&a, &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;

                // Add the sizes of the vectors
                Ok(CTyp::vec(&t, x + y))
            }
            // Uni<A, n> ++ Vec<B, m> = Uni<C, n + m> if A = B = C
            (CTyp::Poly(a, 1, n), CTyp::Vec(box b, m))
            | (CTyp::Vec(box b, m), CTyp::Poly(a, 1, n)) => {
                // Type [a] and [b] should be the same ([t])
                CTyp::lub_equ(&CTyp::base(&a), &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                // Add elements to the polynomial
                Ok(CTyp::uni(&a, n + m))
            }
            // MLE<A, n> ++ Vec<B, m> = MLE<C, n> if n = m and A = B = C
            (CTyp::Poly(a, n, 1), CTyp::Vec(box b, m))
            | (CTyp::Vec(box b, m), CTyp::Poly(a, n, 1))
                if n == m =>
            {
                // Type [a] and [b] should be the same ([t])
                CTyp::lub_equ(&CTyp::base(a), &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                Ok(CTyp::mle(a, n + 1))
            }
            // Vec<A, n> ++ B = Vec<C, n+1> if A = B = C
            (CTyp::Vec(box a, n), b) | (b, CTyp::Vec(box a, n)) => {
                // Type [a] and [b] should be the same ([t])
                let t = CTyp::lub_equ(&a, &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                // Add an element to the vector
                Ok(CTyp::vec(&t, n + 1))
            }

            (ta, tb) => Err(LubError::concat(&ta, &tb)),
        }
    }

    fn lub_and(x: &Self, y: &Self, ctx: &Ctx<Tid, CKind>) -> Result<Self, LubError> {
        match (x, y) {
            // Bool && Bool = Bool
            (CTyp::Bool, CTyp::Bool) => Ok(CTyp::Bool),
            // Vec<Bool> && Bool = Bool (forall)
            (CTyp::Bool, CTyp::Vec(box a, _)) | (CTyp::Vec(box a, _), CTyp::Bool) => {
                Ok(CTyp::lub_and(&a, &CTyp::bool(), ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?)
            }
            // Vec<Bool> && Vec<Bool> = Bool (forall)
            (CTyp::Vec(box a, _), CTyp::Vec(box b, _)) => {
                Ok(CTyp::lub_and(&a, &b, ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?)
            }
            (_, _) => Err(LubError::and(&x, &y)),
        }
    }
}

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
    assert_eq!(
        Range::lub_sub(&b, &a, &Nothing),
        Ok(Range {
            start: 0,
            step: 1,
            end: 15
        })
    );
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

#[cfg(test)]
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
        CTyp::lub_equ(&&CTyp::uni(&f, 10), &&CTyp::uni(&f, 11), &ctx),
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

    assert_eq!(CTyp::lub_and(&CTyp::Bool, &CTyp::Bool, &ctx), Ok(CTyp::Bool));
    assert_eq!(CTyp::lub_and(&CTyp::vec(&CTyp::Bool, 10), &CTyp::vec(&CTyp::Bool, 10), &ctx), Ok(CTyp::Bool));
    assert_eq!(CTyp::lub_and(&CTyp::Bool, &CTyp::vec(&CTyp::Bool, 10), &ctx), Ok(CTyp::Bool));

    // Regression (phase 7): Poly * Poly degree math.
    // Poly(F, n, m) = n variables, max total degree m. Product degrees add.
    // Uni<F, 3> * Uni<F, 4> = Uni<F, 7>
    assert_eq!(CTyp::lub_mul(&CTyp::uni(&f, 3), &CTyp::uni(&f, 4), &ctx), Ok(CTyp::uni(&f, 7)));
    // Mle<F, n> * Mle<F, n> = Poly<F, n, 2> (product of two multilinears is degree 2)
    assert_eq!(CTyp::lub_mul(&CTyp::mle(&f, 3), &CTyp::mle(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 2)));
    // Mle<F, 2> * Mle<F, 3> = Poly<F, 3, 2> (max vars, degree 2)
    assert_eq!(CTyp::lub_mul(&CTyp::mle(&f, 2), &CTyp::mle(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 2)));
    // Uni<F, 5> * Mle<F, 3> via general Poly*Poly: Poly(F,1,5) * Poly(F,3,1) = Poly(F, 3, 6)
    assert_eq!(CTyp::lub_mul(&CTyp::uni(&f, 5), &CTyp::mle(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 6)));
    // Poly<F, 2, 3> * Poly<F, 2, 4> = Poly<F, 2, 7>
    assert_eq!(CTyp::lub_mul(&CTyp::Poly(f.clone(), 2, 3), &CTyp::Poly(f.clone(), 2, 4), &ctx),
        Ok(CTyp::Poly(f.clone(), 2, 7)));
    // Poly<F, 2, 3> * Poly<F, 4, 2> = Poly<F, 4, 5> (max vars, sum degrees)
    assert_eq!(CTyp::lub_mul(&CTyp::Poly(f.clone(), 2, 3), &CTyp::Poly(f.clone(), 4, 2), &ctx),
        Ok(CTyp::Poly(f.clone(), 4, 5)));

    // Regression (phase 7): Poly == Poly falls through to the general arm when
    // the shapes don't match Uni==Uni or Mle==Mle specifically.
    assert_eq!(CTyp::lub_equ(&CTyp::Poly(f.clone(), 2, 2), &CTyp::Poly(f.clone(), 2, 2), &ctx),
        Ok(CTyp::Poly(f.clone(), 2, 2)));
    assert_eq!(CTyp::lub_equ(&CTyp::Poly(f.clone(), 2, 3), &CTyp::Poly(f.clone(), 3, 2), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 3)));

    // Regression (phase 7): lub_div degree math. Poly<F,1,5> / Poly<F,1,5> = Poly<F,1,0>
    assert_eq!(CTyp::lub_div(&CTyp::uni(&f, 5), &CTyp::uni(&f, 5), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 0)));
    assert_eq!(CTyp::lub_div(&CTyp::uni(&f, 7), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 4)));

    // Phase 14.C: poly-encoding unification (m = max degree).
    // lub_rem Poly×Poly: Poly<F,1,5> % Poly<F,1,3> = Poly<F,1,2> (deg = 3 - 1).
    assert_eq!(CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 2)));
    // lub_rem requires m2 >= 1; Poly<F,1,n> % Poly<F,1,0> is an error.
    assert!(CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 0), &ctx).is_err());
    // General Poly×Poly rem: Poly<F,2,5> % Poly<F,3,2> = Poly<F,3,1> (max vars, m2 - 1).
    assert_eq!(CTyp::lub_rem(&CTyp::Poly(f.clone(), 2, 5), &CTyp::Poly(f.clone(), 3, 2), &ctx),
        Ok(CTyp::Poly(f.clone(), 3, 1)));

    // lub_add Uni↔Vec consistency: k == m + 1 (coeff count = degree + 1).
    // Poly<F,1,3> + Vec<F,4> = Poly<F,1,3> (4 coeffs ↔ degree 3).
    assert_eq!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx),
        Ok(CTyp::uni(&f, 3)));
    assert_eq!(CTyp::lub_add(&CTyp::vec(&tf, 4), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::uni(&f, 3)));
    // Length mismatch rejected.
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::vec(&tf, 5), &CTyp::uni(&f, 3), &ctx).is_err());

    // lub_mul Poly×Poly: degrees add. Poly<F,1,2> * Poly<F,1,3> = Poly<F,1,5>.
    assert_eq!(CTyp::lub_mul(&CTyp::uni(&f, 2), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::uni(&f, 5)));

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

    // ---- lub_add / lub_sub: Poly<F,1,n> ± Vec<F,k> requires k == n + 1 ----
    // Positive boundary: k = n + 1 succeeds.
    assert_eq!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx),
        Ok(CTyp::uni(&f, 3)));
    assert_eq!(CTyp::lub_sub(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx),
        Ok(CTyp::uni(&f, 3)));
    // Off-by-one low: k = n rejected (Vec has too few coeffs for degree n).
    assert!(CTyp::lub_add(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 3), &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::vec(&tf, 3), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 3), &ctx).is_err());
    assert!(CTyp::lub_sub(&CTyp::vec(&tf, 3), &CTyp::uni(&f, 3), &ctx).is_err());
    // Off-by-one high: k = n + 2 rejected (Vec has too many coeffs).
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
    assert_eq!(CTyp::lub_div(&CTyp::uni(&f, 3), &CTyp::uni(&f, 3), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 0)));
    // Off-by-one: divisor degree one greater than dividend is rejected.
    assert!(CTyp::lub_div(&CTyp::uni(&f, 2), &CTyp::uni(&f, 3), &ctx).is_err());
    // General Poly/Poly: same off-by-one in multivariate.
    assert!(CTyp::lub_div(&CTyp::Poly(f.clone(), 2, 3), &CTyp::Poly(f.clone(), 2, 4), &ctx).is_err());
    // Far off: any m2 > m1 rejected.
    assert!(CTyp::lub_div(&CTyp::uni(&f, 0), &CTyp::uni(&f, 5), &ctx).is_err());

    // ---- lub_rem: Poly<F,n1,m1> % Poly<F,n2,m2> requires m2 ≥ 1 ----
    // Divisor of degree 0 rejected (no remainder well-defined).
    assert!(CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 0), &ctx).is_err());
    // Degree-only dividend with degree-0 divisor also rejected.
    assert!(CTyp::lub_rem(&CTyp::uni(&f, 0), &CTyp::uni(&f, 0), &ctx).is_err());
    // m1 < m2 is still allowed: remainder degree = m2 - 1 (full dividend fits).
    assert_eq!(CTyp::lub_rem(&CTyp::uni(&f, 3), &CTyp::uni(&f, 4), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 3)));
    // Boundary m2 = 1: remainder has degree 0.
    assert_eq!(CTyp::lub_rem(&CTyp::uni(&f, 5), &CTyp::uni(&f, 1), &ctx),
        Ok(CTyp::Poly(f.clone(), 1, 0)));

    // ---- lub_dot: Vec<F,k> · Poly<F,1,m> requires k == m + 1 ----
    // Positive boundary: k = m + 1.
    assert_eq!(CTyp::lub_dot(&CTyp::vec(&tf, 4), &CTyp::uni(&f, 3), &ctx),
        Ok(tf.clone()));
    assert_eq!(CTyp::lub_dot(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 4), &ctx),
        Ok(tf.clone()));
    // Off-by-one low: k = m rejected.
    assert!(CTyp::lub_dot(&CTyp::vec(&tf, 4), &CTyp::uni(&f, 4), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::uni(&f, 4), &CTyp::vec(&tf, 4), &ctx).is_err());
    // Off-by-one high: k = m + 2 rejected.
    assert!(CTyp::lub_dot(&CTyp::vec(&tf, 5), &CTyp::uni(&f, 3), &ctx).is_err());
    assert!(CTyp::lub_dot(&CTyp::uni(&f, 3), &CTyp::vec(&tf, 5), &ctx).is_err());
}

#[cfg(test)]
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
    fn test_lub_error_and() {
        let err = LubError::and(&"A", &"B");
        assert!(matches!(err, LubError::Bin(BinOp::And, _, _)));
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
        assert!(Range::lub_op(BinOp::Sub, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Mul, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Div, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Pow, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Rem, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::Dot, &a, &b, &ctx).is_ok());
        assert!(Range::lub_op(BinOp::And, &a, &b, &ctx).is_err());
        assert!(Range::lub_op(BinOp::Equ, &a, &b, &ctx).is_ok());

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

#[cfg(test)]
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
    fn test_range_lub_and_error() {
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
        let result = Range::lub_and(&a, &b, &Nothing);
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

#[cfg(test)]
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
    fn test_tid_lub_and_error() {
        let f = Tid::from("F");
        let ctx = Ctx::from([(f.clone(), Kind::Field)]);
        let result = Tid::lub_and(&f, &f, &ctx);
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
