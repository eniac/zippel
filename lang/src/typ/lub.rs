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
    #[error(
        "LubError: Degree overflow under reduce multiplication: degree {0} * vector length {1}"
    )]
    DegreeOverflow(usize, usize),
}

impl LubError {
    pub fn next(a: LubError, b: LubError) -> Self {
        LubError::Next(Box::new(a), Box::new(b))
    }
    pub fn kind_not_found(id: &Tid) -> Self {
        LubError::KindNotFound(id.clone())
    }
    pub fn bad_range(r: &Range<usize>, e: RangeError) -> Self {
        LubError::BadRange(*r, e)
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
            .map_err(|e| LubError::next(LubError::equ(&a, &b), LubError::bad_range(a, e)))?;
        b.check()
            .map_err(|e| LubError::next(LubError::equ(&a, &b), LubError::bad_range(b, e)))?;

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

        Err(LubError::sub(&CTypeVar::new(a, ka), &CTypeVar::new(b, kb)))
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
            // Record types: strict field match (same names, same count, per-field lub_equ)
            (CTyp::Record(fields_a), CTyp::Record(fields_b)) => {
                if fields_a.len() != fields_b.len() {
                    return Err(LubError::equ(&x, &y));
                }
                let mut result_fields = share::Ctx::new();
                for (name, typ_a) in fields_a.iter() {
                    let typ_b = fields_b.get(&name).ok_or_else(|| LubError::equ(&x, &y))?;
                    let lub_typ = CTyp::lub_equ(typ_a, typ_b, ctx)
                        .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?;
                    result_fields.insert(name, &lub_typ);
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
                let degree = *ma + *mb;
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
            (CTyp::Poly(a, 1, n), CTyp::Fin(r)) => Ok(CTyp::uni(a, n * (r.end.saturating_sub(1)))),

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
                // Type [a] and [b] should be the same ([t])
                let t = CTyp::lub_equ(a, b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;

                // Add the sizes of the vectors
                Ok(CTyp::vec(&t, x + y))
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
                Ok(CTyp::vec(&t, n + 1))
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
            (CTyp::Vec(box a, n), CTyp::Bool) => {
                let t = CTyp::lub_and(a, y, ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?;
                Ok(CTyp::vec(&t, *n))
            }
            (CTyp::Bool, CTyp::Vec(box b, m)) => {
                let t = CTyp::lub_and(x, b, ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?;
                Ok(CTyp::vec(&t, *m))
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

    assert_eq!(
        CTyp::lub_and(&CTyp::Bool, &CTyp::Bool, &ctx),
        Ok(CTyp::Bool)
    );
    assert_eq!(
        CTyp::lub_and(
            &CTyp::vec(&CTyp::Bool, 10),
            &CTyp::vec(&CTyp::Bool, 10),
            &ctx
        ),
        Ok(CTyp::vec(&CTyp::Bool, 10))
    );
    assert_eq!(
        CTyp::lub_and(&CTyp::Bool, &CTyp::vec(&CTyp::Bool, 10), &ctx),
        Ok(CTyp::vec(&CTyp::Bool, 10))
    );
    assert_eq!(
        CTyp::lub_and(&CTyp::vec(&CTyp::Bool, 10), &CTyp::Bool, &ctx),
        Ok(CTyp::vec(&CTyp::Bool, 10))
    );

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
#[cfg(test)]
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
        for i in 0..num_fields {
            fields.insert(&names[i].to_string(), &arb_ctyp(u)?);
        }
        Ok(CTyp::Record(fields))
    }

    #[test]
    fn test_record_lub_width_subtyping() {
        let ctx = kind_ctx();
        let mut fields_a = share::Ctx::new();
        fields_a.insert(&"x".to_string(), &tf());

        let mut fields_b = share::Ctx::new();
        fields_b.insert(&"x".to_string(), &tf());
        fields_b.insert(&"y".to_string(), &CTyp::Poly(f(), 1, 3));

        let a = CTyp::Record(fields_a);
        let b = CTyp::Record(fields_b);

        let mut expected_fields = share::Ctx::new();
        expected_fields.insert(&"x".to_string(), &tf());
        let expected = CTyp::Record(expected_fields);

        assert_eq!(CTyp::lub_equ(&a, &b, &ctx), Ok(expected));
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
