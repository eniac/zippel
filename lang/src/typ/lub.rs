use crate::ast::BinOp;
use crate::typ::{Kind, Nothing, CTyp, TypeVar};
use crate::typ::range::{Range, RangeError};
use crate::id::Tid;
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
pub trait Lub where Self: Sized {
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
        a.check().map_err(|e|
                LubError::next(
                    LubError::equ(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::equ(&a, &b),
                    LubError::bad_range(&b, e)))?;

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
        a.check().map_err(|e|
                LubError::next(
                    LubError::add(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::add(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a.clone() + b.clone())
    }

    fn lub_sub(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::sub(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::sub(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a.clone() - b.clone())
    }

    fn lub_mul(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::mul(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::mul(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a.clone() * b.clone())
    }

    fn lub_div(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        println!("Here Lub::div with a: {:?}, b: {:?}", a, b);
        // Validate Ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::div(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::div(&a, &b),
                    LubError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::div(&a, &b)); // Division by zero is undefined
        }

        Ok(a.clone() / b.clone())
    }

    fn lub_pow(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::pow(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::pow(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a.clone() ^ b.clone())
    }

    fn lub_rem(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::rem(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::rem(&a, &b),
                    LubError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::rem(&a, &b)); // Division by zero is undefined
        }

        Ok(a.clone() % b.clone())
    }

    fn lub_dot(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        Self::lub_mul(a, b, &Nothing)
            .map_err(|e| LubError::next(LubError::dot(&a, &b), e))
    }

    fn lub_concat(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::concat(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::concat(&a, &b),
                    LubError::bad_range(&b, e)))?;

        if let Some(c) = a.concat(b) {
            return Ok(c);
        } else {
            return Err(LubError::concat(&a, &b));
        }
    }
    fn lub_and(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::add(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::add(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Err(LubError::and(&a, &b))
    }
    fn lub_pair(a: &Self, b: &Self, _: &Nothing) -> Result<Self, LubError> {
        Err(LubError::pair(&a, &b))
    }
}

/// Least-upper bound of type variables
impl Lub for Tid {
    type Context = Ctx<Tid, Kind>;
    /// Can the two kinds be unified into one kind that describes both?
    fn lub_equ(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Group, Kind::Group) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::equ(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
        }
    }

    /// Least-upper-bound for addition of different kinds
    fn lub_add(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Group, Kind::Group) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::add(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
        }
    }

    /// Least-upper-bound for subtraction same as addition
    fn lub_sub(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            (Kind::Group, Kind::Group) if a == b => Ok(a.clone()),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::sub(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
        }
    }

    /// Least-upper-bound for multiplication of different kinds
    fn lub_mul(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a.clone()),
            // Scalar multiplication: Scalar * Group = Group * Scalar = Group
            (Kind::Scalar(g), Kind::Group) if g.contains(b) => Ok(b.clone()),
            (Kind::Group, Kind::Scalar(g)) if g.contains(a) => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::mul(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
        }
    }

    fn lub_pair(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            // Group multiplication is only allowed for pairing friendly curves
            // G1 * G2 => Pairing(G1, G2)
            // forces G1: Group, G2: Group
            (Kind::Group, Kind::Group) =>
                if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(&a, &b)) {
                    Ok(pid.clone())
                } else {
                    Err(LubError::pair(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
                }
            (_, _) => Err(LubError::pair(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
        }
    }

    /// Least-upper-bound for division of different kinds
    fn lub_div(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        println!("Here 2 Tid::div with a: {:?}, b: {:?}", a, b);
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => 
            {
                println!("Field / Field");
                println!("a: {:?}, b: {:?}", a, b);
                Ok(a.clone())
            },
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => 
            {
                println!("Scalar / Scalar");
                println!("a: {:?}, b: {:?}", a, b);
                Ok(a.clone())
            },
            (Kind::Group, Kind::Scalar(g)) if g.contains(a) => Ok(a.clone()),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::div(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
        }
    }

    /// Least-upper-bound for remainder of different kinds
    fn lub_rem(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::kind_not_found(&b))?;
        Err(LubError::rem(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
    }

    /// Least-upper-bound for exponentiation of different kinds
    fn lub_pow(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::kind_not_found(&b))?;
        Err(LubError::pow(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
    }

    /// Least-upper-bound for dot product is the same as multiplication (for kinds)
    fn lub_dot(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::kind_not_found(&b))?;

        Self::lub_mul(a, b, ctx)
            .map_err(|e|
                LubError::next(LubError::dot(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)), e))
    }

    /// Least-upper-bound for Concatenation is always an error
    fn lub_concat(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;

        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        Err(LubError::sub(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
    }

    fn lub_and(a: &Self, b: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(a)
            .ok_or(LubError::kind_not_found(&a))?;
        let kb = ctx.get(b)
            .ok_or(LubError::kind_not_found(&b))?;

        Err(LubError::and(&TypeVar::new(&a, &ka), &TypeVar::new(&b, &kb)))
    }
}

impl Lub for CTyp {
    type Context = Ctx<Tid, Kind>;
    fn lub_equ(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Bool, CTyp::Bool) => Ok(CTyp::Bool),
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?)),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_equ(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?)),
            // Uni<A> == Uni<B>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) =>
                Ok(CTyp::Poly(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?, 1, *n.max(m))),
            // Mle<A> == Mle<B>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?, *n.max(m), 1)),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(&CTyp::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?, *n)),
            // Indices can act like finite fields
            (a, b) => {
                let ta = a.to_scalar(ctx).ok_or(LubError::equ(&x, &y))?;
                let tb = b.to_scalar(ctx).ok_or(LubError::equ(&x, &y))?;
                Ok(CTyp::Base(Tid::lub_equ(&ta, &tb, ctx)
                    .map_err(|e| LubError::next(LubError::equ(&x, &y), e))?))
            }
        }
    }

    fn lub_add(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        println!("Here 1 CTyp::add with x: {:?}, y: {:?}", x, y);
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_add(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?)),
            // Uni<A> + Uni<B> = Uni<max(A, B)>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) =>
                Ok(CTyp::Poly(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?, 1, *n.max(m))),
            // Mle<A> + Mle<B> = Mle<max(A, B)>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?, *n.max(m), 1)),
            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_add(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::add(&x, &y), e))?, *n))
                } else {
                    Err(LubError::add(&x, &y))
                },
            // Uni<A> + Vec<B> = Uni<C> where C = A = B
            (CTyp::Poly(_a, 1, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    let tb = b.to_scalar(ctx).ok_or(LubError::add(&x, &y))
                        .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                    Ok(CTyp::uni(&tb, *n))
                } else {
                    Err(LubError::add(&x, &y))
                },
            // Vec<A> + Uni<B> = Uni<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Poly(_b, 1, m)) =>
                if n == m {
                    let ta = a.to_scalar(ctx).ok_or(LubError::add(&x, &y))
                        .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                    Ok(CTyp::uni(&ta, *n))
                } else {
                    Err(LubError::add(&x, &y))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(LubError::add(&x, &y), LubError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::add(&x, &y))
                }
            },
            // Finite fields can act like univariate polynomials
            (CTyp::Base(a), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Base(a)) => {
                let t = Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                Ok(CTyp::Poly(t, 1, *n))
            }
            // Indices can act like univariate polynomials
            (CTyp::Fin(_), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Fin(_)) =>
                Ok(CTyp::uni(b, *n)),
            (CTyp::Poly(a, n, 1), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Poly(a, n, 1)) => {
                let t = Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::add(&x, &y), e))?;
                Ok(CTyp::Poly(t, *n, 1))
            },
            (CTyp::Poly(a, n, 1), CTyp:: Fin(_)) | (CTyp::Fin(_), CTyp::Poly(a, n, 1)) => {
                Ok(CTyp::Poly(a.clone(), *n, 1))
            }
            (_, _) => Err(LubError::add(&x, &y)),
        }
    }

    fn lub_sub(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_sub(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?)),
            // Uni<A> - Uni<B> = Uni<max(A, B)>
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) =>
                Ok(CTyp::Poly(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?, 1, *n.max(m))),
            // Mle<A> - Mle<B> = Mle<max(A, B)>
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
                Ok(CTyp::Poly(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?, *n.max(m), 1)),
            // Vec<A> - Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_sub(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?, *n))
                } else {
                    Err(LubError::sub(&x, &y))
                },
            // Uni<A> - Vec<B> = Uni<C> where C = A = B
            (CTyp::Poly(_a, 1, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    let tb = b.to_scalar(ctx).ok_or(LubError::sub(&x, &y))
                        .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                    Ok(CTyp::uni(&tb, *n))
                } else {
                    Err(LubError::sub(&x, &y))
                },
            // Vec<A> - Uni<B> = Uni<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Poly(_b, 1, m)) =>
                if n == m {
                    let ta = a.to_scalar(ctx).ok_or(LubError::sub(&x, &y))
                        .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                    Ok(CTyp::uni(&ta, *n))
                } else {
                    Err(LubError::sub(&x, &y))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(LubError::sub(&x, &y), LubError::kind_not_found(&a)))?;
                if ka.is_scalar() {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::sub(&x, &y))
                }
            },
            // Finite fields can act like univariate polynomials
            (CTyp::Base(a), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Base(a)) => {
                let t = Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                Ok(CTyp::Poly(t, 1, *n))
            }
            // Indices can act like univariate polynomials
            (CTyp::Fin(_), CTyp::Poly(b, 1, n)) | (CTyp::Poly(b, 1, n), CTyp::Fin(_)) =>
                Ok(CTyp::uni(b, *n)),
            (CTyp::Poly(a, n, 1), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Poly(a, n, 1)) => {
                let t = Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::sub(&x, &y), e))?;
                Ok(CTyp::Poly(t, *n, 1))
            },
            (CTyp::Poly(a, n, 1), CTyp:: Fin(_)) | (CTyp::Fin(_), CTyp::Poly(a, n, 1)) => {
                Ok(CTyp::Poly(a.clone(), *n, 1))
            }    
            (_, _) => Err(LubError::sub(&x, &y))
        }
    }

    fn lub_mul(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
            {
                println!("Fin<A> * Fin<B> = Fin<A * B>");
                println!("A: {:?}, B: {:?}", a, b);
                Ok(CTyp::Fin(Range::lub_mul(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?))
            },
            // Uni<A> * Uni<B> = Virtual (product of polynomials)
            (CTyp::Poly(a, 1, _n), CTyp::Poly(b, 1, _m)) =>
            {
                // Return Poly with M != 1 and N != 1 to indicate Virtual
                Ok(CTyp::Poly(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, 2, 2))
            },
            // Mle<A> * Mle<B> = Virtual (product of polynomials)
            (CTyp::Poly(a, n, 1), CTyp::Poly(b, m, 1)) =>
            {
                // Return Poly with M != 1 and N != 1 to indicate Virtual
                Ok(CTyp::Poly(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, 2, 2))
            },
            // Uni<A> * Mle<B> or Mle<A> * Uni<B> = Virtual
            (CTyp::Poly(a, 1, _n), CTyp::Poly(b, m, 1)) | (CTyp::Poly(a, m, 1), CTyp::Poly(b, 1, _n)) =>
            {
                // Return Poly with M != 1 and N != 1 to indicate Virtual
                Ok(CTyp::Poly(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, 2, 2))
            },
            // Any polynomial * general polynomial -> Virtual
            (CTyp::Poly(a, _ma, _na), CTyp::Poly(b, _mb, _nb)) if (*_ma != 1 || *_na != 1) || (*_mb != 1 || *_nb != 1) =>
            {
                // Already a general polynomial or virtual -> Virtual
                Ok(CTyp::Poly(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, 2, 2))
            },
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
            {
                println!("Vec<A> * Vec<B> = Vec<C> where C = A = B");
                println!("A: {:?}, B: {:?}", a, b);
                println!("n: {:?}, m: {:?}", n, m);
                println!("n + m - 1: {:?}", n + m - 1);
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_mul(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, *n))
                } else {
                    Err(LubError::mul(&x, &y))
                }
            },
            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(&CTyp::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?, *n)),
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
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(LubError::mul(&x, &y), LubError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::mul(&x, &y))
                }
            },
            (_, _) => Err(LubError::mul(&x, &y))
        }
    }

    fn lub_pair(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_pair(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::mul(&x, &y), e))?)),
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_pair(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::pair(&x, &y), e))?, *n))
                } else {
                    Err(LubError::pair(&x, &y))
                },
            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(&CTyp::lub_pair(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::pair(&x, &y), e))?, *n)),
            (_, _) => Err(LubError::pair(&x, &y))
        }
    }

    fn lub_div(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        println!("Lub::div with x: {:?}, y: {:?}", x, y);
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) => {
                println!("Base<A> / Base<B>");
                println!("a: {:?}, b: {:?}", a, b);
                Ok(CTyp::Base(Tid::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?))
                },
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_div(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?)),
            // Uni<A> / Uni<B> = Uni<A - B> if A > B
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) if n >= m =>
            {
                println!("Uni<A> / Uni<B> = Uni<A - B> if A > B");
                println!("A: {:?}, B: {:?}", a, b);
                println!("n: {:?}, m: {:?}", n, m);
                println!("n - m + 1: {:?}", n - m + 1);
                Ok(CTyp::Poly(Tid::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?, 1, n - m + 1))
            },
            // Vec<A> / Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) => {
                println!("Vec<A> / Vec<B> = Vec<C> where C = A = B");
                println!("A: {:?}, B: {:?}", a, b);
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_div(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::div(&x, &y), e))?, *n))
                } else {
                    Err(LubError::div(&x, &y))
                }},
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box a, n), b) =>
                Ok(CTyp::vec(&CTyp::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?, *n)),

            // Uni<A> / c = Uni<A> if c is a finite field
            (CTyp::Poly(b, 1, n), a) => {
                let t = CTyp::lub_div(&CTyp::base(b), a, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Poly(c, 1, *n))
                } else {
                    Err(LubError::div(&x, &y))
                }
            }
            // Mle<A> / c = Mle<A> if c is a finite field
            (CTyp::Poly(b, n, 1), a) => {
                let t = CTyp::lub_div(&CTyp::base(b), a, ctx)
                    .map_err(|e| LubError::next(LubError::div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Poly(c, *n, 1))
                } else {
                    Err(LubError::div(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => Ok(CTyp::base(a)),
            (_, _) => Err(LubError::div(&x, &y))
        }
    }

    fn lub_rem(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_rem(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?)),
            // Uni<A> % Uni<B> = Uni<C> where deg(C) = deg(B) - 1
            (CTyp::Poly(a, 1, n), CTyp::Poly(b, 1, m)) if n >= m =>
                Ok(CTyp::Poly(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?, 1, m.saturating_sub(1))),
            // Vec<A> % Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_rem(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?, *n))
                } else {
                    Err(LubError::rem(&x, &y))
                },
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(&CTyp::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::rem(&x, &y), e))?, *n)),

            (_, _) => Err(LubError::rem(&x, &y))
        }
    }

    fn lub_pow(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_pow(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?)),
            (CTyp::Base(a), CTyp::Fin(_)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(
                            LubError::pow(&x, &y),
                            LubError::kind_not_found(&a)))?;
                if ka.is_scalar() {
                    Ok(CTyp::base(a))
                } else {
                    Err(LubError::pow(&x, &y))
                }
            },
            // Vec<A> ^ Vec<B> = Vec<C>
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(&CTyp::lub_pow(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?, *n))
                } else {
                    Err(LubError::pow(&x, &y))
                },
            // Vec<B> ^ A = Vec<A^B>
            (CTyp::Vec(box a, n), b) =>
                Ok(CTyp::vec(&CTyp::lub_pow(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::pow(&x, &y), e))?, *n)),

            // Uni<B> ^ Fin<i..j> = Uni<B*j>
            (CTyp::Poly(a, 1, n), CTyp::Fin(r)) =>
                Ok(CTyp::uni(a, n * (r.end.saturating_sub(1)))),

            (_, _) => Err(LubError::pow(&x, &y))
        }
    }
    
    fn lub_dot(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            // Vec<A> . Vec<B> = C
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    // Type [a] and [b] should be multiplied
                    Ok(CTyp::lub_mul(&a, &b, ctx)
                            .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?)
                } else {
                    Err(LubError::dot(&x, &y))
                },
            // Vec<A> . Uni<A> = A
            (CTyp::Vec(box a, n), CTyp::Poly(b, 1, m))
            | (CTyp::Poly(b, 1, m), CTyp::Vec(box a, n)) =>
                if n == m {
                    // Type [a] and [b] should be multiplied
                    Ok(CTyp::lub_mul(&a, &CTyp::base(b), ctx)
                            .map_err(|e| LubError::next(LubError::dot(&x, &y), e))?)
                } else {
                    Err(LubError::dot(&x, &y))
                },
            (_, _) => Err(LubError::dot(&x, &y))
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
            },
            // Uni<A, n> ++ Vec<B, m> = Uni<C, n + m> if A = B = C
            (CTyp::Poly(a, 1, n), CTyp::Vec(box b, m))
            | (CTyp::Vec(box b, m), CTyp::Poly(a, 1, n)) => {
                // Type [a] and [b] should be the same ([t])
                CTyp::lub_equ(&CTyp::base(&a), &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                // Add elements to the polynomial
                Ok(CTyp::uni(&a, n + m))
            },
            // MLE<A, n> ++ Vec<B, m> = MLE<C, n> if n = m and A = B = C
            (CTyp::Poly(a, n, 1), CTyp::Vec(box b, m))
            | (CTyp::Vec(box b, m), CTyp::Poly(a, n, 1)) 
            if n == m => {
                // Type [a] and [b] should be the same ([t])
                CTyp::lub_equ(&CTyp::base(a), &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                Ok(CTyp::mle(a, n+1))
            },
            // Vec<A, n> ++ B = Vec<C, n+1> if A = B = C
            (CTyp::Vec(box a, n), b)
            | (b, CTyp::Vec(box a, n)) => {
                // Type [a] and [b] should be the same ([t])
                let t = CTyp::lub_equ(&a, &b, kctx)
                    .map_err(|e| LubError::next(LubError::concat(ta, tb), e))?;
                // Add an element to the vector
                Ok(CTyp::vec(&t, n + 1))
            },
 
            (ta, tb) => Err(LubError::concat(&ta, &tb))
        }
    }

    fn lub_and(x: &Self, y: &Self, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x, y) {
            // Bool && Bool = Bool
            (CTyp::Bool, CTyp::Bool) => Ok(CTyp::Bool),
            // Vec<Bool> && Bool = Bool (forall)
            (CTyp::Bool, CTyp::Vec(box a, _)) | (CTyp::Vec(box a, _), CTyp::Bool) =>
                Ok(CTyp::lub_and(&a, &CTyp::bool(), ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?),
            // Vec<Bool> && Vec<Bool> = Bool (forall)
            (CTyp::Vec(box a, _), CTyp::Vec(box b, _)) =>
                Ok(CTyp::lub_and(&a, &b, ctx)
                    .map_err(|e| LubError::next(LubError::and(&x, &y), e))?),
            (_, _) => Err(LubError::and(&x, &y))
        }
    }
}

#[test]
fn lub_range() {
    let a = Range { start: 0, step: 1, end: 10 };
    let b = Range { start: 5, step: 1, end: 15 };

    assert_eq!(Range::lub_equ(&a, &b, &Nothing), Ok(Range { start: 0, step: 1, end: 15 }));
    assert_eq!(Range::lub_add(&a, &b, &Nothing), Ok(Range { start: 5, step: 1, end: 24 }));
    assert_eq!(Range::lub_sub(&b, &a, &Nothing), Ok(Range { start: 0, step: 1, end: 15 }));
    assert_eq!(Range::lub_mul(&a, &b, &Nothing), Ok(Range { start: 0, step: 1, end: 127 }));
    assert_eq!(Range::lub_div(&b, &Range { start: 1, step: 1, end: 15 }, &Nothing), Ok(Range { start: 0, step: 1, end: 15 }));
}

#[cfg(test)] use share::Set;
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
    assert_eq!(CTyp::lub_equ(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 10), &ctx), Ok(CTyp::vec(&tf, 10)));
    assert!(CTyp::lub_equ(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 11), &ctx).is_err());
    assert!(CTyp::lub_equ(&CTyp::vec(&tf, 10), &CTyp::vec(&tg1, 10), &ctx).is_err());
    assert_eq!(CTyp::lub_equ(&&CTyp::uni(&f, 10), &&CTyp::uni(&f, 11), &ctx), Ok(CTyp::uni(&f, 11)));

    assert_eq!(CTyp::lub_add(&tf, &tf, &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_add(&tg1, &tg1, &ctx), Ok(tg1.clone()));
    assert!(CTyp::lub_add(&tg1, &tg2, &ctx).is_err());
    assert_eq!(CTyp::lub_add(&ts1, &ts1, &ctx), Ok(ts1.clone()));
    assert!(CTyp::lub_add(&ts1, &ts2, &ctx).is_err());
    assert_eq!(CTyp::lub_add(&tp, &tp, &ctx), Ok(tp.clone()));
    assert!(CTyp::lub_add(&tp, &tg1, &ctx).is_err());
    assert!(CTyp::lub_add(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 11), &ctx).is_err());
    assert_eq!(CTyp::lub_add(&CTyp::vec(&tf, 10), &CTyp::vec(&tf, 10), &ctx), Ok(CTyp::vec(&tf, 10)));
    assert_eq!(CTyp::lub_add(&CTyp::uni(&f, 10), &CTyp::uni(&f, 11), &ctx), Ok(CTyp::uni(&f, 11)));
    assert_eq!(CTyp::lub_add(&CTyp::mle(&f, 10), &CTyp::mle(&f, 11), &ctx), Ok(CTyp::mle(&f, 11)));
    assert_eq!(CTyp::lub_add(&CTyp::vec(&tg1, 10), &CTyp::vec(&tg1, 10), &ctx), Ok(CTyp::vec(&tg1, 10)));

    assert_eq!(CTyp::lub_pair(&tg1, &tg2, &ctx), Ok(tp.clone()));
    assert_eq!(CTyp::lub_pair(&tg2, &tg1, &ctx), Ok(tp.clone()));

    assert_eq!(CTyp::lub_pow(&tf, &tr, &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_pow(&CTyp::vec(&tf, 10), &tr, &ctx), Ok(CTyp::vec(&tf, 10)));
    assert_eq!(CTyp::lub_pow(&CTyp::uni(&f, 10), &tr, &ctx), Ok(CTyp::uni(&f, 100)));
    assert!(CTyp::lub_pow(&CTyp::mle(&f, 10), &tr, &ctx).is_err());

    assert_eq!(CTyp::lub_and(&CTyp::Bool, &CTyp::Bool, &ctx), Ok(CTyp::Bool));
    assert_eq!(CTyp::lub_and(&CTyp::vec(&CTyp::Bool, 10), &CTyp::vec(&CTyp::Bool, 10), &ctx), Ok(CTyp::Bool));
    assert_eq!(CTyp::lub_and(&CTyp::Bool, &CTyp::vec(&CTyp::Bool, 10), &ctx), Ok(CTyp::Bool));

}


