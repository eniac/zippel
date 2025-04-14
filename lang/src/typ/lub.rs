use crate::typ::{Kind, Nothing, CTyp, TypeVar};
use crate::typ::range::{Range, RangeError};
use crate::id::Tid;
use share::Ctx;

use std::fmt;
use thiserror::Error;

#[derive(Error, PartialEq, Eq, Debug)]
pub enum BinopError<K: fmt::Display> {
    #[error("Cannot take equality of {0} == {1}")]
    Equ(K, K),
    #[error("Cannot take sum of {0} + {1}")]
    Add(K, K),
    #[error("Cannot take difference of {0} - {1}")]
    Sub(K, K),
    #[error("Cannot take product of {0} * {1}")]
    Mul(K, K),
    #[error("Cannot take quotient of {0} / {1}")]
    Div(K, K),
    #[error("Cannot take exponent of {0} ^ {1}")]
    Pow(K, K),
    #[error("Cannot take remainder of {0} % {1}")]
    Rem(K, K),
    #[error("Cannot take dot-product of {0} . {1}")]
    Dot(K, K),
}

#[derive(Error, PartialEq, Debug)]
pub enum LubError {
    #[error("{0}\n\n{1}")]
    Next(Box<LubError>, Box<LubError>),
    #[error("LubError: During binary operation typechecking type variables\n\n{0}")]
    Kind(#[from] BinopError<TypeVar>),
    #[error("LubError: During binary operation typechecking type identifiers\n\n{0}")]
    Tid(#[from] BinopError<Tid>),
    #[error("LubError: During binary operation typechecking ranges\n\n{0}")]
    Range(#[from] BinopError<Range<usize>>),
    #[error("LubError: During binary operation typechecking types\n\n{0}")]
    Type(#[from] BinopError<CTyp>),
    #[error("LubError: Malformed range {0}\n\n{1}")]
    BadRange(Range<usize>, RangeError),
    #[error("LubError: Kind {0} not found")]
    KindNotFound(Tid),
}

impl LubError {
    pub fn kind_not_found(id: &Tid) -> Self {
        LubError::KindNotFound(id.clone())
    }
    pub fn next(a: LubError, b: LubError) -> Self {
        LubError::Next(Box::new(a), Box::new(b))
    }
    pub fn bad_range(r: &Range<usize>, e: RangeError) -> Self {
        LubError::BadRange(r.clone(), e)
    }
    pub fn tv_equ(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Equ(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_add(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Add(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_sub(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Sub(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_mul(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Mul(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_div(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Div(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_pow(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Pow(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_rem(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Rem(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_dot(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        LubError::Kind(BinopError::Dot(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tid_equ(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Equ(a.clone(), b.clone()))
    }
    pub fn tid_add(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Add(a.clone(), b.clone()))
    }
    pub fn tid_sub(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Sub(a.clone(), b.clone()))
    }
    pub fn tid_mul(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Mul(a.clone(), b.clone()))
    }
    pub fn tid_div(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Div(a.clone(), b.clone()))
    }
    pub fn tid_pow(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Pow(a.clone(), b.clone()))
    }
    pub fn tid_dot(a: &Tid, b: &Tid) -> Self {
        LubError::Tid(BinopError::Dot(a.clone(), b.clone()))
    }
    pub fn range_equ(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Equ(a.clone(), b.clone()))
    }
    pub fn range_add(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Add(a.clone(), b.clone()))
    }
    pub fn range_sub(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Sub(a.clone(), b.clone()))
    }
    pub fn range_mul(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Mul(a.clone(), b.clone()))
    }
    pub fn range_rem(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Rem(a.clone(), b.clone()))
    }
    pub fn range_dot(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Dot(a.clone(), b.clone()))
    }
    pub fn range_div(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Div(a.clone(), b.clone()))
    }
    pub fn range_pow(a: &Range<usize>, b: &Range<usize>) -> Self {
        LubError::Range(BinopError::Pow(a.clone(), b.clone()))
    }
    pub fn typ_equ(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Equ(a.clone(), b.clone()))
    }
    pub fn typ_add(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Add(a.clone(), b.clone()))
    }
    pub fn typ_sub(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Sub(a.clone(), b.clone()))
    }
    pub fn typ_mul(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Mul(a.clone(), b.clone()))
    }
    pub fn typ_div(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Div(a.clone(), b.clone()))
    }
    pub fn typ_pow(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Pow(a.clone(), b.clone()))
    }
    pub fn typ_rem(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Rem(a.clone(), b.clone()))
    }
    pub fn typ_dot(a: &CTyp, b: &CTyp) -> Self {
        LubError::Type(BinopError::Dot(a.clone(), b.clone()))
    }
}

/// Instances of this trait can be added, muliplied, divided, exp'd and dot product'd together, generating constraints and type errors
pub trait Lub where Self: Sized {
    type Context;
    fn lub_equ(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_add(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_sub(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_mul(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_div(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_pow(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_dot(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
    fn lub_rem(a: Self, b: Self, ctx: &Self::Context) -> Result<Self, LubError>;
}

/// Least-upper bounds for [Range] overapproximate sets of integers
impl Lub for Range<usize> {
    type Context = Nothing;
    fn lub_equ(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_equ(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_equ(&a, &b),
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

    fn lub_add(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_add(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_add(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a + b)
    }

    fn lub_sub(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_sub(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_sub(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a - b)
    }

    fn lub_mul(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_mul(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_mul(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a * b)
    }

    fn lub_div(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_div(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_div(&a, &b),
                    LubError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::Range(BinopError::Div(a, b))); // Division by zero is undefined
        }

        Ok(a / b)
    }

    fn lub_pow(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_pow(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_pow(&a, &b),
                    LubError::bad_range(&b, e)))?;

        Ok(a ^ b)
    }

    fn lub_rem(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        // Validate Ranges
        a.check().map_err(|e|
                LubError::next(
                    LubError::range_rem(&a, &b),
                    LubError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                LubError::next(
                    LubError::range_rem(&a, &b),
                    LubError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(LubError::Range(BinopError::Div(a, b))); // Division by zero is undefined
        }

        Ok(a % b)
    }

    fn lub_dot(a: Self, b: Self, _: &Nothing) -> Result<Self, LubError> {
        Self::lub_mul(a, b, &Nothing)
            .map_err(|e| LubError::next(LubError::range_dot(&a, &b), e))
    }
}

/// Least-upper bound of type variables
impl Lub for Tid {
    type Context = Ctx<Tid, Kind>;
    /// Can the two kinds be unified into one kind that describes both?
    fn lub_equ(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(
                    LubError::tid_equ(&a, &b),
                    LubError::kind_not_found(&a)))?;

        let kb = ctx.get(&b)
            .ok_or(LubError::next(
                    LubError::tid_equ(&a, &b),
                    LubError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a),
            (Kind::Group, Kind::Group) if a == b => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => Ok(a),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::tv_equ(&a, ka, &b, kb))
        }
    }

    /// Least-upper-bound for addition of different kinds
    fn lub_add(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(
                    LubError::tid_equ(&a, &b),
                    LubError::kind_not_found(&a)))?;

        let kb = ctx.get(&b)
            .ok_or(LubError::next(
                    LubError::tid_equ(&a, &b),
                    LubError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a),
            (Kind::Group, Kind::Group) if a == b => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => Ok(a),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::tv_add(&a, ka, &b, kb))
        }
    }

    /// Least-upper-bound for subtraction same as addition
    fn lub_sub(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(
                    LubError::tid_equ(&a, &b),
                    LubError::kind_not_found(&a)))?;

        let kb = ctx.get(&b)
            .ok_or(LubError::next(
                    LubError::tid_equ(&a, &b),
                    LubError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            (Kind::Group, Kind::Group) if a == b => Ok(a),
            (Kind::Pairing(g1, g2), Kind::Pairing(h1, h2)) if a == b && g1 == h1 && g2 == h2 => Ok(a),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::tv_sub(&a, ka, &b, kb))
        }
    }

    /// Least-upper-bound for multiplication of different kinds
    fn lub_mul(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(LubError::tid_mul(&a, &b), LubError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::next(LubError::tid_mul(&a, &b), LubError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Scalar multiplication: Scalar * Group = Group * Scalar = Group
            (Kind::Scalar(g), Kind::Group) if g == &b => Ok(b),
            (Kind::Group, Kind::Scalar(g)) if g == &a => Ok(a),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            // Group multiplication is only allowed for pairing friendly curves
            // G1 * G2 => Pairing(G1, G2)
            // forces G1: Group, G2: Group
            (Kind::Group, Kind::Group) =>
                if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(&a, &b)) {
                    Ok(pid.clone())
                } else {
                    Err(LubError::tv_mul(&a, ka, &b, kb))
                }
            (_, _) => Err(LubError::tv_mul(&a, ka, &b, kb))
        }
    }

    /// Least-upper-bound for division of different kinds
    fn lub_div(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(LubError::tid_div(&a, &b), LubError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::next(LubError::tid_div(&a, &b), LubError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) if a == b => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            (Kind::Group, Kind::Scalar(g)) if g == &a => Ok(a),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(LubError::tv_div(&a, ka, &b, kb))
        }
    }

    /// Least-upper-bound for remainder of different kinds
    fn lub_rem(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(LubError::tid_div(&a, &b), LubError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::next(LubError::tid_div(&a, &b), LubError::kind_not_found(&b)))?;
        Err(LubError::tv_rem(&a, ka, &b, kb))
    }

    /// Least-upper-bound for exponentiation of different kinds
    fn lub_pow(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        let ka = ctx.get(&a)
            .ok_or(LubError::next(LubError::tid_div(&a, &b), LubError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(LubError::next(LubError::tid_div(&a, &b), LubError::kind_not_found(&b)))?;
        Err(LubError::tv_pow(&a, ka, &b, kb))
    }

    /// Least-upper-bound for dot product is the same as multiplication (for kinds)
    fn lub_dot(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, LubError> {
        Self::lub_mul(a.clone(), b.clone(), ctx)
            .map_err(|e| LubError::next(LubError::tid_dot(&a, &b), e))
    }
}

impl Lub for CTyp {
    type Context = Ctx<Tid, Kind>;
    fn lub_equ(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_equ(&x, &y), e))?)),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_equ(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_equ(&x, &y), e))?)),
            // Uni<A> == Uni<B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_equ(&x, &y), e))?, n.max(m))),
            // Mle<A> == Mle<B>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_equ(&x, &y), e))?, n.max(m))),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_equ(&x, &y), e))?, n)),
            // Indices can act like finite fields
            (a, b) => {
                let ta = a.to_scalar(ctx).ok_or(LubError::typ_equ(&x, &y))?;
                let tb = b.to_scalar(ctx).ok_or(LubError::typ_equ(&x, &y))?;
                Ok(CTyp::Base(Tid::lub_equ(ta, tb, ctx)
                    .map_err(|e| LubError::next(LubError::typ_equ(&x, &y), e))?))
            }
        }
    }

    fn lub_add(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_add(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_add(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_add(&x, &y), e))?)),
            // Uni<A> + Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_add(&x, &y), e))?, n.max(m))),
            // Mle<A> + Mle<B> = Mle<max(A, B)>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Tid::lub_add(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_add(&x, &y), e))?, n.max(m))),
            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_add(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_add(&x, &y), e))?, n))
                } else {
                    Err(LubError::typ_add(&x, &y))
                },

            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(LubError::typ_add(&x, &y), LubError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::Base(a))
                } else {
                    Err(LubError::typ_add(&x, &y))
                }
            },
            (_, _) => Err(LubError::typ_add(&x, &y))
        }
    }

    fn lub_sub(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_sub(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_sub(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_sub(&x, &y), e))?)),
            // Uni<A> - Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_sub(&x, &y), e))?, n.max(m))),
            // Mle<A> - Mle<B> = Mle<max(A, B)>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_sub(&x, &y), e))?, n.max(m))),
            // Vec<A> - Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_sub(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_sub(&x, &y), e))?, n))
                } else {
                    Err(LubError::typ_sub(&x, &y))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(LubError::typ_sub(&x, &y), LubError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::Base(a))
                } else {
                    Err(LubError::typ_sub(&x, &y))
                }
            },
            (_, _) => Err(LubError::typ_sub(&x, &y))
        }
    }

    fn lub_mul(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_mul(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?)),
            // Uni<A> * Uni<B> = Uni<A + B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Tid::lub_sub(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?, n + m)),
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_mul(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?, n))
                } else {
                    Err(LubError::typ_mul(&x, &y))
                },
            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(CTyp::lub_mul(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?, n)),
            // Uni<A> * c = Uni<A> if c is a finite field
            (a, CTyp::Uni(b, n)) | (CTyp::Uni(b, n), a) => {
                let t = CTyp::lub_mul(a.clone(), CTyp::Base(b), ctx)
                    .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(LubError::typ_mul(&x, &y))
                }
            }
            // Mle<A> * c = Mle<A> if c is a finite field
            (a, CTyp::Mle(b, n)) | (CTyp::Mle(b, n), a) => {
                let t = CTyp::lub_mul(a.clone(), CTyp::Base(b), ctx)
                    .map_err(|e| LubError::next(LubError::typ_mul(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(LubError::typ_mul(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(LubError::typ_mul(&x, &y), LubError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::Base(a))
                } else {
                    Err(LubError::typ_mul(&x, &y))
                }
            },
            (_, _) => Err(LubError::typ_mul(&x, &y))
        }
    }

    fn lub_div(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_div(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?)),
            // Uni<A> / Uni<B> = Uni<A - B> if A > B
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) if n >= m =>
                Ok(CTyp::Uni(Tid::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?, n - m)),
            // Vec<A> / Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_div(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?, n))
                } else {
                    Err(LubError::typ_div(&x, &y))
                },
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(CTyp::lub_div(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?, n)),

            // Uni<A> / c = Uni<A> if c is a finite field
            (CTyp::Uni(b, n), a) => {
                let t = CTyp::lub_div(CTyp::Base(b), a.clone(), ctx)
                    .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(LubError::typ_div(&x, &y))
                }
            }
            // Mle<A> / c = Mle<A> if c is a finite field
            (CTyp::Mle(b, n), a) => {
                let t = CTyp::lub_div(CTyp::Base(b), a.clone(), ctx)
                    .map_err(|e| LubError::next(LubError::typ_div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(LubError::typ_div(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(
                            LubError::typ_div(&x, &y),
                            LubError::kind_not_found(&a)))?;
                if ka == &Kind::Field {
                    Ok(CTyp::Base(a))
                } else {
                    Err(LubError::typ_div(&x, &y))
                }
            },
            (_, _) => Err(LubError::typ_div(&x, &y))
        }
    }

    fn lub_rem(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Tid::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_rem(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_rem(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_rem(&x, &y), e))?)),
            // Uni<A> % Uni<B> = Uni<C> where deg(C) = deg(B) - 1
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) if n >= m =>
                Ok(CTyp::Uni(Tid::lub_equ(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_rem(&x, &y), e))?, m.saturating_sub(1))),
            // Vec<A> % Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_rem(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_rem(&x, &y), e))?, n))
                } else {
                    Err(LubError::typ_rem(&x, &y))
                },
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(CTyp::lub_rem(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_rem(&x, &y), e))?, n)),

            (_, _) => Err(LubError::typ_rem(&x, &y))
        }
    }

    fn lub_pow(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_pow(a, b, &Nothing)
                    .map_err(|e| LubError::next(LubError::typ_pow(&x, &y), e))?)),
            (CTyp::Base(a), CTyp::Fin(_)) => {
                let ka = ctx.get(&a)
                    .ok_or(LubError::next(
                            LubError::typ_pow(&x, &y),
                            LubError::kind_not_found(&a)))?;
                if ka.is_scalar() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(LubError::typ_pow(&x, &y))
                }
            },
            // Vec<A> ^ Vec<B> = Vec<C>
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_pow(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_pow(&x, &y), e))?, n))
                } else {
                    Err(LubError::typ_pow(&x, &y))
                },
            // Vec<B> ^ A = Vec<A^B>
            (CTyp::Vec(box a, n), b) =>
                Ok(CTyp::vec(CTyp::lub_pow(a, b, ctx)
                    .map_err(|e| LubError::next(LubError::typ_pow(&x, &y), e))?, n)),

            // Uni<B> ^ Fin<i..j> = Uni<B*j>
            (CTyp::Uni(a, n), CTyp::Fin(r)) =>
                Ok(CTyp::Uni(a, n * (r.end.saturating_sub(1)))),

            (_, _) => Err(LubError::typ_pow(&x, &y))
        }
    }

    fn lub_dot(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, LubError> {
        match (x.clone(), y.clone()) {
            // Vec<A> * Vec<B> = C
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    CTyp::lub_mul(a, b, ctx)
                        .map_err(|e| LubError::next(LubError::typ_dot(&x, &y), e))
                } else {
                    Err(LubError::typ_dot(&x, &y))
                },
            (a, b) => CTyp::lub_mul(a, b, ctx)
                .map_err(|e| LubError::next(LubError::typ_dot(&x, &y), e))
        }
    }
}

#[test]
fn lub_range() {
    let a = Range { start: 0, step: 1, end: 10 };
    let b = Range { start: 5, step: 1, end: 15 };

    assert_eq!(Range::lub_equ(a.clone(), b.clone(), &Nothing), Ok(Range { start: 0, step: 1, end: 15 }));
    assert_eq!(Range::lub_add(a.clone(), b.clone(), &Nothing), Ok(Range { start: 5, step: 1, end: 24 }));
    assert_eq!(Range::lub_sub(b.clone(), a.clone(), &Nothing), Ok(Range { start: 0, step: 1, end: 15 }));
    assert_eq!(Range::lub_mul(a.clone(), b.clone(), &Nothing), Ok(Range { start: 0, step: 1, end: 127 }));
    assert_eq!(Range::lub_div(b.clone(), Range { start: 1, step: 1, end: 15 }, &Nothing), Ok(Range { start: 0, step: 1, end: 15 }));
}

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
        (s1.clone(), Kind::Scalar(g1.clone())),
        (s2.clone(), Kind::Scalar(g2.clone())),
    ]);

    assert_eq!(Tid::lub_equ(f.clone(), f.clone(), &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_equ(g1.clone(), g1.clone(), &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_equ(s1.clone(), s1.clone(), &ctx), Ok(s1.clone()));
    assert!(Tid::lub_equ(g1.clone(), g2.clone(), &ctx).is_err());

    assert_eq!(Tid::lub_add(f.clone(), f.clone(), &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_add(s1.clone(), s1.clone(), &ctx), Ok(s1.clone()));
    assert_eq!(Tid::lub_add(g1.clone(), g1.clone(), &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_add(p.clone(), p.clone(), &ctx), Ok(p.clone()));
    assert!(Tid::lub_add(g1.clone(), g2.clone(), &ctx).is_err());

    assert_eq!(Tid::lub_sub(f.clone(), f.clone(), &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_sub(s1.clone(), s1.clone(), &ctx), Ok(s1.clone()));
    assert_eq!(Tid::lub_sub(g1.clone(), g1.clone(), &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_sub(p.clone(), p.clone(), &ctx), Ok(p.clone()));
    assert!(Tid::lub_sub(g1.clone(), g2.clone(), &ctx).is_err());

    assert_eq!(Tid::lub_mul(f.clone(), f.clone(), &ctx), Ok(f.clone()));
    assert!(Tid::lub_mul(g1.clone(), g1.clone(), &ctx).is_err());
    assert!(Tid::lub_mul(s1.clone(), s2.clone(), &ctx).is_err());
    assert_eq!(Tid::lub_mul(s1.clone(), s1.clone(), &ctx), Ok(s1.clone()));
    assert_eq!(Tid::lub_mul(s1.clone(), g1.clone(), &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_mul(g2.clone(), s2.clone(), &ctx), Ok(g2.clone()));

    assert_eq!(Tid::lub_div(f.clone(), f.clone(), &ctx), Ok(f.clone()));
    assert_eq!(Tid::lub_div(s1.clone(), s1.clone(), &ctx), Ok(s1.clone()));
    assert!(Tid::lub_div(s1.clone(), s2.clone(), &ctx).is_err());
    assert!(Tid::lub_div(g1.clone(), g1.clone(), &ctx).is_err());
    assert!(Tid::lub_div(g1.clone(), f.clone(), &ctx).is_err());
    assert_eq!(Tid::lub_div(g1.clone(), s1.clone(), &ctx), Ok(g1.clone()));
    assert_eq!(Tid::lub_div(g2.clone(), s2.clone(), &ctx), Ok(g2.clone()));
    assert!(Tid::lub_div(g1.clone(), s2.clone(), &ctx).is_err());
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
        (s1.clone(), Kind::Scalar(g1.clone())),
        (s2.clone(), Kind::Scalar(g2.clone())),
    ]);

    let tf = CTyp::Base(f.clone());
    let tg1 = CTyp::Base(g1.clone());
    let tg2 = CTyp::Base(g2.clone());
    let tp = CTyp::Base(p.clone());
    let ts1 = CTyp::Base(s1.clone());
    let ts2 = CTyp::Base(s2.clone());
    let tr = CTyp::Fin(Range::singleton(10));

    assert_eq!(CTyp::lub_equ(tf.clone(), tf.clone(), &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_equ(tg1.clone(), tg1.clone(), &ctx), Ok(tg1.clone()));
    assert!(CTyp::lub_equ(tg1.clone(), tg2.clone(), &ctx).is_err());
    assert_eq!(CTyp::lub_equ(ts1.clone(), ts1.clone(), &ctx), Ok(ts1.clone()));
    assert_eq!(CTyp::lub_equ(CTyp::vec(tf.clone(), 10), CTyp::vec(tf.clone(), 10), &ctx), Ok(CTyp::vec(tf.clone(), 10)));
    assert!(CTyp::lub_equ(CTyp::vec(tf.clone(), 10), CTyp::vec(tf.clone(), 11), &ctx).is_err());
    assert!(CTyp::lub_equ(CTyp::vec(tf.clone(), 10), CTyp::vec(tg1.clone(), 10), &ctx).is_err());
    assert_eq!(CTyp::lub_equ(CTyp::uni(f.clone(), 10), CTyp::uni(f.clone(), 11), &ctx), Ok(CTyp::uni(f.clone(), 11)));

    assert_eq!(CTyp::lub_add(tf.clone(), tf.clone(), &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_add(tg1.clone(), tg1.clone(), &ctx), Ok(tg1.clone()));
    assert!(CTyp::lub_add(tg1.clone(), tg2.clone(), &ctx).is_err());
    assert_eq!(CTyp::lub_add(ts1.clone(), ts1.clone(), &ctx), Ok(ts1.clone()));
    assert!(CTyp::lub_add(ts1.clone(), ts2.clone(), &ctx).is_err());
    assert_eq!(CTyp::lub_add(tp.clone(), tp.clone(), &ctx), Ok(tp.clone()));
    assert!(CTyp::lub_add(tp.clone(), tg1.clone(), &ctx).is_err());
    assert!(CTyp::lub_add(CTyp::vec(tf.clone(), 10), CTyp::vec(tf.clone(), 11), &ctx).is_err());
    assert_eq!(CTyp::lub_add(CTyp::vec(tf.clone(), 10), CTyp::vec(tf.clone(), 10), &ctx), Ok(CTyp::vec(tf.clone(), 10)));
    assert_eq!(CTyp::lub_add(CTyp::uni(f.clone(), 10), CTyp::uni(f.clone(), 11), &ctx), Ok(CTyp::uni(f.clone(), 11)));
    assert_eq!(CTyp::lub_add(CTyp::mle(f.clone(), 10), CTyp::mle(f.clone(), 11), &ctx), Ok(CTyp::mle(f.clone(), 11)));
    assert_eq!(CTyp::lub_add(CTyp::vec(tg1.clone(), 10), CTyp::vec(tg1.clone(), 10), &ctx), Ok(CTyp::vec(tg1.clone(), 10)));

    assert_eq!(CTyp::lub_pow(tf.clone(), tr.clone(), &ctx), Ok(tf.clone()));
    assert_eq!(CTyp::lub_pow(CTyp::vec(tf.clone(), 10), tr.clone(), &ctx), Ok(CTyp::vec(tf.clone(), 10)));
    assert_eq!(CTyp::lub_pow(CTyp::uni(f.clone(), 10), tr.clone(), &ctx), Ok(CTyp::uni(f.clone(), 100)));
    assert!(CTyp::lub_pow(CTyp::mle(f.clone(), 10), tr.clone(), &ctx).is_err());
}


