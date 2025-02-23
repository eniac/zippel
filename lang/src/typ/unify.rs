use crate::typ::{Kind, CTyp, TypeVar, AliasSubsts};
use crate::range::{Range, RangeError};
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
    #[error("Cannot take dot-product of {0} . {1}")]
    Dot(K, K),
}

#[derive(Error, PartialEq, Debug)]
pub enum UnifyError {
    #[error("{0}\n\n{1}")]
    Next(Box<UnifyError>, Box<UnifyError>),
    #[error("UnificationError: During binary operation typechecking type variables\n\n{0}")]
    Kind(#[from] BinopError<TypeVar>),
    #[error("UnificationError: During binary operation typechecking type identifiers\n\n{0}")]
    Tid(#[from] BinopError<Tid>),
    #[error("UnificationError: During binary operation typechecking ranges\n\n{0}")]
    Range(#[from] BinopError<Range<usize>>),
    #[error("UnificationError: During binary operation typechecking types\n\n{0}")]
    Type(#[from] BinopError<CTyp>),
    #[error("UnificationError: Malformed range error {0}\n\n{1}")]
    BadRange(Range<usize>, RangeError),
    #[error("Kind {0} not found")]
    KindNotFound(Tid),
}

impl UnifyError {
    pub fn kind_not_found(id: &Tid) -> Self {
        UnifyError::KindNotFound(id.clone())
    }
    pub fn next(a: UnifyError, b: UnifyError) -> Self {
        UnifyError::Next(Box::new(a), Box::new(b))
    }
    pub fn bad_range(r: &Range<usize>, e: RangeError) -> Self {
        UnifyError::BadRange(r.clone(), e)
    }
    pub fn tv_equ(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Equ(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_add(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Add(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_sub(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Sub(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_mul(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Mul(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_div(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Div(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_pow(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Pow(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tv_dot(a: &Tid, ka: &Kind, b: &Tid, kb: &Kind) -> Self {
        UnifyError::Kind(BinopError::Dot(
                TypeVar { id: a.clone(), kind: ka.clone() },
                TypeVar { id: b.clone(), kind: kb.clone() }))
    }
    pub fn tid_equ(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Equ(a.clone(), b.clone()))
    }
    pub fn tid_add(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Add(a.clone(), b.clone()))
    }
    pub fn tid_sub(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Sub(a.clone(), b.clone()))
    }
    pub fn tid_mul(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Mul(a.clone(), b.clone()))
    }
    pub fn tid_div(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Div(a.clone(), b.clone()))
    }
    pub fn tid_pow(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Pow(a.clone(), b.clone()))
    }
    pub fn tid_dot(a: &Tid, b: &Tid) -> Self {
        UnifyError::Tid(BinopError::Dot(a.clone(), b.clone()))
    }
    pub fn range_equ(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Equ(a.clone(), b.clone()))
    }
    pub fn range_add(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Add(a.clone(), b.clone()))
    }
    pub fn range_sub(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Sub(a.clone(), b.clone()))
    }
    pub fn range_mul(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Mul(a.clone(), b.clone()))
    }
    pub fn range_dot(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Dot(a.clone(), b.clone()))
    }
    pub fn range_div(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Div(a.clone(), b.clone()))
    }
    pub fn range_pow(a: &Range<usize>, b: &Range<usize>) -> Self {
        UnifyError::Range(BinopError::Pow(a.clone(), b.clone()))
    }
    pub fn typ_equ(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Equ(a.clone(), b.clone()))
    }
    pub fn typ_add(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Add(a.clone(), b.clone()))
    }
    pub fn typ_sub(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Sub(a.clone(), b.clone()))
    }
    pub fn typ_mul(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Mul(a.clone(), b.clone()))
    }
    pub fn typ_div(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Div(a.clone(), b.clone()))
    }
    pub fn typ_pow(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Pow(a.clone(), b.clone()))
    }
    pub fn typ_dot(a: &CTyp, b: &CTyp) -> Self {
        UnifyError::Type(BinopError::Dot(a.clone(), b.clone()))
    }
}

/// Instances of this trait can be added, muliplied, divided, exp'd and dot product'd together, generating constraints and type errors
pub trait Unify where Self: Sized {
    fn unify_equ(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
    fn unify_add(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
    fn unify_sub(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
    fn unify_mul(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
    fn unify_div(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
    fn unify_pow(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
    fn unify_dot(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError>;
}

/// Least-upper bounds for [Range] overapproximate sets of integers
impl Unify for Range<usize> {
    fn unify_equ(a: Self, b: Self, _: &Ctx<Tid, Kind>, _: &mut AliasSubsts) -> Result<Self, UnifyError> {
        // Validate ranges
        a.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_equ(&a, &b),
                    UnifyError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_equ(&a, &b),
                    UnifyError::bad_range(&b, e)))?;

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

    fn unify_add(a: Self, b: Self, _: &Ctx<Tid, Kind>, _: &mut AliasSubsts) -> Result<Self, UnifyError> {
        // Validate ranges
        a.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_add(&a, &b),
                    UnifyError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_add(&a, &b),
                    UnifyError::bad_range(&b, e)))?;

        // Compute new start, end and step
        let new_start = a.start + b.start;
        let new_end = (a.end - a.step) + (b.end - b.step) + 1;
        let new_step = num::integer::gcd(a.step, b.step);

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn unify_sub(a: Self, b: Self, _: &Ctx<Tid, Kind>, _: &mut AliasSubsts) -> Result<Self, UnifyError> {
        // Validate ranges
        a.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_sub(&a, &b),
                    UnifyError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_sub(&a, &b),
                    UnifyError::bad_range(&b, e)))?;

        // Compute new start, end and step
        let new_start = a.start.saturating_sub(b.end - b.step); // Use saturating_sub to avoid underflow
        let new_end = (a.end - a.step) - b.start + 1;
        let new_step = num::integer::gcd(a.step, b.step);

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn unify_mul(a: Self, b: Self, _: &Ctx<Tid, Kind>, _: &mut AliasSubsts) -> Result<Self, UnifyError> {
        // Validate ranges
        a.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_mul(&a, &b),
                    UnifyError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_mul(&a, &b),
                    UnifyError::bad_range(&b, e)))?;

        let a_min = a.start;
        let a_max = a.end - a.step;
        let b_min = b.start;
        let b_max = b.end - b.step;

        // Compute all possible products
        let p1 = a_min * b_min;
        let p2 = a_min * b_max;
        let p3 = a_max * b_min;
        let p4 = a_max * b_max;

        // Compute new start and end
        let new_start = p1.min(p2).min(p3).min(p4);
        let new_end = p1.max(p2).max(p3).max(p4) + 1;

        // Compute new step
        let new_step = num::integer::gcd(a.step * b.step, num::integer::gcd(a.step * b.start, b.step * a.start));

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn unify_div(a: Self, b: Self, _: &Ctx<Tid, Kind>, _: &mut AliasSubsts) -> Result<Self, UnifyError> {
        // Validate Ranges
        a.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_div(&a, &b),
                    UnifyError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_div(&a, &b),
                    UnifyError::bad_range(&b, e)))?;

        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(UnifyError::Range(BinopError::Div(a, b))); // Division by zero is undefined
        }

        let a_min = a.start;
        let a_max = a.end - a.step;
        let b_min = b.start;
        let b_max = b.end - b.step;

        // Compute new start and end
        let new_start = a_min / b_max; // Smallest quotient
        let new_end = a_max / b_min + 1; // Largest quotient + 1 (right-exclusive)

        // Use a step of 1 for safe overapproximation
        let new_step = 1;

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn unify_pow(a: Self, b: Self, _: &Ctx<Tid, Kind>, _: &mut AliasSubsts) -> Result<Self, UnifyError> {
        // Validate Ranges
        a.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_pow(&a, &b),
                    UnifyError::bad_range(&a, e)))?;
        b.check().map_err(|e|
                UnifyError::next(
                    UnifyError::range_pow(&a, &b),
                    UnifyError::bad_range(&b, e)))?;

        let a_min = a.start;
        let a_max = a.end - a.step;
        let b_min = b.start;
        let b_max = b.end - b.step;

        // Compute new start and end
        let new_start = a_min.pow(b_min as u32); // Smallest power
        let new_end = a_max.pow(b_max as u32) + 1; // Largest power + 1 (right-exclusive)

        // Use a step of 1 for safe overapproximation
        let new_step = 1;

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn unify_dot(a: Self, b: Self, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        Self::unify_mul(a, b, ctx, subs)
            .map_err(|e| UnifyError::next(UnifyError::range_dot(&a, &b), e))
    }
}

/// Least-upper bound of type variables
impl Unify for Tid {

    /// Can the two kinds be unified into one kind that describes both?
    fn unify_equ(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        let ka = ctx.get(&a)
            .ok_or(UnifyError::next(
                    UnifyError::tid_equ(&a, &b),
                    UnifyError::kind_not_found(&a)))?;

        let kb = ctx.get(&b)
            .ok_or(UnifyError::next(
                    UnifyError::tid_equ(&a, &b),
                    UnifyError::kind_not_found(&b)))?;

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
            (Kind::Group, Kind::Group) => Ok(subs.add_equ(&a, &b)),
            (Kind::Pairing(k1, k2), Kind::Pairing(k3, k4)) => {
                subs.add_equ(k1, k3);
                subs.add_equ(k2, k4);
                Ok(subs.add_equ(&a, &b))
            },
            // Ranges in kinds should be concretized already, if not its a bug
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(UnifyError::tv_equ(&a, &ka, &b, &kb))
        }
    }

    /// Type inference for addition of different kinds
    fn unify_add(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        Self::unify_equ(a.clone(), b.clone(), ctx, subs)
            .map_err(|e| UnifyError::next(UnifyError::tid_add(&a, &b), e))
    }

    /// Type inference for subtraction same as addition
    fn unify_sub(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        Self::unify_equ(a.clone(), b.clone(), ctx, subs)
            .map_err(|e| UnifyError::next(UnifyError::tid_sub(&a, &b), e))
    }

    /// Type inference for multiplication of different kinds
    fn unify_mul(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        let ka = ctx.get(&a)
            .ok_or(UnifyError::next(UnifyError::tid_mul(&a, &b), UnifyError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(UnifyError::next(UnifyError::tid_mul(&a, &b), UnifyError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(subs.add_equ(&a, &b)),
            (Kind::Scalar(g1), Kind::Scalar(g2)) => {
                subs.add_equ(g1, g2);
                Ok(subs.add_equ(&a, &b))
            },
            // Scalar multiplication: Scalar * Group = Group
            (Kind::Scalar(g1), Kind::Group) => Ok(subs.add_equ(&g1, &b)),
            (Kind::Group, Kind::Scalar(g2)) => Ok(subs.add_equ(&g2, &a)),
            (Kind::Multiplicative(f1), Kind::Field) => Ok(subs.add_equ(&f1, &b)),
            (Kind::Field, Kind::Multiplicative(f2)) => Ok(subs.add_equ(&a, &f2)),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            // Group multiplication is only allowed for pairing friendly curves
            // G1 * G2 => Pairing(G1, G2)
            // forces G1: Group, G2: Group
            (Kind::Group, Kind::Group) =>
                if let Some((pid, _)) = ctx.find(|_, k| k.is_pairing(&a, &b)) {
                    Ok(pid.clone())
                } else {
                    Err(UnifyError::tv_mul(&a, ka, &b, kb))
                }
            (_, _) => Err(UnifyError::tv_mul(&a, ka, &b, kb))
        }
    }

    /// Type inference for division of different kinds
    fn unify_div(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        let ka = ctx.get(&a)
            .ok_or(UnifyError::next(UnifyError::tid_div(&a, &b), UnifyError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(UnifyError::next(UnifyError::tid_div(&a, &b), UnifyError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(subs.add_equ(&a, &b)),
            (Kind::Scalar(g1), Kind::Scalar(g2)) => {
                subs.add_equ(g1, g2);
                Ok(subs.add_equ(&a, &b))
            },
            // Group / Scalar = Group
            (Kind::Group, Kind::Scalar(g)) => Ok(subs.add_equ(&a, g)),
            (Kind::Multiplicative(f), Kind::Field) => Ok(subs.add_equ(f, &b)),
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(UnifyError::tv_div(&a, ka, &b, kb))
        }
    }

    /// Type inference for exponentiation of different kinds
    fn unify_pow(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        let ka = ctx.get(&a)
            .ok_or(UnifyError::next(UnifyError::tid_pow(&a, &b), UnifyError::kind_not_found(&a)))?;
        let kb = ctx.get(&b)
            .ok_or(UnifyError::next(UnifyError::tid_pow(&a, &b), UnifyError::kind_not_found(&b)))?;

        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(subs.add_equ(&a, &b)),
            (Kind::Scalar(g1), Kind::Scalar(g2)) => {
                subs.add_equ(g1, g2);
                Ok(subs.add_equ(&a, &b))
            },
            // Range kinds should be substituted at this point
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) => Err(UnifyError::tv_pow(&a, ka, &b, kb))
        }
    }
    /// Type inference for dot product is the same as multiplication (for kinds)
    fn unify_dot(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Tid, UnifyError> {
        Self::unify_mul(a.clone(), b.clone(), ctx, subs)
            .map_err(|e| UnifyError::next(UnifyError::tid_dot(&a, &b), e))
    }
}

impl Unify for CTyp {
    fn unify_equ(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?)),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?)),
            // Uni<A> == Uni<B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Unify::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?, n.max(m))),
            // Mle<A> == Mle<B>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Unify::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?, n.max(m))),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?, n)),
            // Finite fields can act like 0 degree polynomals
            (CTyp::Uni(a, n), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Uni(a, n)) =>
                Ok(CTyp::Uni(Unify::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?, n)),
            // Finite fields can act like 0 variable MLEs
            (CTyp::Mle(a, n), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Mle(a, n)) =>
                Ok(CTyp::Mle(Unify::unify_equ(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_equ(&x, &y), e))?, n)),
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(UnifyError::typ_equ(&x, &y), UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_equ(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_equ(&x, &y))
        }
    }

    fn unify_add(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_add(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::unify_add(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?)),
            // Uni<A> + Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Unify::unify_add(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?, n.max(m))),
            // Mle<A> + Mle<B> = Mle<max(A, B)>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Unify::unify_add(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?, n.max(m))),
            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::unify_add(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?, n)),
            // Uni<A> + c = Uni<                },A> if c is a finite field
            (a, CTyp::Uni(b, n)) | (CTyp::Uni(b, n), a) => {
                let t = CTyp::unify_add(a.clone(), CTyp::Base(b), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(UnifyError::typ_add(&x, &y))
                }
            }
            // Mle<A> + c = Mle<A> if c is a finite field
            (a, CTyp::Mle(b, n)) | (CTyp::Mle(b, n), a) => {
                let t = CTyp::unify_add(a.clone(), CTyp::Base(b), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_add(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(UnifyError::typ_add(&x, &y))
                }
            }

            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(UnifyError::typ_add(&x, &y), UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_add(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_add(&x, &y))
        }
    }

    fn unify_sub(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?)),
            // Uni<A> - Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Unify::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?, n.max(m))),
            // Mle<A> - Mle<B> = Mle<max(A, B)>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Unify::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?, n.max(m))),
            // Vec<A> - Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?, n)),

            // Uni<A> - c = Uni<A> if c is a finite field
            (CTyp::Uni(b, n), a) => {
                let t = CTyp::unify_sub(CTyp::Base(b), a.clone(), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(UnifyError::typ_sub(&x, &y))
                }
            }

            // Mle<A> - c = Mle<A> if c is a finite field
            (CTyp::Mle(b, n), a) => {
                let t = CTyp::unify_sub(CTyp::Base(b), a.clone(), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_sub(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(UnifyError::typ_sub(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(UnifyError::typ_sub(&x, &y), UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_sub(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_sub(&x, &y))
        }
    }

    fn unify_mul(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_mul(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::unify_mul(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?)),
            // Uni<A> * Uni<B> = Uni<A + B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Unify::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?, n + m)),
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::unify_mul(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?, n)),

            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(Unify::unify_mul(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?, n)),
            // Uni<A> * c = Uni<A> if c is a finite field
            (a, CTyp::Uni(b, n)) | (CTyp::Uni(b, n), a) => {
                let t = CTyp::unify_mul(a.clone(), CTyp::Base(b), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(UnifyError::typ_mul(&x, &y))
                }
            }
            // Mle<A> * c = Mle<A> if c is a finite field
            (a, CTyp::Mle(b, n)) | (CTyp::Mle(b, n), a) => {
                let t = CTyp::unify_mul(a.clone(), CTyp::Base(b), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_mul(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(UnifyError::typ_mul(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(UnifyError::typ_mul(&x, &y), UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_mul(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_mul(&x, &y))
        }
    }

    fn unify_div(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_div(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::unify_div(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?)),
            // Uni<A> / Uni<B> = Uni<A - B> if A > B
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) if n >= m =>
                Ok(CTyp::Uni(Unify::unify_div(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?, n - m)),
            // Vec<A> / Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                Ok(CTyp::vec(CTyp::unify_div(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?, n)),
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(CTyp::unify_div(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?, n)),

            // Uni<A> / c = Uni<A> if c is a finite field
            (CTyp::Uni(b, n), a) => {
                let t = CTyp::unify_div(CTyp::Base(b), a.clone(), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(UnifyError::typ_div(&x, &y))
                }
            }
            // Mle<A> / c = Mle<A> if c is a finite field
            (CTyp::Mle(b, n), a) => {
                let t = CTyp::unify_div(CTyp::Base(b), a.clone(), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_div(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(UnifyError::typ_div(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(
                            UnifyError::typ_div(&x, &y),
                            UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_div(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_div(&x, &y))
        }
    }

    fn unify_pow(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_pow(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_pow(&x, &y), e))?)),
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(
                            UnifyError::typ_pow(&x, &y),
                            UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_pow(&x, &y))
                }
            },

            // Vec<B> ^ A = Vec<B>
            (CTyp::Vec(box a, n), b) =>
                Ok(CTyp::vec(CTyp::unify_pow(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_pow(&x, &y), e))?, n)),

            // Uni<B> ^ Fin<i..j> = Uni<B*j>
            (CTyp::Uni(a, n), CTyp::Fin(r)) =>
                Ok(CTyp::Uni(a, n * r.end)),

            (_, _) => Err(UnifyError::typ_pow(&x, &y))
        }
    }

    fn unify_dot(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>, subs: &mut AliasSubsts) -> Result<Self, UnifyError> {
        match (x.clone(), y.clone()) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Unify::unify_dot(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e))?)),
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::unify_dot(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e))?)),
            // Uni<A> * Uni<B> = Uni<A + B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Unify::unify_sub(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e))?, n + m)),

            // Vec<A> * Vec<B> = C
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                CTyp::unify_dot(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e)),

            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::vec(Unify::unify_dot(a, b, ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e))?, n)),

            // Uni<A> * c = Uni<A> if c is a finite field
            (a, CTyp::Uni(b, n)) | (CTyp::Uni(b, n), a) => {
                let t = CTyp::unify_dot(a.clone(), CTyp::Base(b), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(UnifyError::typ_dot(&x, &y))
                }
            }
            // Mle<A> * c = Mle<A> if c is a finite field
            (a, CTyp::Mle(b, n)) | (CTyp::Mle(b, n), a) => {
                let t = CTyp::unify_dot(a.clone(), CTyp::Base(b), ctx, subs)
                    .map_err(|e| UnifyError::next(UnifyError::typ_dot(&x, &y), e))?;
                if let CTyp::Base(c) = t {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(UnifyError::typ_dot(&x, &y))
                }
            }
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Fin(_)) | (CTyp::Fin(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a)
                    .ok_or(UnifyError::next(UnifyError::typ_dot(&x, &y), UnifyError::kind_not_found(&a)))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(UnifyError::typ_dot(&x, &y))
                }
            },
            (_, _) => Err(UnifyError::typ_dot(&x, &y))
        }
    }
}
