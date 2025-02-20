use crate::typ::{Kind, CTyp, TypeVar};
use crate::range::Range;
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

#[derive(Error, PartialEq, Eq, Debug)]
pub enum ArithmeticTypeError {
    #[error("ArithmeticKindError: {0}")]
    Kind(#[from] BinopError<TypeVar>),
    #[error("Kind {0} not found in context {1}")]
    KindNotFound(Tid, Ctx<Tid, Kind>),
    #[error("ArithmeticContainerError: {0}")]
    Container(#[from] BinopError<CTyp>),
}

/// Instances of this trait can be added, muliplied, divided, exp'd and dot product'd together, generating constraints and type errors
pub trait Lub where Self: Sized {
    type Term;
    fn lub_equ(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
    fn lub_add(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
    fn lub_sub(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
    fn lub_mul(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
    fn lub_div(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
    fn lub_pow(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
    fn lub_dot(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError>;
}

/// Least-upper bounds for [Range] overapproximate sets of integers
impl Lub for Range<usize> {
    type Term = Range<usize>;
    fn lub_equ(r1: Self::Term, r2: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        // Find the maximum of the starts and minimum of the ends
        let max_start = std::cmp::max(r1.start, r2.start);
        let min_end = std::cmp::min(r1.end, r2.end);

        // Check if there's an overlap
        if max_start >= min_end {
            return Err(BinopError::Equ(r1, r2));
        }

        // Determine the step for the intersection. If one range's step is a multiple of the other,
        // use the larger step; otherwise, find the least common multiple (LCM) of the steps.
        let step = if r1.step % r2.step == 0 {
            r1.step
        } else if r2.step % r1.step == 0 {
            r2.step
        } else {
            // LCM calculation for when steps are not multiples of each other
            let gcd = num::integer::gcd(r1.step.abs(), r2.step.abs());
            (r1.step.abs() * r2.step.abs()) / gcd
        };

        // Ensure the intersection start aligns with the new step
        let adjusted_start = if (max_start - r1.start) % step != 0 {
            max_start + (step - (max_start - r1.start) % step)
        } else {
            max_start
        };

        // If the adjusted start goes beyond the end, there's no valid intersection
        if adjusted_start >= min_end {
            Err(BinopError::Equ(r1, r2))
        } else {
            Ok(Range {
                start: adjusted_start,
                step,
                end: min_end,
            })
        }
    }

    fn lub_add(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        let new_start = a.start + b.start;
        let new_end = (a.end - a.step) + (b.end - b.step) + 1;
        let new_step = num::integer::gcd(a.step, b.step);

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn lub_sub(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        let new_start = a.start.saturating_sub(b.end - b.step); // Use saturating_sub to avoid underflow
        let new_end = (a.end - a.step) - b.start + 1;
        let new_step = num::integer::gcd(a.step, b.step);

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn lub_mul(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
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

    fn lub_div(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        // Check if the divisor range includes zero
        if b.start == 0 {
            return Err(ArithmeticTypeError::DivError(a, b)); // Division by zero is undefined
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

    fn lub_pow(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {

        let a_min = a.start;
        let a_max = a.end - a.step;
        let b_min = b.start;
        let b_max = b.end - b.step;

        // Compute new start and end
        let new_start = a_min.pow(b_min); // Smallest power
        let new_end = a_max.pow(b_max) + 1; // Largest power + 1 (right-exclusive)

        // Use a step of 1 for safe overapproximation
        let new_step = 1;

        Ok(Range {
            start: new_start,
            step: new_step,
            end: new_end,
        })
    }

    fn lub_dot(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        Self::lub_mul(a, b, ctx)
    }
}

/// Least-upper bound of kinds
impl Lub for Kind {
    type Term = Tid;

    /// Can the two kinds be unified into one kind that describes both?
    fn lub_equ(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(b, ctx.clone()))?;
        match (ka, kb) {
            // Both kinds are defined
            (Kind::Field, Kind::Field) => Ok(a),
            (Kind::Scalar(x), Kind::Scalar(y)) if x == y => Ok(a),
            (Kind::Multiplicative(x), Kind::Multiplicative(y)) if x == y => Ok(a),
            (Kind::Group, Kind::Group) => Ok(a),
            (Kind::Pairing(k1, k2), Kind::Pairing(k3, k4)) if k1 == k3 && k2 == k4 => Ok(a),
            // Ranges in kinds should be concretized already, if not its a bug
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) =>
                Err(ArithmeticTypeError::Kind(BinopError::Add(
                            TypeVar::new(a, ka),
                            TypeVar::new(b, kb)))),
        }
    }

    /// Type inference for addition of different kinds
    fn lub_add(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        Self::lub_equ(a, b, ctx)
    }

    /// Type inference for subtraction same as addition
    fn lub_sub(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        Self::lub_equ(a, b, ctx)
    }

    /// Type inference for multiplication of different kinds
    fn lub_mul(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(b, ctx.clone()))?;
        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Scalar multiplication: Scalar * Group = Group
            (_, Kind::Scalar(g)) if g == a && ka.is_group() => Ok(a),
            (Kind::Scalar(g), _) if g == b && kb.is_group() => Ok(b),
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            // Group multiplication is only allowed for pairing friendly curves
            // G1 * G2 => Pairing(G1, G2)
            // forces G1: Group, G2: Group
            (_, _) =>
                if ka.is_group() && kb.is_group() {
                    if let Some((pid, _)) = ctx.find(|pid, k| k == &Kind::Pairing(a, b)) {
                        Ok(pid.clone())
                    } else {
                        Err(ArithmeticTypeError::Kind(BinopError::Mul(
                                TypeVar::new(a, ka),
                                TypeVar::new(b, kb))))
                    }
                } else {
                    Err(ArithmeticTypeError::Kind(BinopError::Mul(
                            TypeVar::new(a, ka),
                            TypeVar::new(b, kb))))
                }
        }
    }

    /// Type inference for division of different kinds
    fn lub_div(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(b, ctx.clone()))?;
        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Group / Scalar = Group
            (Kind::Scalar(g), k2) if g == b && k2.is_group() => Ok(b),
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) =>
                Err(ArithmeticTypeError::Kind(BinopError::Div(TypeVar::new(a, ka), TypeVar::new(b, kb)))),
        }
    }

    /// Type inference for exponentiation of different kinds
    fn lub_pow(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(b, ctx.clone()))?;
        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Group ^ Scalar = Group
            (_, Kind::Scalar(g)) if ka.is_group() => Ok(a),
            (Kind::Range(_), _) | (_, Kind::Range(_)) => unreachable!(),
            (_, _) =>
                Err(ArithmeticTypeError::Kind(BinopError::Pow(TypeVar::new(a, ka), TypeVar::new(b, kb)))),
        }
    }
    /// Type inference for dot product is the same as multiplication (for kinds)
    fn lub_dot(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Kind, ArithmeticTypeError> {
        Self::lub_mul(a, b, ctx)
    }
}

impl Lub for CTyp {
    type Term = CTyp;
    fn lub_equ(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Kind::lub_equ(a, b, ctx))),
            // Fin<A..B> == Fin<C..D>
            (CTyp::Fin(a), CTyp::Fin(b)) =>
                Ok(CTyp::Fin(Range::lub_equ(a, b, ctx)?)),
            // Uni<A> == Uni<B>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Kind::lub_equ(a, b, ctx)?, n.max(m))),
            // Mle<A> == Mle<B>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Kind::lub_equ(a, b, ctx)?, n.max(m))),
            // [A; N] == [B; M]
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_equ(a, b, ctx)?, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Equ(x, y)))
                },
            // Finite fields can act like 0 degree polynomals
            (CTyp::Uni(a, n), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Uni(a, n)) =>
                Ok(CTyp::Uni(Kind::lub_equ(a, b, ctx)?, n)),
            // Finite fields can act like 0 variable MLEs
            (CTyp::Mle(a, n), CTyp::Base(b)) | (CTyp::Base(b), CTyp::Mle(a, n)) =>
                Ok(CTyp::Mle(Kind::lub_equ(a, b, ctx)?, n)),
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Index(_)) | (CTyp::Index(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Equ(x, y)))
                }
            },
            (_, _) => Err(ArithmeticTypeError::Container(BinopError::Add(x, y)))
        }
    }

    fn lub_add(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Kind::lub_add(a, b, ctx)?)),
            (CTyp::Index(a), CTyp::Index(b)) =>
                Ok(CTyp::Index(Range::lub_add(a, b, ctx)?)),
            // Uni<A> + Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Kind::lub_add(a, b, ctx)?, n.max(m))),
            // Mle<A> + Mle<B> = Mle<max(A, B)>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Kind::lub_add(a, b, ctx)?, n.max(m))),

            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_add(a, b, ctx)?, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(x, y)))
                },
            // Uni<A> + c = Uni<A> if c is a finite field
            (a, CTyp::Uni(b, n)) | (CTyp::Uni(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_add(a.clone(), CTyp::base(&b), ctx)? {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(x, y)))
                },
            // Mle<A> + c = Mle<A> if c is a finite field
            (a, CTyp::Mle(b, n)) | (CTyp::Mle(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_add(a.clone(), CTyp::base(&b), ctx)? {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(x, y)))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Index(_)) | (CTyp::Index(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(x, y)))
                }
            },
            (_, _) => Err(ArithmeticTypeError::Container(BinopError::Add(x, y)))
        }
    }

    fn lub_sub(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Kind::lub_sub(a, b, ctx)?)),
            (CTyp::Index(a), CTyp::Index(b)) =>
                Ok(CTyp::Index(Range::lub_sub(a, b, ctx)?)),
            // Uni<A> - Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Kind::lub_sub(a, b, ctx)?, n.max(m))),
            // Mle<A> - Mle<B> = Mle<max(A, B)>
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Ok(CTyp::Mle(Kind::lub_sub(a, b, ctx)?, n.max(m))),
            // Vec<A> - Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_sub(a, b, ctx)?, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(x, y)))
                },
            // Uni<A> - c = Uni<A> if c is a finite field
            (CTyp::Uni(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_sub(CTyp::base(&b), a, ctx)? {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(x, y)))
                },
            // Mle<A> - c = Mle<A> if c is a finite field
            (CTyp::Mle(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_sub(CTyp::base(&b), a, ctx)? {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(x, y)))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Index(_)) | (CTyp::Index(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(x, y)))
                }
            },
            (_, _) => Err(ArithmeticTypeError::Container(BinopError::Sub(x, y)))
        }
    }

    fn lub_mul(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Kind::lub_mul(a, b, ctx)?)),
            (CTyp::Index(a), CTyp::Index(b)) =>
                Ok(CTyp::Index(Range::lub_mul(a, b, ctx)?)),
            // Uni<A> * Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Kind::lub_sub(a, b, ctx)?, n + m)),
            // Mle<A> * Mle<B> = error!
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Err(ArithmeticTypeError::Container(BinopError::Mul(x, y))),
            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_mul(a, b, ctx)?, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Mul(x, y)))
                },
            // Vec<A> * c = Vec<A>
            (a, CTyp::Vec(box b, n)) | (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::Vec(CTyp::lub_mul(a, b, ctx)?, n)),
            // Uni<A> * c = Uni<A> if c is a finite field
            (a, CTyp::Uni(b, n)) | (CTyp::Uni(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_mul(a.clone(), CTyp::base(&b), ctx)? {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Mul(x, y)))
                },
            // Mle<A> * c = Mle<A> if c is a finite field
            (a, CTyp::Mle(b, n)) | (CTyp::Mle(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_mul(a.clone(), CTyp::base(&b), ctx)? {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Mul(x, y)))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Index(_)) | (CTyp::Index(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Mul(x, y)))
                }
            },
            (_, _) => Err(ArithmeticTypeError::Container(BinopError::Mul(x, y)))
        }
    }

    fn lub_div(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Kind::lub_div(a, b, ctx)?)),
            (CTyp::Index(a), CTyp::Index(b)) =>
                Ok(CTyp::Index(Range::lub_div(a, b, ctx)?)),
            // Uni<A> * Uni<B> = Uni<max(A, B)>
            (CTyp::Uni(a, n), CTyp::Uni(b, m)) =>
                Ok(CTyp::Uni(Kind::lub_div(a, b, ctx)?, n - m)),
            // Mle<A> / Mle<B> = error!
            (CTyp::Mle(a, n), CTyp::Mle(b, m)) =>
                Err(ArithmeticTypeError::Container(BinopError::Mul(x, y))),
            // Vec<A> / Vec<B> = Vec<C> where C = A = B
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) =>
                if n == m {
                    Ok(CTyp::vec(CTyp::lub_div(a, b, ctx)?, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(x, y)))
                },
            // Vec<A> / c = Vec<A>
            (CTyp::Vec(box b, n), a) =>
                Ok(CTyp::Vec(CTyp::lub_div(a, b, ctx)?, n)),

            // Uni<A> / c = Uni<A> if c is a finite field
            (CTyp::Uni(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_div(CTyp::base(&b), a, ctx)? {
                    Ok(CTyp::Uni(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(x, y)))
                },
            // Mle<A> / c = Mle<A> if c is a finite field
            (CTyp::Mle(b, n), a) =>
                if let CTyp::Base(c) = CTyp::lub_div(CTyp::base(&b), a, ctx)? {
                    Ok(CTyp::Mle(c, n))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(x, y)))
                },
            // Indices can act like finite fields
            (CTyp::Base(a), CTyp::Index(_)) | (CTyp::Index(_), CTyp::Base(a)) => {
                let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(a, ctx.clone()))?;
                if ka.is_field() {
                    Ok(CTyp::Base(a))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(x, y)))
                }
            },
            (_, _) => Err(ArithmeticTypeError::Container(BinopError::Div(x, y)))
        }
    }

    fn lub_pow(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Base(a), CTyp::Base(b)) =>
                Ok(CTyp::Base(Kind::lub_pow(a, b, ctx)?)),
            (CTyp::Base(a), CTyp::Index(_)) => Ok(x),

            // Vec<B> ^ A = Vec<B>
            (CTyp::Vec(box a, n), b) =>
                Ok(CTyp::vec(&CTyp::lub_pow(a, b, ctx)?, &n)),

            // Uni<B> ^ Fin<i..j> = Uni<B*j>
            (CTyp::Uni(a, n), CTyp::Index(r)) =>
                Ok(CTyp::Uni(a, n * r.end)),

            (_, _) => Err(ArithmeticTypeError::Container(BinopError::Pow(x, y)))
        }
    }

    fn lub_dot(x: CTyp, y: CTyp, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (x, y) {
            (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m =>
                CTyp::lub_dot(a, b, ctx),
            (_, _) => CTyp::lub_mul(x, y, ctx)
                    .map_err(|_| ArithmeticTypeError::Container(BinopError::Dot(x.clone(), y.clone())))
        }
    }
}
