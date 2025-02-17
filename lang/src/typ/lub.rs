use crate::typ::{Kind, CTyp, TypeVar};
use crate::range::Range;
use crate::id::Tid;
use share::{Ctx, Set, Traversable1};

use std::fmt;
use thiserror::Error;


#[derive(Error, PartialEq, Eq, Debug)]
pub enum BinopError<K: fmt::Display> {
    #[error("Cannot take sum of types {0} + {1}")]
    Add(K, K),
    #[error("Cannot take difference of types {0} - {1}")]
    Sub(K, K),
    #[error("Cannot take product of types {0} * {1}")]
    Mul(K, K),
    #[error("Cannot take quotient of types {0} / {1}")]
    Div(K, K),
    #[error("Cannot take exponent of types {0} ^ {1}")]
    Pow(K, K),
    #[error("Cannot take dot-product of types {0} . {1}")]
    Dot(K, K),
}

#[derive(Error, PartialEq, Eq, Debug)]
pub enum ArithmeticTypeError {
    #[error("ArithmeticKindError: {0}")]
    Kind(#[from] BinopError<TypeVar>),
    #[error("Kind {0} not found in context {1}")]
    KindNotFound(Kind, Ctx<Tid, Kind>),
    #[error("ArithmeticContainerError: {0}")]
    Container(#[from] BinopError<CTyp>),
}

/// Instances of this trait can be added, muliplied, divided, exp'd and dot product'd together, generating constraints and type errors
pub trait Lub where Self: Sized {
    type Term;
    fn lub_equ(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
    fn lub_add(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
    fn lub_sub(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
    fn lub_mul(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
    fn lub_div(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
    fn lub_pow(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
    fn lub_dot(a: Self::Term, b: Self::Term, ctx: &Ctx<Tid, Kind>) -> Result<Self::Term, ArithmeticTypeError>;
}

/// Unification of kinds is basically a least upper bound
impl Lub for Kind {
    type Term = Tid;

    /// Can the two kinds be unified into one kind that describes both?
    fn lub_equ(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(Kind::Field, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(Kind::Field, ctx.clone()))?;
        match (ka, kb) {
            // Both kinds are defined
            (Kind::Field, Kind::Field) => Ok(a),
            (Kind::Scalar(x), Kind::Scalar(y)) if x == y => Ok(a),
            (Kind::Multiplicative(x), Kind::Multiplicative(y)) if x == y => Ok(a),
            (Kind::Group, Kind::Group) => Ok(a),
            (Kind::Pairing(k1, k2), Kind::Pairing(k3, k4)) if k1 == k3 && k2 == k4 => Ok(a),
            // Ranges in kinds should be concretized already, if not its a bug
            (Kind::Range(_), _) | (_, Kind::Range(_)) => !unreachable(),
            (_, _) =>
                Err(ArithmeticTypeError::Kind(BinopError::Add(
                            TypeVar::new(a, ka),
                            TypeVar::new(b, kb)))),
        }
    }

    /// Type inference for addition of different kinds
    fn lub_add(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, ArithmeticTypeError> {
        Self::lub_equ(a, b, ctx)
    }

    /// Type inference for subtraction same as addition
    fn lub_sub(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, ArithmeticTypeError> {
        Self::lub_equ(a, b, ctx)
    }

    /// Type inference for multiplication of different kinds
    fn lub_mul(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(Kind::Field, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(Kind::Field, ctx.clone()))?;
        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Scalar multiplication: Scalar * Group = Group
            (_, Kind::Scalar(g)) if g == a && ka.is_group() => Ok(a),
            (Kind::Scalar(g), _) if g == b && kb.is_group() => Ok(b),
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
    fn lub_div(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, ArithmeticTypeError> {
        match (ctx.get_kind(&a)?, ctx.get_kind(&b)?) {
            (Kind::Field, Kind::Field) => Ok(a.clone()),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Group / Scalar = Group
            (Kind::Scalar(g), k2) if g == b && k2.is_group() => Ok(b),
            (_, _) =>
                Err(ArithmeticTypeError::Kind(BinopError::Div(TypeVar::new(a, ka), TypeVar::new(b, kb)))),
        }
    }

    /// Type inference for exponentiation of different kinds
    fn lub_pow(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>, constr: &mut SizeConstraints) -> Result<Tid, ArithmeticTypeError> {
        let ka = ctx.get(&a).ok_or(ArithmeticTypeError::KindNotFound(Kind::Field, ctx.clone()))?;
        let kb = ctx.get(&b).ok_or(ArithmeticTypeError::KindNotFound(Kind::Field, ctx.clone()))?;
        match (ka, kb) {
            (Kind::Field, Kind::Field) => Ok(a),
            (Kind::Scalar(g1), Kind::Scalar(g2)) if g1 == g2 => Ok(a),
            // Group ^ Scalar = Group
            (_, Kind::Scalar(g)) if ka.is_group() => Ok(a),
            (_, _) =>
                Err(ArithmeticTypeError::Kind(BinopError::Pow(TypeVar::new(a, k1), TypeVar::new(b, k2)))),
        }
    }
    /// Type inference for dot product is the same as multiplication (for kinds)
    fn lub_dot(a: Tid, b: Tid, ctx: &Ctx<Tid, Kind>) -> Result<Tid, ArithmeticTypeError> {
        Self::lub_mul(a, b, ctx)
    }
}

impl Lub for Typ {
    type Term = Typ;
    fn lub_equ(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Base(a), Typ::Base(b)) =>
                Ok(Typ::Base(Kind::lub_add(a, b, ctx))),
            // Fin<A..B> == Fin<C..D>
            (Typ::Fin(a), Typ::Fin(b)) =>
                Ok(Typ::Fin(Range::lub(a, b))),

            // Uni<A> + Uni<B> = Uni<C> where C = max(A, B)
            (Typ::Uni(a, n), Typ::Uni(b, m)) =>
                Ok(Typ::Uni(Kind::lub_add(a, b, ctx, constr)?, n.max(m).clone())),
            // Mle<A> + Mle<B> = Mle<C> where C = max(A, B)
            (Typ::Mle(a, n), Typ::Mle(b, m)) =>
                Ok(Typ::Mle(Kind::lub_add(a, b, ctx, constr)?, n.max(m).clone())),

            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (Typ::Vec(box a, n), Typ::Vec(box b, m)) =>
                Ok(Typ::vec(&Typ::lub_add(a, b, ctx, constr)?, &constr.add_eq(&n, &m)?)),

            // Uni<A> + c = Uni<A>
            (a, Typ::Uni(t, n)) | (Typ::Uni(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_add(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Uni(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(a, Typ::Uni(t, n))))
                },

            // Mle<A> + c = Mle<A>
            (a, Typ::Mle(t, n)) | (Typ::Mle(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_add(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Mle(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(a, Typ::Uni(t, n))))
                },

            // Implicit coercions with vectors of size 1
            // Vec<A> + c = Vec<a> + c = c where A = 1
            (a, Typ::Vec(box b, n)) | (Typ::Vec(box b, n), a) => {
                constr.add_eq(&n, &Size::one())?;
                Ok(Typ::lub_add(a, b, ctx, constr)?)
            },

            // Indices can act like finite fields
            (Typ::Base(a), Typ::Index(_)) if ctx.is_field(&a) => Ok(Typ::Base(a)),
            (Typ::Index(_), Typ::Base(a)) if ctx.is_field(&a) => Ok(Typ::Base(a)),

            (a, b) => Err(ArithmeticTypeError::Container(BinopError::Add(a, b)))
        }
        Self::lub_add(a, b, ctx)
    }
    fn lub_add(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Base(a), Typ::Base(b)) =>
                Ok(Typ::Base(Kind::lub_add(a, b, ctx, constr)?)),
            (Typ::Index(a), Typ::Index(b)) =>
                Ok(Typ::Index(a + b)),

            // Uni<A> + Uni<B> = Uni<C> where C = max(A, B)
            (Typ::Uni(a, n), Typ::Uni(b, m)) =>
                Ok(Typ::Uni(Kind::lub_add(a, b, ctx, constr)?, n.max(m).clone())),
            // Mle<A> + Mle<B> = Mle<C> where C = max(A, B)
            (Typ::Mle(a, n), Typ::Mle(b, m)) =>
                Ok(Typ::Mle(Kind::lub_add(a, b, ctx, constr)?, n.max(m).clone())),

            // Vec<A> + Vec<B> = Vec<C> where C = A = B
            (Typ::Vec(box a, n), Typ::Vec(box b, m)) =>
                Ok(Typ::vec(&Typ::lub_add(a, b, ctx, constr)?, &constr.add_eq(&n, &m)?)),

            // Uni<A> + c = Uni<A>
            (a, Typ::Uni(t, n)) | (Typ::Uni(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_add(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Uni(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(a, Typ::Uni(t, n))))
                },

            // Mle<A> + c = Mle<A>
            (a, Typ::Mle(t, n)) | (Typ::Mle(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_add(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Mle(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Add(a, Typ::Uni(t, n))))
                },

            // Implicit coercions with vectors of size 1
            // Vec<A> + c = Vec<a> + c = c where A = 1
            (a, Typ::Vec(box b, n)) | (Typ::Vec(box b, n), a) => {
                constr.add_eq(&n, &Size::one())?;
                Ok(Typ::lub_add(a, b, ctx, constr)?)
            },

            // Indices can act like finite fields
            (Typ::Base(a), Typ::Index(_)) if ctx.is_field(&a) => Ok(Typ::Base(a)),
            (Typ::Index(_), Typ::Base(a)) if ctx.is_field(&a) => Ok(Typ::Base(a)),

            (a, b) => Err(ArithmeticTypeError::Container(BinopError::Add(a, b)))
        }
    }

    fn lub_sub(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>, constr: &mut SizeConstraints) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Base(a), Typ::Base(b)) =>
                Ok(Typ::Base(Kind::lub_sub(a, b, ctx, constr)?)),
            (Typ::Index(a), Typ::Index(b)) =>
                Ok(Typ::Index(a - b)),

            // Indices can act like finite fields
            (Typ::Base(a), Typ::Index(_)) if ctx.is_field(&a) =>
                Ok(Typ::Base(a)),

            // Uni<A> - Uni<B> = Uni<C> where C = max(A, B)
            (Typ::Uni(a, n), Typ::Uni(b, m)) =>
                Ok(Typ::Uni(Kind::lub_sub(a, b, ctx, constr)?, n.max(m).clone())),
            // Mle<A> - Mle<B> = Mle<C> where C = max(A, B)
            (Typ::Mle(a, n), Typ::Mle(b, m)) =>
                Ok(Typ::Mle(Kind::lub_sub(a, b, ctx, constr)?, n.max(m).clone())),

            // Vec<A> - Vec<B> = Vec<C> where C = A = B
            (Typ::Vec(box a, n), Typ::Vec(box b, m)) =>
                Ok(Typ::vec(&Typ::lub_sub(a, b, ctx, constr)?, &constr.add_eq(&n, &m)?)),

            // Implicit coercions
            // c - Uni<A> = c where A = 1
            (a, Typ::Uni(t, n)) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_sub(a.clone(), Typ::base(&t), ctx, constr)? {
                    constr.add_eq(&n, &Size::one())?;
                    Ok(Typ::Base(c))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(a, Typ::Uni(t, n))))
                },
            // Uni<A> - c = Uni<A>
            (Typ::Uni(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_sub(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Uni(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(Typ::Uni(t, n), a)))
                },

            // c - Mle<A> = c where A = 1
            (a, Typ::Mle(t, n)) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_sub(a.clone(), Typ::base(&t), ctx, constr)? {
                    constr.add_eq(&n, &Size::one())?;
                    Ok(Typ::Base(c))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(a, Typ::Mle(t, n))))
                },
            // Mle<A> - c = Mle<A>
            (Typ::Mle(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_sub(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Mle(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Sub(Typ::Mle(t, n), a)))
                },
            // Vec<B> - A = Vec<B>
            (Typ::Vec(box a, n), b) =>
                Ok(Typ::vec(&Typ::lub_sub(a, b, ctx, constr)?, &n)),

            // c - Vec<A>  = c where A = 1
            (a, Typ::Vec(box b, n)) => {
                constr.add_eq(&n, &Size::one())?;
                Ok(Typ::lub_sub(a, b, ctx, constr)?)
            },

            (a, b) => Err(ArithmeticTypeError::Container(BinopError::Sub(a, b)))
        }
    }

    fn lub_mul(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>, constr: &mut SizeConstraints) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Base(a), Typ::Base(b)) =>
                Ok(Typ::Base(Kind::lub_mul(a, b, ctx, constr)?)),
            (Typ::Base(a), Typ::Index(_)) | (Typ::Index(_), Typ::Base(a)) if ctx.is_field(&a) => Ok(Typ::Base(a)),

            // Uni<A> * Uni<B> = Uni<C> where C = A + B
            (Typ::Uni(a, n), Typ::Uni(b, m)) =>
                Ok(Typ::Uni(Kind::lub_mul(a, b, ctx, constr)?, n + m)),

            // Vec<A> * Vec<B> = Vec<C> where C = A = B
            (Typ::Vec(box a, n), Typ::Vec(box b, m)) =>
                Ok(Typ::vec(&Typ::lub_mul(a, b, ctx, constr)?, &constr.add_eq(&n, &m)?)),

            // Vec<B> * X = X * Vec<B> = Vec<B>
            (x, Typ::Vec(box b, n)) | (Typ::Vec(box b, n), x) =>
                Ok(Typ::vec(&Typ::lub_mul(x, b, ctx, constr)?, &n)),

            // Uni<A> * c = Uni<A> * c = Uni<A>
            (a, Typ::Uni(t, n)) | (Typ::Uni(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_mul(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Uni(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Mul(a, Typ::Uni(t, n))))
                },

            // Mle<A> * c = Mle<A> * c = Mle<A>
            (a, Typ::Mle(t, n)) | (Typ::Mle(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_mul(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Mle(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Mul(a, Typ::Uni(t, n))))
                },

            (a, b) => Err(ArithmeticTypeError::Container(BinopError::Mul(a, b)))
        }
    }

    fn lub_div(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>, constr: &mut SizeConstraints) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Base(a), Typ::Base(b)) =>
                Ok(Typ::Base(Kind::lub_div(a, b, ctx, constr)?)),
            (Typ::Base(a), Typ::Index(_)) if ctx.is_field(&a) => Ok(Typ::Base(a)),

            // Uni<A> / Uni<B> = Uni<C> where C = A - B
            (Typ::Uni(a, n), Typ::Uni(b, m)) => {
                constr.add_gt(&n, &m)?;
                Ok(Typ::Uni(Kind::lub_div(a, b, ctx, constr)?, n - m))
            },

            // Vec<A> / Vec<B> = Vec<C> where C = A = B
            (Typ::Vec(box a, n), Typ::Vec(box b, m)) =>
                Ok(Typ::vec(&Typ::lub_div(a, b, ctx, constr)?, &constr.add_eq(&n, &m)?)),

            // Vec<B> / A = Vec<B>
            (Typ::Vec(box a, n), b) =>
                Ok(Typ::vec(&Typ::lub_div(a, b, ctx, constr)?, &n)),

            // Implicit coercions
            // c / Uni<A> = c where A = 1
            (a, Typ::Uni(t, n)) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_div(a.clone(), Typ::base(&t), ctx, constr)? {
                    constr.add_eq(&n, &Size::one())?;
                    Ok(Typ::Base(c))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(a, Typ::Uni(t, n))))
                },
            // Uni<A> / c = Uni<A>
            (Typ::Uni(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_div(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Uni(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(Typ::Uni(t, n), a)))
                },

            // c / Mle<A> = c where A = 1
            (a, Typ::Mle(t, n)) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_div(a.clone(), Typ::base(&t), ctx, constr)? {
                    constr.add_eq(&n, &Size::one())?;
                    Ok(Typ::Base(c))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(a, Typ::Mle(t, n))))
                },
            // Mle<A> / c = Mle<A>
            (Typ::Mle(t, n), a) if ctx.is_field(&t) =>
                if let Typ::Base(c) = Typ::lub_div(a.clone(), Typ::base(&t), ctx, constr)? {
                    Ok(Typ::Mle(c, n.clone()))
                } else {
                    Err(ArithmeticTypeError::Container(BinopError::Div(Typ::Mle(t, n), a)))
                },

            // c / Vec<A>  = c where A = 1
            (a, Typ::Vec(box b, n)) => {
                constr.add_eq(&n, &Size::one())?;
                Ok(Typ::lub_sub(a, b, ctx, constr)?)
            },

            // Vec<A> / c = Vec<A>
            (Typ::Vec(box b, n), a) =>
                Ok(Typ::vec(&Typ::lub_div(b, a, ctx, constr)?, &n)),

            (a, b) => Err(ArithmeticTypeError::Container(BinopError::Div(a, b)))
        }
    }

    fn lub_pow(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>, constr: &mut SizeConstraints) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Base(a), Typ::Base(b)) =>
                Ok(Typ::Base(Kind::lub_pow(a, b, ctx, constr)?)),
            (Typ::Base(a), Typ::Index(r)) if ctx.is_field(&a) => {
                constr.add_range(r);
                Ok(Typ::Base(a))
            },

            // Vec<B> ^ A = Vec<B>
            (Typ::Vec(box a, n), b) =>
                Ok(Typ::vec(&Typ::lub_pow(a, b, ctx, constr)?, &n)),

            // Uni<B> ^ A = Uni<B*A>
            (Typ::Uni(a, n), Typ::Index(r)) if ctx.is_field(&a) =>
                Ok(Typ::Uni(a, n + r.end)),

            // Mle<B> * A = A * Uni<B> = Uni<C> where C = A * B
            // Division of an MLE by an element
            (Typ::Mle(b, n), Typ::Base(a)) =>
                Ok(Typ::Mle(Kind::lub_pow(a, b, ctx, constr)?, n)),

            (a, b) => Err(ArithmeticTypeError::Container(BinopError::Pow(a, b)))
        }
    }

    fn lub_dot(a: Typ, b: Typ, ctx: &Ctx<Tid, Kind>, constr: &mut SizeConstraints) -> Result<Self, ArithmeticTypeError> {
        match (a, b) {
            (Typ::Vec(box a, n), Typ::Vec(box b, m)) => {
                constr.add_eq(&n, &m)?;
                Typ::lub_mul(a, b, ctx, constr)
            },
            (a, b) =>
                Self::lub_mul(a.clone(), b.clone(), ctx, constr)
                    .map_err(|_| ArithmeticTypeError::Container(BinopError::Dot(a.clone(), b.clone())))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::{SizeEval, SizeEvalError, Traversable1};
    use crate::lang::types::{Kind, Typ, Size, Constr, ConstrError};
    use crate::lang::context::Ctx;
    use crate::lang::types::context::{Ctx<Tid, Kind>, SizeConstraints};
    use crate::lang::id::Tid;
    use super::*;
    use itertools::Group;

    #[test]
    fn test_typ_lub_add_vec_err() {
        let mut constr = SizeConstraints::new();
        let mut ctx = Ctx<Tid, Kind>::new(
            Ctx::<Tid, Kind>::from([
                (Tid::from("G"), Kind::Group),
                (Tid::from("F"), Kind::Scalar(Tid::from("G")))
            ]), Ctx::new(), Ctx::new());

        assert_eq!(Typ::lub_add(
                      Typ::vec(&Typ::Base(Tid::from("F")), &Size::lit(4)),
                      Typ::vec(&Typ::Base(Tid::from("F")), &Size::one()), &ctx, &mut constr),
                   Err(ArithmeticTypeError::UnsatConstraint(ConstrError::Eq(Size::lit(4), Size::one()))));
    }
}
