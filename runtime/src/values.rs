use crate::ark::*;
use rayon::prelude::*;
use rand::Rng;
use std::fmt;
use core::hash::Hasher;
use std::ops::{Add, Sub, Mul, Div, AddAssign, SubAssign, MulAssign, DivAssign};

use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value<C: ArkConfig> {
    Scalar(C::F),
    Group1(C::G1),
    Group2(C::G2),
    GroupT(C::GT),
    Uni(Uni<C::F>),
    Mle(Mle<C::F>),
    Vec(Vec<Value<C>>),
}

impl<C: ArkConfig> Value<C> {
    pub fn into_scalar(&self) -> &C::F {
        match self {
            Value::Scalar(f) => f,
            _ => panic!("Expected scalar, found {}", self),
        }
    }

    pub fn into_scalar_mut(&mut self) -> &mut C::F {
        match self {
            Value::Scalar(f) => f,
            _ => panic!("Expected mut scalar, found {}", self),
        }
    }

    pub fn into_uni_mut(&mut self) -> &mut Uni<C::F> {
        match self {
            Value::Uni(u) => u,
            _ => panic!("Expected mut uni, found {}", self),
        }
    }

    pub fn into_mle_mut(&mut self) -> &mut Mle<C::F> {
        match self {
            Value::Mle(m) => m,
            _ => panic!("Expected mut mle, found {}", self),
        }
    }

    pub fn into_group1_mut(&mut self) -> &mut C::G1 {
        match self {
            Value::Group1(g) => g,
            _ => panic!("Expected mut group1, found {}", self),
        }
    }

    pub fn into_group2_mut(&mut self) -> &mut C::G2 {
        match self {
            Value::Group2(g) => g,
            _ => panic!("Expected mut group2, found {}", self),
        }
    }

    pub fn into_groupt_mut(&mut self) -> &mut C::GT {
        match self {
            Value::GroupT(g) => g,
            _ => panic!("Expected mut groupt, found {}", self),
        }
    }

    pub fn into_vec_mut(&mut self) -> &mut Vec<Value<C>> {
        match self {
            Value::Vec(v) => v,
            _ => panic!("Expected mut vec, found {}", self),
        }
    }
}

impl<C: ArkConfig> fmt::Display for Value<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Scalar(a) => C::scalar_fmt(a, f),
            Value::Group1(a) => C::group_fmt1(a, f),
            Value::Group2(g) => C::group_fmt2(g, f),
            Value::GroupT(g) => C::group_fmtt(g, f),
            Value::Uni(u) => C::uni_fmt(u, f),
            Value::Mle(m) => C::mle_fmt(m, f),
            Value::Vec(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            }
        }
    }
}

pub type ValueBls12_381 = Value<ArkBls12_381>;
pub type ValueCurve25519 = Value<ArkCurve25519>;
pub type ValueBn254 = Value<ArkBn254>;
pub type ValueMNT4_298 = Value<ArkMNT4_298>;
pub type ValueSecp256k1 = Value<ArkSecp256k1>;
pub type ValuePallas = Value<ArkPallas>;
pub type ValueVesta = Value<ArkVesta>;
pub type ValueEd25519 = Value<ArkEd25519>;
pub type ValueF17 = Value<ArkF17>;
pub type ValueF65537 = Value<ArkF65537>;

impl<C: ArkConfig + Clone> Value<C> {
    /// Value addition, saves result in other
    fn value_add(&self, other: &mut Self) {
        match (self, other) {
            (Value::Scalar(a), Value::Scalar(b)) => C::scalar_add(a, b),
            (Value::Group1(a), Value::Group1(b)) => C::group_add1(a, b),
            (Value::Group2(a), Value::Group2(b)) => C::group_add2(a, b),
            (Value::GroupT(a), Value::GroupT(b)) => C::group_addt(a, b),
            (Value::Vec(a), Value::Vec(b)) =>
                a.par_iter().zip(b.par_iter_mut())
                .for_each(|(a, b)| Self::value_add(a, &mut *b)),
            (Value::Uni(a), Value::Uni(b)) => C::uni_add(a, b),
            (Value::Uni(a), other) => {
                let scalar = other.into_scalar();
                let mut uni = C::into_uni(*scalar);
                C::uni_add(&a, &mut uni);
                *other = Value::Uni(uni);
            },
            (Value::Scalar(b), Value::Uni(a)) =>
                C::uni_add(&C::into_uni(*b), a),
            (Value::Mle(a), Value::Mle(b)) => C::mle_add(a, b),
            (Value::Mle(a), other) => {
                let scalar = other.into_scalar();
                let mut mle = C::into_mle(*scalar);
                C::mle_add(&a, &mut mle);
                *other = Value::Mle(mle);
            },
            (Value::Scalar(b), Value::Mle(a)) => C::mle_add(&C::into_mle(*b), a),
            (a, b) => panic!("Mismatched values {} + {}", a, b)
        }
    }

    /// Value negation in-place
    fn value_neg(&mut self) {
        match self {
            Value::Scalar(a) => C::scalar_neg(a),
            Value::Group1(a) => C::group_neg1(a),
            Value::Group2(a) => C::group_neg2(a),
            Value::GroupT(a) => C::group_negt(a),
            Value::Vec(a) => a.par_iter_mut().for_each(|a| Self::value_neg(a)),
            Value::Uni(a) => C::uni_neg(a),
            Value::Mle(a) => C::mle_neg(a),
        }
    }

    fn value_sub(&self, other: &mut Self) {
        other.value_neg();
        self.value_add(other);
    }

    /// Value multiplication, saves result in other
    fn value_mul(&self, other: &mut Self) {
        match (self, &other) {
            // Scalar * Scalar = Scalar
            (Value::Scalar(a), Value::Scalar(_)) =>
                C::scalar_mul(a, other.into_scalar_mut()),

            // Group1 * Group2 = GroupT
            (Value::Group1(a), Value::Group2(b)) => {
                *other = Value::GroupT(C::billinear_map(*a, *b));
            },
            // Group1 * scalar multiplication
            (Value::Group1(a), Value::Scalar(b)) => {
                let mut group = C::scalar_group_mul1(*a, vec![*b]);
                *other = Value::Group1(group.remove(0));
            },
            // Scalar * Group1 multiplication
            (Value::Scalar(b), Value::Group1(_)) => {
                let a = other.into_group1_mut();
                *a = C::scalar_group_mul1(*a, vec![*b])[0];
            },
            // Group2 * scalar multiplication
            (Value::Group2(a), Value::Scalar(b)) => {
                let mut group = C::scalar_group_mul2(*a, vec![*b]);
                *other = Value::Group2(group.remove(0));
            },
            // Scalar * Group2 multiplication
            (Value::Scalar(b), Value::Group2(_)) => {
                let a = other.into_group2_mut();
                *a = C::scalar_group_mul2(*a, vec![*b])[0];
            },
            // GroupT * scalar multiplication
            (Value::GroupT(a), Value::Scalar(b)) => {
                let mut group = C::scalar_group_mult(*a, vec![*b]);
                *other = Value::GroupT(group.remove(0));
            },
            // Scalar * GroupT multiplication
            (Value::Scalar(b), Value::GroupT(_)) => {
                let a = other.into_groupt_mut();
                *a = C::scalar_group_mult(*a, vec![*b])[0];
            },
            // Vector<T> * Vector<T> multiplication
            (Value::Vec(a), Value::Vec(_)) =>
                a.par_iter().zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_mul(&mut *b)),
            // Vector<T> * T multiplication
            (Value::Vec(a), _) => {
                let other = std::iter::repeat(other.clone()).take(a.len()).collect::<Vec<_>>();
                Self::value_mul(self, &mut Value::Vec(other));
            },
            // T * Vector<T> multiplication
            (_, Value::Vec(_)) =>
                other.into_vec_mut().par_iter_mut().for_each(|b| self.value_mul(b)),

            // Uni * Uni
            (Value::Uni(a), Value::Uni(_)) =>
                C::uni_mul(a, other.into_uni_mut()),
            // Uni * scalar
            (Value::Uni(a), Value::Scalar(b)) => {
                let mut uni = C::into_uni(*b);
                C::uni_mul(a, &mut uni);
                *other = Value::Uni(uni);
            },
            // Scalar * Uni
            (Value::Scalar(b), Value::Uni(_)) =>
                C::uni_mul(&C::into_uni(*b), other.into_uni_mut()),

            // Mle * scalar
            (Value::Mle(_), Value::Scalar(b)) => {
                let mut mle = C::into_mle(*b);
                C::mle_mul(b, &mut mle);
                *other = Value::Mle(mle);
            },
            // Scalar * Mle
            (Value::Scalar(b), Value::Mle(_)) =>
                C::mle_mul(b, other.into_mle_mut()),
            (a, b) => panic!("Mismatched values {} * {}", a, b)
        }
    }
}

