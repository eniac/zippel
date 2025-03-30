use crate::ark::*;
use rayon::prelude::*;
use rand::Rng;
use std::fmt;
use core::hash::Hasher;
use std::ops::{Add, Sub, Mul, Div, AddAssign, SubAssign, MulAssign, DivAssign};

use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value<C: ArkConfig> {
    Scalar(C::F),
    Group1(C::G1),
    Group2(C::G2),
    GroupT(C::GT),
    Uni(Uni<C::F>),
    Mle(Mle<C::F>),
    Vec(Box<Value<C>>, Vec<Value<C>>),
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

    pub fn scalar_vec_add(f1: &Vec<Self>, f2: &mut Vec<Self>) {
        f2.par_iter_mut().zip(f1.par_iter()).for_each(|(a, b)| *a += b);
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

impl<C: ArkConfig> Value<C> {
    /// Scalar addition, saves result in f2
    fn value_add(f1: &Self, f2: &mut Self) {
           match (self, other) {
            (Value::Scalar(a), Value::Scalar(b)) => C::scalar_add(a, b),
            (Value::Group1(a), Value::Group1(b)) => C::group_add1(a, b),
            (Value::Group2(a), Value::Group2(b)) => C::group_add2(a, b),
            (Value::GroupT(a), Value::GroupT(b)) => C::group_addt(a, b),
            (Value::Vec(a), Value::Vec(b)) => Value::Vec(vec![]),

                C::scalar_vec_add(a, b) f2),
                for (a, b) in a.iter().zip(b.iter_mut()) {
                    a.add(b);
                }
            },
            (Value::Uni(a), Value::Uni(b)) => *a = C::uni_add(*a, *b),
            (Value::Mle(a), Value::Mle(b)) => *a = C::mle_add(*a, *b),
            (a, b) => panic!("Mismatched values")
        }
    }
    fn add_assign(&mut self, other: Self) {
        match (self, other) {
            (Value::Scalar(a), Value::Scalar(b)) => a *= C::scalar_add(a, b),
            (Value::Group1(a), Value::Group1(b)) => Value::Group1(C::group_add1(a, b)),
            (Value::Group2(a), Value::Group2(b)) => Value::Group2(C::group_add2(a, b)),
            (Value::GroupT(a), Value::GroupT(b)) => Value::GroupT(C::group_addt(a, b)),
            (Value::Vec(a), Value::Vec(b)) => Value::Vec(C::vec_add(a, b)),
            (Value::Uni(a), Value::Scalar(b))
            | (Value::Scalar(b), Value::Uni(a)) => Value::Uni(C::uni_add(a, C::into_uni(b))),
            (Value::Uni(a), Value::Uni(b)) => Value::Uni(C::uni_add(a, b)),
            (Value::Mle(a), Value::Mle(b)) => Value::Mle(C::mle_add(a, b)),
            (a, b) => panic!("Mismatched values")
        }
    }
}

impl<C: ArkConfig> Sub for Value<C> {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Value::Scalar(a), Value::Scalar(b)) => Value::Scalar(C::scalar_sub(a, b)),
            (Value::Group1(a), Value::Group1(b)) => Value::Group1(C::group_sub1(a, b)),
            (Value::Group2(a), Value::Group2(b)) => Value::Group2(C::group_sub2(a, b)),
            (Value::GroupT(a), Value::GroupT(b)) => Value::GroupT(C::group_subt(a, b)),
            (Value::Vec(a), Value::Vec(b)) =>
                a.par_iter().zip(b.par_iter()).map(|(a, b)| a - b).collect(),
            (Value::Uni(a), Value::Uni(b)) => Value::Uni(C::uni_sub(a, b)),
            (Value::Mle(a), Value::Mle(b)) => Value::Mle(C::mle_sub(a, b)),
            (a, b) => panic!("Mismatched values")
        }
    }
}

impl<C: ArkConfig + Sized> Mul for Value<C> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Value::Scalar(a), Value::Scalar(b)) => Value::Scalar(C::scalar_mul(a, b)),
            (Value::Group1(a), Value::Scalar(b))
            | (Value::Scalar(b), Value::Group1(a)) => C::scalar_group_mul1(a, vec![b])[0],
            (Value::Group2(a), Value::Scalar(b))
            | (Value::Scalar(b), Value::Group2(a)) => C::scalar_group_mul2(a, vec![b])[0],
            (Value::GroupT(a), Value::Scalar(b))
            | (Value::Scalar(b), Value::GroupT(a)) => C::scalar_group_mult(a, vec![b])[0],
            (Value::Group1(a), Value::Group2(b))
            | (Value::Group2(b), Value::Group1(a))  => Value::GroupT(C::billinear_map(a, b)),
            // Empty vector
            (Value::Vec(a), _) | (_, Value::Vec(a)) if a.is_empty() => Value::Vec(a),
            // Vector<T> * scalar multiplication
            (Value::Vec(a), Value::Scalar(b))
            | (Value::Scalar(b), Value::Vec(a)) =>
                Value::Vec(a.par_iter().map(|a| a * Value::Scalar(b)).collect()),
            // Vector<scalar> * group1 multiplication
            (Value::Vec(a), Value::Group1(b))
            | (Value::Group1(b), Value::Vec(a)) if matches!(a[0], Value::Scalar(_)) =>
                Value::Vec(C::scalar_group_mul1(b, a.iter().map(|a| a.into_scalar()).collect())),
            // Vector<scalar> * group2 multiplication
            (Value::Vec(a), Value::Group2(b))
            | (Value::Group2(b), Value::Vec(a)) if matches!(a[0], Value::Scalar(_)) =>
                Value::Vec(C::scalar_group_mul2(b, a.iter().map(|a| a.into_scalar()).collect())),
            // Vector<scalar> * groupt multiplication
            (Value::Vec(a), Value::GroupT(b))
            | (Value::GroupT(b), Value::Vec(a)) if matches!(a[0], Value::Scalar(_)) =>
                Value::Vec(C::scalar_group_mult(b, a.iter().map(|a| a.into_scalar()).collect())),
            // Vector * Vector multiplication
            (Value::Vec(a), Value::Vec(b)) => Value::Vec(a.par_iter().zip(b.par_iter()).map(|(a, b)| a * b).collect()),

            // Uni * Uni
            (Value::Uni(a), Value::Uni(b)) => Value::Uni(C::uni_mul(a, b)),
            // Uni * scalar
            (Value::Uni(a), Value::Scalar(b))
            // TODO: Keep going
            | (Value::Scalar(b), Value::Uni(a)) => Value::Uni(C::uni_scalar_mul(a, b)),
            (Value::Mle(a), Value::Scalar(b)) => Value::Mle(C::mle_mul(a, b)),
            (a, b) => panic!("Mismatched values")
        }
    }
}
*/

