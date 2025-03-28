use crate::ark::*;
use rayon::prelude::*;
use rand::Rng;
use core::hash::Hasher;
use std::ops::{Add, Sub, Mul, Div};

use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value<C: ArkConfig> {
    Scalar(C::F),
    Group1(C::G1),
    Group2(C::G2),
    GroupT(C::GT),
    Vec(Vec<Value<C>>),
    Uni(Uni<C::F>),
    Mle(Mle<C::F>),
}

impl<C: ArkConfig> Value<C> {
    pub fn into_scalar(self) -> C::F {
        match self {
            Value::Scalar(f) => f,
            _ => panic!("Expected scalar"),
        }
    }

    pub fn into_group1(self) -> C::G1 {
        match self {
            Value::Group1(g) => g,
            _ => panic!("Expected group1"),
        }
    }

    pub fn into_group2(self) -> C::G2 {
        match self {
            Value::Group2(g) => g,
            _ => panic!("Expected group2"),
        }
    }

    pub fn into_groupt(self) -> C::GT {
        match self {
            Value::GroupT(g) => g,
            _ => panic!("Expected groupT"),
        }
    }

    pub fn into_vec(self) -> Vec<Value<C>> {
        match self {
            Value::Vec(v) => v,
            _ => panic!("Expected vector"),
        }
    }

    pub fn into_uni(self) -> Uni<C::F> {
        match self {
            Value::Uni(u) => u,
            _ => panic!("Expected univariate polynomial"),
        }
    }

    pub fn into_mle(self) -> Mle<C::F> {
        match self {
            Value::Mle(m) => m,
            _ => panic!("Expected multilinear extension"),
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

impl<C: ArkConfig> Add for Value<C> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Value::Scalar(a), Value::Scalar(b)) => Value::Scalar(C::scalar_add(a, b)),
            (Value::Group1(a), Value::Group1(b)) => Value::Group1(C::group_add1(a, b)),
            (Value::Group2(a), Value::Group2(b)) => Value::Group2(C::group_add2(a, b)),
            (Value::GroupT(a), Value::GroupT(b)) => Value::GroupT(C::group_addt(a, b)),
            (Value::Vec(a), Value::Vec(b)) =>
                a.par_iter().zip(b.par_iter()).map(|(a, b)| a + b).collect(),
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

impl<C: ArkConfig> Mul for Value<C> {
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

