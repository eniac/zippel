use crate::ark::*;
use ark_ff::Field;
use rayon::prelude::*;
use rand::Rng;
use std::fmt;
use core::hash::Hasher;
use std::ops::{Add, Sub, Mul, Div, AddAssign, SubAssign, MulAssign, DivAssign};

use ark_poly::polynomial::univariate::DensePolynomial as Uni;
use ark_poly::evaluations::multivariate::multilinear::DenseMultilinearExtension as Mle;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value<C: ArkConfig> {
    Index(u64),
    Scalar(C::F),
    Group1(C::G1),
    Group2(C::G2),
    GroupT(C::GT),
    Uni(Uni<C::F>),
    Mle(Mle<C::F>),
    VecIndex(Vec<u64>),
    VecScalar(Vec<C::F>),
    VecGroup1(Vec<C::G1>),
    VecGroup2(Vec<C::G2>),
    VecGroupT(Vec<C::GT>),
}

impl<C: ArkConfig> Value<C> {
    pub fn into_scalar(&self) -> C::F {
        match self {
            Value::Scalar(f) => *f,
            Value::Index(i) => (*i).into(),
            _ => panic!("Expected scalar, found {}", self),
        }
    }
    pub fn into_group1(&self) -> &C::G1 {
        match self {
            Value::Group1(g) => g,
            _ => panic!("Expected group1, found {}", self),
        }
    }
    pub fn into_group2(&self) -> &C::G2 {
        match self {
            Value::Group2(g) => g,
            _ => panic!("Expected group2, found {}", self),
        }
    }
    pub fn into_groupt(&self) -> &C::GT {
        match self {
            Value::GroupT(g) => g,
            _ => panic!("Expected groupt, found {}", self),
        }
    }
    pub fn into_scalar_mut(&mut self) -> &mut C::F {
        match self {
            Value::Scalar(f) => f,
            Value::Index(i) => {
                *self = Value::Scalar((*i).into());
                self.into_scalar_mut()
            },
            _ => panic!("Expected mut scalar, found {}", self),
        }
    }
    pub fn into_uni_mut(&mut self) -> &mut Uni<C::F> {
        match self {
            Value::Uni(u) => u,
            Value::Scalar(s) => {
                *self = Value::Uni(C::into_uni(*s));
                self.into_uni_mut()
            },
            Value::Index(i) => {
                *self = Value::Uni(C::into_uni((*i).into()));
                self.into_uni_mut()
            },
            _ => panic!("Expected mut uni, found {}", self),
        }
    }
    pub fn into_mle_mut(&mut self) -> &mut Mle<C::F> {
        match self {
            Value::Mle(m) => m,
            Value::Scalar(s) => {
                *self = Value::Mle(C::into_mle(*s));
                self.into_mle_mut()
            },
            Value::Index(i) => {
                *self = Value::Mle(C::into_mle((*i).into()));
                self.into_mle_mut()
            },
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

    pub fn into_vec_scalar_mut(&mut self) -> &mut Vec<C::F> {
        match self {
            Value::VecScalar(v) => v,
            Value::VecIndex(v) => {
                *self = Value::VecScalar(v.iter().map(|i| (*i).into()).collect());
                self.into_vec_scalar_mut()
            },
            _ => panic!("Expected mut vec scalar, found {}", self),
        }
    }
    pub fn into_vec_group1(&self) -> &Vec<C::G1> {
        match self {
            Value::VecGroup1(v) => v,
            _ => panic!("Expected vec group1, found {}", self),
        }
    }
    pub fn into_vec_group2(&self) -> &Vec<C::G2> {
        match self {
            Value::VecGroup2(v) => v,
            _ => panic!("Expected vec group2, found {}", self),
        }
    }
    pub fn into_vec_group1_mut(&mut self) -> &mut Vec<C::G1> {
        match self {
            Value::VecGroup1(v) => v,
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }
    pub fn into_vec_group2_mut(&mut self) -> &mut Vec<C::G2> {
        match self {
            Value::VecGroup2(v) => v,
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }
    pub fn into_vec_groupt_mut(&mut self) -> &mut Vec<C::GT> {
        match self {
            Value::VecGroupT(v) => v,
            _ => panic!("Expected mut vec groupt, found {}", self),
        }
    }
    pub fn into_vec_index_mut(&mut self) -> &mut Vec<u64> {
        match self {
            Value::VecIndex(v) => v,
            _ => panic!("Expected mut vec index, found {}", self),
        }
    }
    pub fn into_vec_index(&self) -> &Vec<u64> {
        match self {
            Value::VecIndex(v) => v,
            _ => panic!("Expected vec index, found {}", self),
        }
    }
    pub fn into_index(&self) -> u64 {
        match self {
            Value::Index(i) => *i,
            _ => panic!("Expected index, found {}", self),
        }
    }
    pub fn into_index_mut(&mut self) -> &mut u64 {
        match self {
            Value::Index(i) => i,
            _ => panic!("Expected mut index, found {}", self),
        }
    }
}

impl<C: ArkConfig> fmt::Display for Value<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Index(i) => write!(f, "{}", i),
            Value::Scalar(a) => C::scalar_fmt(a, f),
            Value::Group1(a) => C::group_fmt1(a, f),
            Value::Group2(g) => C::group_fmt2(g, f),
            Value::GroupT(g) => C::group_fmtt(g, f),
            Value::Uni(u) => C::uni_fmt(u, f),
            Value::Mle(m) => C::mle_fmt(m, f),
            Value::VecScalar(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            },
            Value::VecGroup1(v) => {
                write!(f, "[")?;
                for i in v {
                    C::group_fmt1(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecGroup2(v) => {
                write!(f, "[")?;
                for i in v {
                    C::group_fmt2(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecGroupT(v) => {
                write!(f, "[")?;
                for i in v {
                    C::group_fmtt(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecIndex(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            },
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
    pub fn value_add(&self, other: &mut Self) {
        match self {
            // Indexes coerce to scalars (addition)
            Value::Index(a) =>
                match &other {
                    Value::Index(_) => *other.into_index_mut() += *a,
                    Value::Scalar(_) => C::scalar_add(&(*a).into(), other.into_scalar_mut()),
                    Value::Uni(_) => C::uni_add(&C::into_uni((*a).into()), other.into_uni_mut()),
                    Value::Mle(_) => C::mle_add(&C::into_mle((*a).into()), other.into_mle_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Scalar(a) =>
                match &other {
                    Value::Index(b) => C::scalar_add(a, &mut (*b).into()),
                    Value::Scalar(_) => C::scalar_add(a, other.into_scalar_mut()),
                    Value::Uni(_) => C::uni_add(&C::into_uni(*a), other.into_uni_mut()),
                    Value::Mle(_) => C::mle_add(&C::into_mle(*a), other.into_mle_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            // Group addition
            Value::Group1(a) =>
                C::group_add1(a, other.into_group1_mut()),
            Value::Group2(a) =>
                C::group_add2(a, other.into_group2_mut()),
            Value::GroupT(a) =>
                C::group_addt(a, other.into_groupt_mut()),
            // The same but for vectors (scalars)
            Value::VecIndex(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_index_mut() .par_iter_mut())
                        .for_each(|(a, b)| *b += *a),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_add(&(*a).into(), b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_add(a, b)),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_add(a, b)),
                    _ => panic!("Expected vec scalar, found {}", other)
                },
            Value::VecGroup1(vs) =>
                vs.par_iter()
                .zip(other.into_vec_group1_mut().par_iter_mut())
                .for_each(|(a, b)| C::group_add1(a, b)),
            Value::VecGroup2(vs) =>
                vs.par_iter()
                .zip(other.into_vec_group2_mut().par_iter_mut())
                .for_each(|(a, b)| C::group_add2(a, b)),
            Value::VecGroupT(vs) =>
                vs.par_iter()
                .zip(other.into_vec_groupt_mut().par_iter_mut())
                .for_each(|(a, b)| C::group_addt(a, b)),
            // Univariate polynomials
            Value::Uni(a) =>
                C::uni_add(a, other.into_uni_mut()),
            // Multivariate polynomials
            Value::Mle(a) =>
                C::mle_add(a, other.into_mle_mut()),
        }
    }

    pub fn value_sub(&self, other: &mut Self) {
        match self {
            // Indexes coerce to scalars (addition)
            Value::Index(a) =>
                match &other {
                    Value::Index(b) => *other.into_index_mut() = *a - *b,
                    Value::Scalar(_) => C::scalar_sub(&(*a).into(), other.into_scalar_mut()),
                    Value::Uni(_) => C::uni_sub(&C::into_uni((*a).into()), other.into_uni_mut()),
                    Value::Mle(_) => C::mle_sub(&C::into_mle((*a).into()), other.into_mle_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Scalar(a) =>
                match &other {
                    Value::Index(b) => C::scalar_sub(a, &mut (*b).into()),
                    Value::Scalar(_) => C::scalar_sub(a, other.into_scalar_mut()),
                    Value::Uni(_) => C::uni_sub(&C::into_uni(*a), other.into_uni_mut()),
                    Value::Mle(_) => C::mle_sub(&C::into_mle(*a), other.into_mle_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            // Group addition
            Value::Group1(a) =>
                C::group_sub1(a, other.into_group1_mut()),
            Value::Group2(a) =>
                C::group_sub2(a, other.into_group2_mut()),
            Value::GroupT(a) =>
                C::group_subt(a, other.into_groupt_mut()),
            // The same but for vectors (scalars)
            Value::VecIndex(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_index_mut() .par_iter_mut())
                        .for_each(|(a, b)| *b = *a - *b),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_sub(&(*a).into(), b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_sub(a, b)),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_sub(a, b)),
                    _ => panic!("Expected vec scalar, found {}", other)
                },
            Value::VecGroup1(vs) =>
                vs.par_iter()
                .zip(other.into_vec_group1_mut().par_iter_mut())
                .for_each(|(a, b)| C::group_sub1(a, b)),
            Value::VecGroup2(vs) =>
                vs.par_iter()
                .zip(other.into_vec_group2_mut().par_iter_mut())
                .for_each(|(a, b)| C::group_sub2(a, b)),
            Value::VecGroupT(vs) =>
                vs.par_iter()
                .zip(other.into_vec_groupt_mut().par_iter_mut())
                .for_each(|(a, b)| C::group_subt(a, b)),
            // Univariate polynomials
            Value::Uni(a) =>
                C::uni_sub(a, other.into_uni_mut()),
            // Multivariate polynomials
            Value::Mle(a) =>
                C::mle_sub(a, other.into_mle_mut()),
        }
    }

    /// Value multiplication, saves result in other
    pub fn value_mul(&self, other: &mut Self) {
        match self {
            Value::Index(a) =>
                match &other {
                    // Index * Index = Index
                    Value::Index(_) => *other.into_index_mut() *= *a,
                    // Index * whatever, cast index to scalar
                    Value::Scalar(_) => C::scalar_mul(&(*a).into(), other.into_scalar_mut()),
                    // Index * Univariate polynomial
                    Value::Uni(_) => C::uni_mul(&C::into_uni((*a).into()), other.into_uni_mut()),
                    // Index * Multivariate polynomial
                    Value::Mle(_) => C::mle_mul(&(*a).into(), other.into_mle_mut()),
                    // Index * groups
                    Value::Group1(_) => {
                        let group = other.into_group1_mut();
                        C::group_mul1(&(*a).into(), group);
                    },
                    Value::Group2(_) => {
                        let group = other.into_group2_mut();
                        C::group_mul2(&(*a).into(), group);
                    },
                    Value::GroupT(_) => {
                        let group = other.into_groupt_mut();
                        C::group_mult(&(*a).into(), group);
                    },
                    // Index * Vectors
                    Value::VecIndex(_) =>
                        other.into_vec_index_mut().par_iter_mut()
                        .for_each(|b| *b *= *a),
                    Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::scalar_mul(&(*a).into(), b)),
                    Value::VecGroup1(_) =>
                        other.into_vec_group1_mut().par_iter_mut()
                        .for_each(|b| C::group_mul1(&(*a).into(), b)),
                    Value::VecGroup2(_) =>
                        other.into_vec_group2_mut().par_iter_mut()
                        .for_each(|b| C::group_mul2(&(*a).into(), b)),
                    Value::VecGroupT(_) =>
                        other.into_vec_groupt_mut().par_iter_mut()
                        .for_each(|b| C::group_mult(&(*a).into(), b)),
                },
            Value::Scalar(a) =>
                match &other {
                    // Scalar * index, cast index to Scalar
                    Value::Index(b) => C::scalar_mul(a, &mut (*b).into()),
                    // Scalar * Scalar = Scalar
                    Value::Scalar(_) => C::scalar_mul(a, other.into_scalar_mut()),
                    // Scalar * Univariate polynomial
                    Value::Uni(_) => C::uni_mul(&C::into_uni(*a), other.into_uni_mut()),
                    // Scalar * Multivariate polynomial
                    Value::Mle(_) => C::mle_mul(a, other.into_mle_mut()),
                    // Index * groups
                    Value::Group1(_) => {
                        let group = other.into_group1_mut();
                        C::group_mul1(a, group);
                    },
                    Value::Group2(_) => {
                        let group = other.into_group2_mut();
                        C::group_mul2(a, group);
                    },
                    Value::GroupT(_) => {
                        let group = other.into_groupt_mut();
                        C::group_mult(a, group);
                    },
                    // Scalar * Vector
                    Value::VecIndex(_) | Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::scalar_mul(a, b)),
                    Value::VecGroup1(_) =>
                        other.into_vec_group1_mut().par_iter_mut()
                        .for_each(|b| C::group_mul1(a, b)),
                    Value::VecGroup2(_) =>
                        other.into_vec_group2_mut().par_iter_mut()
                        .for_each(|b| C::group_mul2(a, b)),
                    Value::VecGroupT(_) =>
                        other.into_vec_groupt_mut().par_iter_mut()
                        .for_each(|b| C::group_mult(a, b)),
                },
            Value::Group1(a) =>
                match &other {
                    // Group1 * Group2 = GroupT
                    Value::Group2(_) =>
                        *other = Value::GroupT(C::billinear_map(a, other.into_group2())),
                    // Group1 * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let mut group = C::scalar_group_mul1(a, &vec![other.into_scalar()]);
                        *other = Value::Group1(group.remove(0));
                    },
                    // Group1 * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecGroup1(C::scalar_group_mul1(a, vr));
                    },
                    // Group1 * Vec<Group2>
                    Value::VecGroup2(_) =>
                        *other = Value::GroupT(C::billinear_vec_mul(&vec![*a], other.into_vec_group2())[0]),
                    _ => panic!("Expected scalar or group2, found {}", other)
                },
            Value::Group2(a) =>
                match &other {
                    // Group2 * Group1 = GroupT
                    Value::Group1(_) =>
                        *other = Value::GroupT(C::billinear_map(other.into_group1(), a)),
                    // Group2 * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecGroup2(C::scalar_group_mul2(a, vr));
                    },
                    // Group2 * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecGroup2(C::scalar_group_mul2(a, vr));
                    },
                    // Group2 * Vec<Group1>
                    Value::VecGroup1(_) =>
                        *other = Value::GroupT(C::billinear_vec_mul(other.into_vec_group1(), &vec![*a])[0]),
                    _ => panic!("Expected scalar or group1, found {}", other)
                },
            Value::GroupT(a) =>
                match &other {
                    // GroupT * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let mut vr = vec![*other.into_scalar_mut()];
                        let mut group = C::scalar_group_mult(a, &mut vr);
                        *other = Value::GroupT(group.remove(0));
                    },
                    // GroupT * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecGroupT(C::scalar_group_mult(a, vr))
                    },
                    _ => panic!("Expected scalar, found {}", other)
                }
            Value::VecIndex(v) =>
                match &other {
                    // Vec<Index> * Index
                    Value::Index(i) =>
                        *other = Value::VecIndex(v.par_iter().map(|a| *a * *i).collect()),
                    // Vec<Index> * Scalar
                    Value::Scalar(_) => {
                        *other = Value::VecScalar(std::iter::repeat(other.into_scalar()).take(v.len()).collect::<Vec<_>>());
                        Self::value_mul(self, other);
                    },
                    // Vec<index> * Group1
                    Value::Group1(g) =>
                        *other = Value::VecGroup1(C::scalar_group_mul1(g, &v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>())),
                    // Vec<index> * Group2
                    Value::Group2(g) =>
                        *other = Value::VecGroup2(C::scalar_group_mul2(g, &v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>())),
                    // Vec<index> * GroupT
                    Value::GroupT(g) =>
                        *other = Value::VecGroupT(C::scalar_group_mult(g, &v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>())),
                    // Vec<Index> * Vec<Index> = Vec<Index>
                    Value::VecIndex(_) =>
                        v.par_iter()
                        .zip(other.into_vec_index_mut().par_iter_mut())
                        .for_each(|(a, b)| *b *= *a),
                    // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                    Value::VecScalar(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_mul(&(*a).into(), b)),
                    // Vec<Index> * Vec<Group1> = Vec<Group1>
                    Value::VecGroup1(_) =>
                        v.par_iter()
                        .zip(other.into_vec_group1_mut().par_iter_mut())
                        .for_each(|(a, b)| C::group_mul1(&(*a).into(), b)),
                    // Vec<Index> * Vec<Group2> = Vec<Group2>
                    Value::VecGroup2(_) =>
                        v.par_iter()
                        .zip(other.into_vec_group2_mut().par_iter_mut())
                        .for_each(|(a, b)| C::group_mul2(&(*a).into(), b)),
                    // Vec<Index> * Vec<GroupT> = Vec<GroupT>
                    Value::VecGroupT(_) =>
                        v.par_iter()
                        .zip(other.into_vec_groupt_mut().par_iter_mut())
                        .for_each(|(a, b)| C::group_mult(&(*a).into(), b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(v) =>
                match &other {
                    // Vec<Scalar> * Index
                    Value::Index(_) | Value::Scalar(_) => {
                        *other = Value::VecScalar(std::iter::repeat(other.into_scalar()).take(v.len()).collect::<Vec<_>>());
                        Self::value_mul(self, other);
                    }
                    // Vec<Scalar> * Group1
                    Value::Group1(g) =>
                        *other = Value::VecGroup1(C::scalar_group_mul1(g, v)),
                    // Vec<index> * Group2
                    Value::Group2(g) =>
                        *other = Value::VecGroup2(C::scalar_group_mul2(g, v)),
                    // Vec<index> * GroupT
                    Value::GroupT(g) =>
                        *other = Value::VecGroupT(C::scalar_group_mult(g, v)),
                    // Vec<Index> * Vec<Index> = Vec<Index>
                    Value::VecIndex(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_mul(a, b)),
                    // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                    Value::VecScalar(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_mul(a, b)),
                    // Vec<Index> * Vec<Group1> = Vec<Group1>
                    Value::VecGroup1(_) =>
                        v.par_iter()
                        .zip(other.into_vec_group1_mut().par_iter_mut())
                        .for_each(|(a, b)| C::group_mul1(a, b)),
                    // Vec<Index> * Vec<Group2> = Vec<Group2>
                    Value::VecGroup2(_) =>
                        v.par_iter()
                        .zip(other.into_vec_group2_mut().par_iter_mut())
                        .for_each(|(a, b)| C::group_mul2(a, b)),
                    // Vec<Index> * Vec<GroupT> = Vec<GroupT>
                    Value::VecGroupT(_) =>
                        v.par_iter()
                        .zip(other.into_vec_groupt_mut().par_iter_mut())
                        .for_each(|(a, b)| C::group_mult(a, b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecGroup1(v) =>
                match &other {
                    // Vec<Group1> * Group2 = Vec<GroupT>
                    Value::Group2(g) =>
                        *other = Value::VecGroupT(v.par_iter()
                            .map(|a| C::billinear_map(a, g))
                            .collect()),
                    // Vec<Group1> * scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let a = other.into_scalar();
                        *other = Value::VecGroup1(v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::group_mul1(&a, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = &*other.into_vec_scalar_mut();
                        let mut vr = v.clone();
                        vl.par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::group_mul1(a, b));
                        *other = Value::VecGroup1(vr);
                    },
                    // Vec<Group1> * Vec<Group2>
                    Value::VecGroup2(_) =>
                        *other = Value::VecGroupT(C::billinear_vec_mul(v, other.into_vec_group2())),
                    _ => panic!("Expected scalar or group2, found {}", other)
                },
            Value::VecGroup2(v) =>
                match &other {
                    // Vec<Group2> * Group1 = Vec<GroupT>
                    Value::Group1(g) =>
                        *other = Value::VecGroupT(v.par_iter()
                            .map(|a| C::billinear_map(g, a))
                            .collect()),
                    // Vec<Group2> * scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let a = other.into_scalar();
                        *other = Value::VecGroup2(v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::group_mul2(&a, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group2> * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = &*other.into_vec_scalar_mut();
                        let mut vr = v.clone();
                        vl.par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::group_mul2(a, b));
                        *other = Value::VecGroup2(vr);
                    },
                    // Vec<Group1> * Vec<Group2>
                    Value::VecGroup1(_) =>
                        *other = Value::VecGroupT(C::billinear_vec_mul(other.into_vec_group1(), v)),
                    _ => panic!("Expected scalar or group1, found {}", other)
                },
            Value::VecGroupT(v) =>
                match &other {
                    // Vec<GroupT> * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let a = other.into_scalar();
                        *other = Value::VecGroupT(v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::group_mult(&a, &mut gm);
                                gm
                            }).collect());
                    },
                    // GroupT * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = &*other.into_vec_scalar_mut();
                        let mut vr = v.clone();
                        vl.par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::group_mult(a, b));
                        *other = Value::VecGroupT(vr);
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Uni(a) =>
                C::uni_mul(a, other.into_uni_mut()),
            Value::Mle(a) => {
                let x = other.into_scalar();
                let mut vl = a.clone();
                C::mle_mul(&x, &mut vl);
                *other = Value::Mle(vl);
            }
        }
    }

    /// Value division, saves result in other
    pub fn value_div(&self, other: &mut Self) {
        match self {
            Value::Index(a) =>
                match &other {
                    // Index / Index = Index
                    Value::Index(_) => *other.into_index_mut() /= *a,
                    // Index / whatever, cast index to scalar
                    Value::Scalar(_) => C::scalar_div(&(*a).into(), other.into_scalar_mut()),
                    // Index / Vectors
                    Value::VecIndex(_) =>
                        other.into_vec_index_mut().par_iter_mut()
                        .for_each(|b| *b /= *a),
                    Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::scalar_div(&(*a).into(), b)),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Scalar(a) =>
                match &other {
                    // Scalar / index, cast index to Scalar
                    Value::Index(b) => C::scalar_div(a, &mut (*b).into()),
                    // Scalar / Scalar = Scalar
                    Value::Scalar(_) => C::scalar_div(a, other.into_scalar_mut()),
                    // Scalar / Vector
                    Value::VecIndex(_) | Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::scalar_div(a, b)),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Group1(a) =>
                match &other {
                    // Group1 / scalar
                    Value::Scalar(_) | Value::Index(_) => {
                        let f = other.into_scalar().inverse()
                            .expect(format!("Failed to invert scalar {}", other).as_str());
                        let mut g = *a;
                        C::group_mul1(&f, &mut g);
                        *other = Value::Group1(g);
                    },
                    // Group1 / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(&mut vr);
                        *other = Value::VecGroup1(C::scalar_group_mul1(a, &vr));
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Group2(a) =>
                match &other {
                    // Group2 / scalar
                    Value::Scalar(_) | Value::Index(_) => {
                        let f = other.into_scalar().inverse()
                            .expect(format!("Failed to invert scalar {}", other).as_str());
                        let mut g = *a;
                        C::group_mul2(&f, &mut g);
                        *other = Value::Group2(g);
                    },
                    // Group2 / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(&mut vr);
                        *other = Value::VecGroup2(C::scalar_group_mul2(a, &vr));
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::GroupT(a) =>
                match &other {
                    // Group2 / scalar
                    Value::Scalar(_) | Value::Index(_) => {
                        let f = other.into_scalar().inverse()
                            .expect(format!("Failed to invert scalar {}", other).as_str());
                        let mut g = *a;
                        C::group_mult(&f, &mut g);
                        *other = Value::GroupT(g);
                    },
                    // Group2 / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(&mut vr);
                        *other = Value::VecGroupT(C::scalar_group_mult(a, &vr));
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::VecIndex(v) =>
                match &other {
                    // Vec<Index> / Index
                    Value::Index(i) =>
                        *other = Value::VecIndex(v.par_iter().map(|a| *a / *i).collect()),
                    // Vec<Index> / Scalar
                    Value::Scalar(_) => {
                        *other = Value::VecScalar(std::iter::repeat(other.into_scalar()).take(v.len()).collect::<Vec<_>>());
                        Self::value_div(self, other);
                    },
                    // Vec<Index> / Vec<Index> = Vec<Index>
                    Value::VecIndex(_) =>
                        v.par_iter()
                        .zip(other.into_vec_index_mut().par_iter_mut())
                        .for_each(|(a, b)| *b /= *a),
                    // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                    Value::VecScalar(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::scalar_div(&(*a).into(), b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(v) =>
                match &other {
                    // Vec<Scalar> / Index
                    Value::Index(_) | Value::Scalar(_) => {
                        *other = Value::VecScalar(std::iter::repeat(other.into_scalar()).take(v.len()).collect::<Vec<_>>());
                        Self::value_div(self, other);
                    }
                    // Vec<Index> / Vec<Index> = Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(&mut vr);
                        v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::scalar_mul(a, b));
                    },
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecGroup1(v) =>
                match &other {
                    // Vec<Group1> / scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(vr);
                        *other = Value::VecGroup1(v.par_iter().zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::group_mul1(f, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(vl);
                        let mut vr = v.clone();
                        (*vl).par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::group_mul1(a, b));
                        *other = Value::VecGroup1(vr);
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::VecGroup2(v) =>
                match &other {
                    // Vec<Group1> / scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(vr);
                        *other = Value::VecGroup2(v.par_iter().zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::group_mul2(f, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(vl);
                        let mut vr = v.clone();
                        (*vl).par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::group_mul2(a, b));
                        *other = Value::VecGroup2(vr);
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::VecGroupT(v) =>
                match &other {
                    // Vec<Group1> / scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(vr);
                        *other = Value::VecGroupT(v.par_iter().zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::group_mult(f, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = other.into_vec_scalar_mut();
                        C::scalar_vec_inv(vl);
                        let mut vr = v.clone();
                        (*vl).par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::group_mult(a, b));
                        *other = Value::VecGroupT(vr);
                    },
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Uni(a) =>
                C::uni_div(a, other.into_uni_mut()),
            Value::Mle(a) => {
                let x = other.into_scalar();
                let mut vl = a.clone();
                C::mle_div(&x, &mut vl);
                *other = Value::Mle(vl);
            }
        }
    }

    /// Value exponentiation, saves result in other
    pub fn value_pow(&self, other: &mut Self) {
        #[inline]
        fn pow64(a: u64, i: u64) -> u64 {
            let mut i = i;
            let mut exp = a;
            while i % 2 == 0 {
                exp *= exp;
                i /= 2;
            }
            while i > 1 {
                exp *= a;
                i -= 1;
            }
            exp
        }
        match (self, &other) {
            // Index ^ Index = Index
            (Value::Index(a), Value::Index(i)) =>
                *other.into_index_mut() = pow64(*a, *i),
            // Scalar ^ Index
            (Value::Scalar(a), Value::Index(i)) => {
                let mut a = a.clone();
                C::scalar_pow(&mut a, *i);
                *other = Value::Scalar(a);
            },
            // Vec<Index> ^ Index
            (Value::VecIndex(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| *v = pow64(*v, *i));
                *other = Value::VecIndex(vs);
            },
            // Vec<Scalar> ^ Index
            (Value::VecScalar(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| C::scalar_pow(v, *i));
                *other = Value::VecScalar(vs);
            },
            (Value::Uni(u), Value::Index(i)) => {
                let mut u = u.clone();
                C::uni_pow(&mut u, *i);
                *other = Value::Uni(u);
            },
            (a, b) => panic!("Mismatched values {} ^ {}", a, b)
        }
    }

    pub fn value_dot(&self, other: &mut Self) {
        match (&self, &other) {
            (Value::VecIndex(a), Value::VecGroup1(b))
            | (Value::VecGroup1(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::Group1(C::scalar_group_dot1(b, &vf));
            },
            (Value::VecIndex(a), Value::VecGroup2(b))
            | (Value::VecGroup2(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::Group2(C::scalar_group_dot2(b, &vf));
            },
            (Value::VecIndex(a), Value::VecGroupT(b))
            | (Value::VecGroupT(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::GroupT(C::scalar_group_dott(b, &vf));
            },
            (Value::VecScalar(a), Value::VecGroup1(b))
            | (Value::VecGroup1(b), Value::VecScalar(a)) =>
                *other = Value::Group1(C::scalar_group_dot1(b, a)),
            (Value::VecScalar(a), Value::VecGroup2(b))
            | (Value::VecGroup2(b), Value::VecScalar(a)) =>
                *other = Value::Group2(C::scalar_group_dot2(b, a)),
            (Value::VecScalar(a), Value::VecGroupT(b))
            | (Value::VecGroupT(b), Value::VecScalar(a)) =>
                *other = Value::GroupT(C::scalar_group_dott(b, a)),
            (Value::VecIndex(a), Value::VecIndex(b)) =>
                *other = Value::Index(a.par_iter()
                    .zip(b.par_iter())
                    .map(|(a, b)| *a * *b)
                    .sum()),
            (Value::VecIndex(v), _) => {
                let vf = other.into_vec_scalar_mut();
                *other = Value::Scalar(
                    (*vf).par_iter()
                        .zip(v.par_iter())
                        .map(|(a, b)| {
                            let mut a = *a;
                            C::scalar_mul(&(*b).into(), &mut a);
                            a
                        }).reduce(
                            || C::scalar_zero(),
                            |mut a, b| {
                                C::scalar_add(&b, &mut a);
                                a
                            }
                        ));
            },
            (Value::VecScalar(v), _) => {
                let vf = other.into_vec_scalar_mut();
                *other = Value::Scalar(
                    (*vf).par_iter()
                        .zip(v.par_iter())
                        .map(|(a, b)| {
                            let mut a = *a;
                            C::scalar_mul(b, &mut a);
                            a
                        }).reduce(
                            || C::scalar_zero(),
                            |mut a, b| {
                                C::scalar_add(&b, &mut a);
                                a
                            }
                        ));
            }
            (Value::VecGroup1(a), Value::VecGroup2(b))
            | (Value::VecGroup2(b), Value::VecGroup1(a)) =>
                *other = Value::GroupT(
                    a.par_iter()
                    .zip(b.par_iter())
                    .map(|(a, b)| C::billinear_map(a, b))
                    .reduce(|| C::group_zerot(), |mut a, b| {
                        C::group_addt(&b, &mut a);
                        a
                    })),
            (a, b) => panic!("Mismatched values {} . {}", a, b)
        }
    }
}


