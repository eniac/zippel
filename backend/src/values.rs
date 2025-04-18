use ark_ec::pairing::PairingOutput;
use ark_ff::Field;
use lang::typ::Range;
use rayon::prelude::*;
use rand::Rng;
use std::fmt;
use core::hash::{Hash, Hasher};
use ark_ff::Zero;
use std::ops::{Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr, AddAssign, MulAssign};
use ark_ec::{AffineRepr, CurveGroup};

use crate::{ATyp, ArkConfig, ArkScalarOps, ArkGroupOps, ArkPairingOps};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value<C: ArkConfig> {
    /// Boolean
    Bool(bool),
    VecBool(Vec<bool>),
    /// Scalars
    Index(u64),
    Scalar(C::F),
    VecIndex(Vec<u64>),
    VecScalar(Vec<C::F>),
    /// Groups
    G1(C::G1),
    G2(C::G2),
    GT(PairingOutput<C::P>),
    VecG1(Vec<C::G1>),
    VecG2(Vec<C::G2>),
    VecGT(Vec<PairingOutput<C::P>>),
    /// Affine group elements
    G1Affine(C::G1Affine),
    G2Affine(C::G2Affine),
    VecG1Affine(Vec<C::G1Affine>),
    VecG2Affine(Vec<C::G2Affine>),
    /// Vectors of vectors etc
    Vec(Vec<Value<C>>)
}

impl<C: ArkConfig> Value<C> {
    /// Value addition, saves result in other
    #[inline]
    pub fn value_add(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => panic!("Cannot add bools {} + {}", self, other),
            // Indexes coerce to scalars (addition)
            Value::Index(a) =>
                match &other {
                    Value::Index(_) => *other.into_index_mut() += *a,
                    Value::Scalar(_) => C::FOps::add(&(*a).into(), other.into_scalar_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Scalar(a) =>
                match &other {
                    Value::Index(b) => C::FOps::add(a, &mut (*b).into()),
                    Value::Scalar(_) => C::FOps::add(a, other.into_scalar_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            // Group addition
            Value::G1Affine(a) =>
                C::G1Ops::add(a, other.into_g1_mut()),
            Value::G2Affine(a) =>
                C::G2Ops::add(a, other.into_g2_mut()),
            Value::G1(a) =>
                C::G1Ops::add(&(*a).into_affine(), other.into_g1_mut()),
            Value::G2(a) =>
                C::G2Ops::add(&(*a).into_affine(), other.into_g2_mut()),
            Value::GT(a) =>
                C::POps::add(a, other.into_gt_mut()),
            // The same but for vectors (scalars)
            Value::VecIndex(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_index_mut().par_iter_mut())
                        .for_each(|(a, b)| *b += *a),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::add(&(*a).into(), b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::add(a, b)),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::add(a, b)),
                    _ => panic!("Expected vec scalar, found {}", other)
                },
            Value::VecG1Affine(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::add(a, b)),
            Value::VecG2Affine(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::add(a, b)),
            Value::VecG1(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::add(&(*a).into_affine(), b)),
            Value::VecG2(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::add(&(*a).into_affine(), b)),
            Value::VecGT(vs) =>
                vs.par_iter()
                .zip(other.into_vec_gt_mut().par_iter_mut())
                .for_each(|(a, b)| C::POps::add(a, b)),
            Value::Vec(vs) =>
                vs.par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_add(b)),
        }
    }

    #[inline]
    pub fn value_sub(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => panic!("Cannot subtract bools {} - {}", self, other),
            // Indexes coerce to scalars (addition)
            Value::Index(a) =>
                match &other {
                    Value::Index(b) => *other.into_index_mut() = *a - *b,
                    Value::Scalar(_) => C::FOps::sub(&(*a).into(), other.into_scalar_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Scalar(a) =>
                match &other {
                    Value::Index(b) => C::FOps::sub(a, &mut (*b).into()),
                    Value::Scalar(_) => C::FOps::sub(a, other.into_scalar_mut()),
                    _ => panic!("Expected scalar, found {}", other)
                },
            // Group addition
            Value::G1Affine(a) =>
                C::G1Ops::sub(a, other.into_g1_mut()),
            Value::G2Affine(a) =>
                C::G2Ops::sub(a, other.into_g2_mut()),
            Value::G1(a) =>
                C::G1Ops::sub(&(*a).into_affine(), other.into_g1_mut()),
            Value::G2(a) =>
                C::G2Ops::sub(&(*a).into_affine(), other.into_g2_mut()),
            Value::GT(a) =>
                C::POps::sub(a, other.into_gt_mut()),
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
                        .for_each(|(a, b)| C::FOps::sub(&(*a).into(), b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(vs) =>
                match &other {
                    Value::VecIndex(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::sub(a, b)),
                    Value::VecScalar(_) =>
                        vs.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::sub(a, b)),
                    _ => panic!("Expected vec scalar, found {}", other)
                },
            Value::VecG1Affine(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::sub(a, b)),
            Value::VecG2Affine(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::sub(a, b)),
            Value::VecG1(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::sub(&(*a).into_affine(), b)),
            Value::VecG2(vs) =>
                vs.par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::sub(&(*a).into_affine(), b)),
            Value::VecGT(vs) =>
                vs.par_iter()
                .zip(other.into_vec_gt_mut().par_iter_mut())
                .for_each(|(a, b)| C::POps::sub(a, b)),
            Value::Vec(vs) =>
                vs.par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_sub(b)),
        }
    }

    /// Value multiplication, saves result in other
    #[inline]
    pub fn value_mul(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => panic!("Cannot multiply bools {} * {}", self, other),
            Value::Index(a) =>
                match &other {
                    Value::Bool(_) | Value::VecBool(_) => panic!("Cannot multiply bools {} * {}", self, other),
                    // Index * Index = Index
                    Value::Index(_) => *other.into_index_mut() *= *a,
                    // Index * whatever, cast index to scalar
                    Value::Scalar(_) => C::FOps::mul(&(*a).into(), other.into_scalar_mut()),
                    // Index * groups
                    Value::G1(_) | Value::G1Affine(_) => {
                        let group = other.into_g1_mut();
                        C::G1Ops::mul(&(*a).into(), group);
                    },
                    Value::G2(_) | Value::G2Affine(_) => {
                        let group = other.into_g2_mut();
                        C::G2Ops::mul(&(*a).into(), group);
                    },
                    Value::GT(_) => {
                        let group = other.into_gt_mut();
                        C::POps::mul(&(*a).into(), group);
                    },
                    // Index * Vectors
                    Value::VecIndex(_) =>
                        other.into_vec_index_mut().par_iter_mut()
                        .for_each(|b| *b *= *a),
                    Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::FOps::mul(&(*a).into(), b)),
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        other.into_vec_g1_mut().par_iter_mut()
                        .for_each(|b| C::G1Ops::mul(&(*a).into(), b)),
                    Value::VecG2(_) | Value::VecG2Affine(_) =>
                        other.into_vec_g2_mut().par_iter_mut()
                        .for_each(|b| C::G2Ops::mul(&(*a).into(), b)),
                    Value::VecGT(_) =>
                        other.into_vec_gt_mut().par_iter_mut()
                        .for_each(|b| C::POps::mul(&(*a).into(), b)),
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_mul(b)),
                },
            Value::Scalar(a) =>
                match &other {
                    Value::Bool(_) | Value::VecBool(_) => panic!("Cannot multiply bools {} * {}", self, other),
                    // Scalar * index, cast index to Scalar
                    Value::Index(b) => C::FOps::mul(a, &mut (*b).into()),
                    // Scalar * Scalar = Scalar
                    Value::Scalar(_) => C::FOps::mul(a, other.into_scalar_mut()),
                    // Index * groups
                    Value::G1(_) | Value::G1Affine(_) => {
                        let group = other.into_g1_mut();
                        C::G1Ops::mul(a, group);
                    },
                    Value::G2(_) | Value::G2Affine(_) => {
                        let group = other.into_g2_mut();
                        C::G2Ops::mul(a, group);
                    },
                    Value::GT(_) => {
                        let group = other.into_gt_mut();
                        C::POps::mul(a, group);
                    },
                    // Scalar * Vector
                    Value::VecIndex(_) | Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::FOps::mul(a, b)),
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        other.into_vec_g1_mut().par_iter_mut()
                        .for_each(|b| C::G1Ops::mul(a, b)),
                    Value::VecG2(_) | Value::VecG2Affine(_) =>
                        other.into_vec_g2_mut().par_iter_mut()
                        .for_each(|b| C::G2Ops::mul(a, b)),
                    Value::VecGT(_) =>
                        other.into_vec_gt_mut().par_iter_mut()
                        .for_each(|b| C::POps::mul(a, b)),
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_mul(b)),
                },
            Value::G1(a) =>
                match &other {
                    // Group1 * G2 = GT
                    Value::G2(_) | Value::G2Affine(_) =>
                        *other = Value::GT(C::POps::billinear_map(a, other.into_g2_mut())),
                    // Group1 * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let mut group = C::G1Ops::vec_mul(a, &vec![other.into_scalar()]);
                        *other = Value::G1Affine(group.remove(0));
                    },
                    // Group1 * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecG1Affine(C::G1Ops::vec_mul(a, vr));
                    },
                    // Group1 * Vec<G2>
                    Value::VecG2(_) | Value::VecG2Affine(_) =>
                        *other = Value::GT(C::POps::billinear_vec_mul(&vec![*a], other.into_vec_g2_mut())[0]),
                    // Group1 * Vec<T>
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_mul(b)),
                    _ => panic!("Expected scalar or group2, found {}", other)
                },
            Value::G2(a) =>
                match &other {
                    // G2 * Group1 = GT
                    Value::G1(_) | Value::G1Affine(_) =>
                        *other = Value::GT(C::POps::billinear_map(other.into_g1_mut(), a)),
                    // G2 * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecG2Affine(C::G2Ops::vec_mul(a, vr));
                    },
                    // G2 * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecG2Affine(C::G2Ops::vec_mul(a, vr));
                    },
                    // G2 * Vec<Group1>
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        *other = Value::GT(C::POps::billinear_vec_mul(other.into_vec_g1_mut(), &vec![*a])[0]),
                    // G2 * Vec<T>
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_mul(b)),
                    _ => panic!("Expected scalar or group1, found {}", other)
                },
            Value::G1Affine(a) =>
                Self::value_mul(&Value::G1((*a).into()), other),
            Value::G2Affine(a) =>
                Self::value_mul(&Value::G2((*a).into()), other),
            Value::GT(a) =>
                match &other {
                    // GT * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let mut vr = vec![*other.into_scalar_mut()];
                        let mut group = C::POps::vec_mul(a, &mut vr);
                        *other = Value::GT(group.remove(0));
                    },
                    // GT * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        *other = Value::VecGT(C::POps::vec_mul(a, vr))
                    },
                    // GT * Vec<T>
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_mul(b)),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::VecIndex(v) =>
                match &other {
                    Value::Bool(_) | Value::VecBool(_) => panic!("Cannot multiply bools {} * {}", self, other),
                    // Vec<Index> * Index
                    Value::Index(i) =>
                        *other = Value::VecIndex(v.par_iter().map(|a| *a * *i).collect()),
                    // Vec<Index> * Scalar
                    Value::Scalar(_) => {
                        *other = Value::VecScalar(std::iter::repeat(other.into_scalar()).take(v.len()).collect::<Vec<_>>());
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(&(*a).into(), b))
                    },
                    // Vec<index> * Group1
                    Value::G1(_) | Value::G1Affine(_) =>
                        *other = Value::VecG1Affine(C::G1Ops::vec_mul(&*other.into_g1_mut(),
                                &v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>())),
                    // Vec<index> * G2
                    Value::G2(_) | Value::G2Affine(_) =>
                        *other = Value::VecG2Affine(C::G2Ops::vec_mul(&*other.into_g2_mut(),
                                &v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>())),
                    // Vec<index> * GT
                    Value::GT(g) =>
                        *other = Value::VecGT(C::POps::vec_mul(g, &v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>())),
                    // Vec<Index> * Vec<Index> = Vec<Index>
                    Value::VecIndex(_) =>
                        v.par_iter()
                        .zip(other.into_vec_index_mut().par_iter_mut())
                        .for_each(|(a, b)| *b *= *a),
                    // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                    Value::VecScalar(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(&(*a).into(), b)),
                    // Vec<Index> * Vec<Group1> = Vec<Group1>
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        v.par_iter()
                        .zip(other.into_vec_g1_mut().par_iter_mut())
                        .for_each(|(a, b)| C::G1Ops::mul(&(*a).into(), b)),
                    // Vec<Index> * Vec<G2> = Vec<G2>
                    Value::VecG2(_) | Value::VecG2Affine(_) =>
                        v.par_iter()
                        .zip(other.into_vec_g2_mut().par_iter_mut())
                        .for_each(|(a, b)| C::G2Ops::mul(&(*a).into(), b)),
                    // Vec<Index> * Vec<GT> = Vec<GT>
                    Value::VecGT(_) =>
                        v.par_iter()
                        .zip(other.into_vec_gt_mut().par_iter_mut())
                        .for_each(|(a, b)| C::POps::mul(&(*a).into(), b)),
                    // Vec<Index> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::Index(*a).value_mul(b)),
                },
            Value::VecScalar(v) =>
                match &other {
                    // Vec<Scalar> * Index
                    Value::Index(_) | Value::Scalar(_) => {
                        *other = Value::VecScalar(std::iter::repeat(other.into_scalar()).take(v.len()).collect::<Vec<_>>());
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(&(*a).into(), b))
                    },
                    // Vec<Scalar> * Group1
                    Value::G1(g) =>
                        *other = Value::VecG1Affine(C::G1Ops::vec_mul(g, v)),
                    // Vec<index> * G2
                    Value::G2(g) =>
                        *other = Value::VecG2Affine(C::G2Ops::vec_mul(g, v)),
                    // Vec<index> * GT
                    Value::GT(g) =>
                        *other = Value::VecGT(C::POps::vec_mul(g, v)),
                    // Vec<Scalar> * Vec<Scalar> = Vec<Scalar>
                    Value::VecIndex(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b)),
                    // Vec<Scalar> * Vec<Scalar> = Vec<Scalar>
                    Value::VecScalar(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b)),
                    // Vec<Scalar> * Vec<Group1> = Vec<Group1>
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        v.par_iter()
                        .zip(other.into_vec_g1_mut().par_iter_mut())
                        .for_each(|(a, b)| C::G1Ops::mul(a, b)),
                    // Vec<Scalar> * Vec<G2> = Vec<G2>
                    Value::VecG2(_) | Value::VecG2Affine(_) =>
                        v.par_iter()
                        .zip(other.into_vec_g2_mut().par_iter_mut())
                        .for_each(|(a, b)| C::G2Ops::mul(a, b)),
                    // Vec<Scalar> * Vec<GT> = Vec<GT>
                    Value::VecGT(_) =>
                        v.par_iter()
                        .zip(other.into_vec_gt_mut().par_iter_mut())
                        .for_each(|(a, b)| C::POps::mul(a, b)),
                    // Vec<Scalar> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::Scalar(*a).value_mul(b)),
                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecG1(v) =>
                match &other {
                    // Vec<Group1> * G2 = Vec<GT>
                    Value::G2(_) | Value::G2Affine(_) => {
                        let g = other.into_g2_mut();
                        *other = Value::VecGT(v.par_iter()
                            .map(|a| C::POps::billinear_map(a, g))
                            .collect())
                    },
                    // Vec<Group1> * scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let a = other.into_scalar();
                        *other = Value::VecG1(v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::G1Ops::mul(&a, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = &*other.into_vec_scalar_mut();
                        let mut vr = v.clone();
                        vl.par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::G1Ops::mul(a, b));
                        *other = Value::VecG1(vr);
                    },
                    // Vec<Group1> * Vec<G2>
                    Value::VecG2(_)  | Value::VecG2Affine(_) =>
                        *other = Value::VecGT(C::POps::billinear_vec_mul(v, other.into_vec_g2_mut())),
                    // Vec<Group1> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::G1(*a).value_mul(b)),
                    _ => panic!("Expected scalar or group2, found {}", other)
                },
            Value::VecG2(v) =>
                match &other {
                    // Vec<G2> * Group1 = Vec<GT>
                    Value::G1(_) | Value::G1Affine(_) => {
                        let g = other.into_g1_mut();
                        *other = Value::VecGT(v.par_iter()
                            .map(|a| C::POps::billinear_map(g, a))
                            .collect());
                    },
                    // Vec<G2> * scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let a = other.into_scalar();
                        *other = Value::VecG2(v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::G2Ops::mul(&a, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<G2> * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = &*other.into_vec_scalar_mut();
                        let mut vr = v.clone();
                        vl.par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::G2Ops::mul(a, b));
                        *other = Value::VecG2(vr);
                    },
                    // Vec<Group1> * Vec<G2>
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        *other = Value::VecGT(C::POps::billinear_vec_mul(other.into_vec_g1_mut(), v)),
                    // Vec<G2> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::G2(*a).value_mul(b)),
                    _ => panic!("Expected scalar or group1, found {}", other)
                },
            Value::VecG1Affine(v) =>
                Self::value_mul(&Value::VecG1(v.par_iter().map(|a| (*a).into()).collect()), other),
            Value::VecG2Affine(v) =>
                Self::value_mul(&Value::VecG2(v.par_iter().map(|a| (*a).into()).collect()), other),
            Value::VecGT(v) =>
                match &other {
                    // Vec<GT> * scalar multiplication
                    Value::Scalar(_) | Value::Index(_) => {
                        let a = other.into_scalar();
                        *other = Value::VecGT(v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::POps::mul(&a, &mut gm);
                                gm
                            }).collect());
                    },
                    // GT * Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = &*other.into_vec_scalar_mut();
                        let mut vr = v.clone();
                        vl.par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::POps::mul(a, b));
                        *other = Value::VecGT(vr);
                    },
                    // Vec<GT> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::GT(*a).value_mul(b)),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Vec(v) =>
                v.par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_mul(b)),
        }
    }

    /// Value division, saves result in other
    #[inline]
    pub fn value_div(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => panic!("Cannot divide bools {} / {}", self, other),
            Value::Index(a) =>
                match &other {
                    // Index / Index = Index
                    Value::Index(_) => *other.into_index_mut() /= *a,
                    // Index / whatever, cast index to scalar
                    Value::Scalar(_) => C::FOps::div(&(*a).into(), other.into_scalar_mut()),
                    // Index / Vectors
                    Value::VecIndex(_) =>
                        other.into_vec_index_mut().par_iter_mut()
                        .for_each(|b| *b /= *a),
                    Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::FOps::div(&(*a).into(), b)),
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_div(b)),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Scalar(a) =>
                match &other {
                    // Scalar / index, cast index to Scalar
                    Value::Index(b) => C::FOps::div(a, &mut (*b).into()),
                    // Scalar / Scalar = Scalar
                    Value::Scalar(_) => C::FOps::div(a, other.into_scalar_mut()),
                    // Scalar / Vector
                    Value::VecIndex(_) | Value::VecScalar(_) =>
                        other.into_vec_scalar_mut().par_iter_mut()
                        .for_each(|b| C::FOps::div(a, b)),
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_div(b)),
                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::G1(a) =>
                match &other {
                    // Group1 / scalar
                    Value::Scalar(_) | Value::Index(_) => {
                        let f = other.into_scalar().inverse()
                            .expect(format!("Failed to invert scalar {}", other).as_str());
                        let mut g = *a;
                        C::G1Ops::mul(&f, &mut g);
                        *other = Value::G1(g);
                    },
                    // Group1 / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(&mut vr);
                        *other = Value::VecG1Affine(C::G1Ops::vec_mul(a, &vr));
                    },
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_div(b)),


                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::G2(a) =>
                match &other {
                    // G2 / scalar
                    Value::Scalar(_) | Value::Index(_) => {
                        let f = other.into_scalar().inverse()
                            .expect(format!("Failed to invert scalar {}", other).as_str());
                        let mut g = *a;
                        C::G2Ops::mul(&f, &mut g);
                        *other = Value::G2(g);
                    },
                    // G2 / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(&mut vr);
                        *other = Value::VecG2Affine(C::G2Ops::vec_mul(a, &vr));
                    },
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_div(b)),

                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::G1Affine(a) =>
                Self::value_div(&Value::G1((*a).into()), other),
            Value::G2Affine(a) =>
                Self::value_div(&Value::G2((*a).into()), other),
            Value::GT(a) =>
                match &other {
                    // G2 / scalar
                    Value::Scalar(_) | Value::Index(_) => {
                        let f = other.into_scalar().inverse()
                            .expect(format!("Failed to invert scalar {}", other).as_str());
                        let mut g = *a;
                        C::POps::mul(&f, &mut g);
                        *other = Value::GT(g);
                    },
                    // G2 / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(&mut vr);
                        *other = Value::VecGT(C::POps::vec_mul(a, &vr));
                    },
                    Value::Vec(_) =>
                        other.into_vec_mut().par_iter_mut()
                        .for_each(|b| self.value_div(b)),

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
                         v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::div(&(*a).into(), b));
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
                        .for_each(|(a, b)| C::FOps::div(&(*a).into(), b)),
                    // Vec<Index> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::Index(*a).value_div(b)),

                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecScalar(v) =>
                match &other {
                    // Vec<Scalar> / Index
                    Value::Index(_) | Value::Scalar(_) => {
                        let f = other.into_scalar_mut();
                        f.inverse()
                            .expect(format!("Failed to invert scalar {}", f).as_str());
                        let mut vr = std::iter::repeat(f.clone()).take(v.len()).collect::<Vec<_>>();
                        v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b));
                        *other = Value::VecScalar(vr);
                    }
                    // Vec<Index> / Vec<Index> = Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        let mut vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(&mut vr);
                        v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b));
                    },
                    // Vec<Scalar> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::Scalar(*a).value_div(b)),

                    _ => panic!("Expected vec index, found {}", other)
                },
            Value::VecG1(v) =>
                match &other {
                    // Vec<Group1> / scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(vr);
                        *other = Value::VecG1(v.par_iter().zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::G1Ops::mul(f, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(vl);
                        let mut vr = v.clone();
                        (*vl).par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::G1Ops::mul(a, b));
                        *other = Value::VecG1(vr);
                    },
                    // Vec<G1> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::G1(*a).value_div(b)),

                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::VecG2(v) =>
                match &other {
                    // Vec<Group1> / scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(vr);
                        *other = Value::VecG2(v.par_iter().zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::G2Ops::mul(f, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(vl);
                        let mut vr = v.clone();
                        (*vl).par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::G2Ops::mul(a, b));
                        *other = Value::VecG2(vr);
                    },
                    // Vec<G2> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::G2(*a).value_div(b)),

                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::VecG1Affine(v) =>
                Self::value_div(&Value::VecG1(v.par_iter().map(|a| (*a).into()).collect()), other),
            Value::VecG2Affine(v) =>
                Self::value_div(&Value::VecG2(v.par_iter().map(|a| (*a).into()).collect()), other),
            Value::VecGT(v) =>
                match &other {
                    // Vec<Group1> / scalar multiplication
                    Value::Index(_) | Value::Scalar(_) => {
                        let vr = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(vr);
                        *other = Value::VecGT(v.par_iter().zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::POps::mul(f, &mut gm);
                                gm
                            }).collect());
                    },
                    // Vec<Group1> / Vec<Index>
                    Value::VecIndex(_) | Value::VecScalar(_) => {
                        // TODO: There has to be a better way to do this...
                        let vl = other.into_vec_scalar_mut();
                        C::FOps::vec_inv(vl);
                        let mut vr = v.clone();
                        (*vl).par_iter().zip(vr.par_iter_mut())
                            .for_each(|(a, b)| C::POps::mul(a, b));
                        *other = Value::VecGT(vr);
                    },
                    // Vec<GT> * Vec<T>
                    Value::Vec(_) =>
                        v.par_iter()
                        .zip(other.into_vec_mut().par_iter_mut())
                        .for_each(|(a, b)| Value::GT(*a).value_div(b)),

                    _ => panic!("Expected scalar, found {}", other)
                },
            Value::Vec(v) =>
                v.par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_div(b)),
        }
    }

    pub fn value_rem(&self, other: &mut Self) {
        match (self, &other) {
            (Value::Index(a), Value::Index(b)) =>
                *other.into_index_mut() = *a % *b,
            (Value::Index(i), Value::VecIndex(_)) => {
                other.into_vec_index_mut()
                    .par_iter_mut().for_each(|v| *v %= *i);
            },
            (Value::VecIndex(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| *v %= *i);
                *other = Value::VecIndex(vs);
            },
            (Value::VecIndex(vs), Value::VecIndex(_)) => {
                other.into_vec_index_mut()
                    .par_iter_mut()
                    .zip(vs.par_iter())
                    .for_each(|(v, i)| *v  = *i % *v);
                },
            (_, _) =>
                panic!("Cannot do {} % {}", self, other)
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
                C::FOps::pow(&mut a, *i);
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
                vs.par_iter_mut().for_each(|v| C::FOps::pow(v, *i));
                *other = Value::VecScalar(vs);
            },
            // Vec<Index> ^ Vec<Index> = Vec<Index>
            (Value::VecIndex(vs), _) =>
                vs.par_iter()
                .zip(other.into_vec_index_mut().par_iter_mut())
                .for_each(|(a, b)| *b = pow64(*a, *b)),

            // Vec<T> ^ Index
            (Value::Vec(vs), Value::Index(_)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| Value::value_pow(other, v));
                *other = Value::Vec(vs);
            }
            // Vec<T> ^ Vec
            (Value::Vec(v), _) =>
                v.par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_pow(b)),
            (a, b) => panic!("Mismatched values {} ^ {}", a, b)
        }
    }

    #[inline]
    pub fn value_dot(&self, other: &mut Self) {
        match (&self, &other) {
            (Value::VecIndex(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::G1(C::G1Ops::vec_dot(b, &vf));
            },
            (Value::VecIndex(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::G2(C::G2Ops::vec_dot(b, &vf));
            },
            (Value::VecIndex(a), Value::VecGT(b))
            | (Value::VecGT(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::GT(C::POps::vec_dot(b, &vf));
            },
            (Value::VecScalar(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecScalar(a)) =>
                *other = Value::G1(C::G1Ops::vec_dot(b, a)),
            (Value::VecScalar(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecScalar(a)) =>
                *other = Value::G2(C::G2Ops::vec_dot(b, a)),
            (Value::VecScalar(a), Value::VecGT(b))
            | (Value::VecGT(b), Value::VecScalar(a)) =>
                *other = Value::GT(C::POps::vec_dot(b, a)),
            (Value::VecIndex(_), Value::VecG1(b))
            | (Value::VecG1(b), Value::VecIndex(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG1Affine(vg), other);
            },
            (Value::VecIndex(_), Value::VecG2(b))
            | (Value::VecG2(b), Value::VecIndex(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG2Affine(vg), other);
            },
            (Value::VecScalar(_), Value::VecG1(b))
            | (Value::VecG1(b), Value::VecScalar(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG1Affine(vg), other);
            },
            (Value::VecScalar(_), Value::VecG2(b))
            | (Value::VecG2(b), Value::VecScalar(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG2Affine(vg), other);
            }
            (Value::VecIndex(a), Value::VecIndex(b)) =>
                *other = Value::Index(a.par_iter()
                    .zip(b.par_iter())
                    .map(|(a, b)| *a * *b)
                    .sum()),
            (Value::VecIndex(v), _) => {
                let vl = v.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecScalar(vl), other);
            },
            (Value::VecScalar(v), _) => {
                let vf = other.into_vec_scalar_mut();
                *other = Value::Scalar(
                    (*vf).par_iter()
                        .zip(v.par_iter())
                        .map(|(a, b)| {
                            let mut a = *a;
                            C::FOps::mul(b, &mut a);
                            a
                        }).reduce(
                            || C::FOps::zero(),
                            |mut a, b| {
                                C::FOps::add(&b, &mut a);
                                a
                            }
                        ));
            }
            (Value::VecG1(a), Value::VecG2(b))
            | (Value::VecG2(b), Value::VecG1(a)) =>
                *other = Value::GT(
                    a.par_iter()
                    .zip(b.par_iter())
                    .map(|(a, b)|
                        C::POps::billinear_map(a, b))
                    .reduce(|| C::POps::zero(), |mut a, b| {
                        C::POps::add(&b, &mut a);
                        a
                    })),
            (Value::Vec(a), _) =>
                a.par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_dot(b)),
            (a, b) => panic!("Mismatched values {} . {}", a, b)
        }
    }

    #[inline]
    pub fn dot(self, other: Self) -> Self {
        let mut other = other;
        self.value_dot(&mut other);
        other
    }

    #[inline]
    pub fn value_and(&self, other: &mut Self) {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => *b = *a && *b,
            (Value::VecBool(a), Value::VecBool(b)) => {
                *b = a.par_iter().zip(b.par_iter()).map(|(a, b)| *a && *b).collect();
            },
            (a, b) => panic!("Cannot AND {} and {}", a, b)
        }
    }

    #[inline]
    pub fn value_or(&self, other: &mut Self) {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => *b = *a || *b,
            (Value::VecBool(a), Value::VecBool(b)) => {
                *b = a.par_iter().zip(b.par_iter()).map(|(a, b)| *a || *b).collect();
            },
            (a, b) => panic!("Cannot OR {} and {}", a, b)
        }
    }

    #[inline]
    pub fn value_not(&self) -> Self {
        match self {
            Value::Bool(a) => Value::Bool(!*a),
            Value::VecBool(a) => Value::VecBool(a.iter().map(|a| !*a).collect()),
            a => panic!("Cannot NOT {}", a)
        }
    }

    /// Value equality
    #[inline]
    pub fn value_equ(a: &Self, other: &Self) -> bool {
        match (a, other) {
            (Value::Bool(a), Value::Bool(b)) => *a == *b,
            (Value::VecBool(a), Value::VecBool(b)) => a == b,
            (Value::Index(a), Value::Index(b)) => *a == *b,
            (Value::Scalar(a), Value::Scalar(b)) => a == b,
            (Value::Scalar(a), Value::Index(b)) => *a == (*b).into(),
            (Value::Index(a), Value::Scalar(b)) => <u64 as Into<C::F>>::into(*a) == *b,
            (Value::VecIndex(a), Value::VecIndex(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| *a == *b),
            (Value::VecScalar(a), Value::VecScalar(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| *a == *b),
            (Value::VecIndex(a), Value::VecScalar(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| <u64 as Into<C::F>>::into(*a) == *b),
            (Value::VecScalar(a), Value::VecIndex(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| <u64 as Into<C::F>>::into(*b) == *a),
            (Value::G1(a), Value::G1(b)) => a == b,
            (Value::G2(a), Value::G2(b)) => a == b,
            (Value::GT(a), Value::GT(b)) => a == b,
            (Value::G1Affine(a), Value::G1(b))
            | (Value::G1(b), Value::G1Affine(a)) => a == &b.into_affine(),
            (Value::G2Affine(a), Value::G2(b))
            | (Value::G2(b), Value::G2Affine(a)) => a == &b.into_affine(),
            (Value::VecG1(a), Value::VecG1(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b),
            (Value::VecG2(a), Value::VecG2(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b),
            (Value::VecGT(a), Value::VecGT(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b),
            (Value::VecG1(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecG1(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| &a.into_affine() == b),
            (Value::VecG2(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecG2(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| &a.into_affine() == b),
            (Value::Vec(a), Value::Vec(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, b)),
            (Value::Vec(a), Value::VecScalar(b))
            | (Value::VecScalar(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::Scalar(*b))),
            (Value::Vec(a), Value::VecIndex(b))
            | (Value::VecIndex(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::Index(*b))),
            (Value::Vec(a), Value::VecG1(b))
            | (Value::VecG1(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::G1(*b))),
            (Value::Vec(a), Value::VecG2(b))
            | (Value::VecG2(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::G2(*b))),
            (Value::Vec(a), Value::VecGT(b))
            | (Value::VecGT(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::GT(*b))),
            (Value::Vec(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::G1Affine(*b))),
            (Value::Vec(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::Vec(a)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| Value::value_equ(a, &Value::G2Affine(*b))),
            (a, b) => panic!("Cannot compare {} == {}", a, b)
        }
    }

    /// TODO: How do I sample the hasher state?
    pub fn value_challenge<H: Hasher>(typ: &ATyp, h: &mut H) -> Self {
        // TODO: Use spongefish to hash and generate challenges
        unimplemented!();
    }

    pub fn ram(self, r: Self) -> Self {
        match (self, r) {
            (Value::VecIndex(a), Value::VecIndex(b)) =>
                Value::VecIndex(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecIndex(a), Value::Index(b)) =>
                Value::Index(a[b as usize].clone()),
            (Value::VecScalar(a), Value::VecIndex(b)) =>
                Value::VecScalar(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecScalar(a), Value::Index(b)) =>
                Value::Scalar(a[b as usize].clone()),
            (Value::VecG1(a), Value::VecIndex(b)) =>
                Value::VecG1(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecG1(a), Value::Index(b)) =>
                Value::G1(a[b as usize].clone()),
            (Value::VecG2(a), Value::VecIndex(b)) =>
                Value::VecG2(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecG2(a), Value::Index(b)) =>
                Value::G2(a[b as usize].clone()),
            (Value::VecGT(a), Value::VecIndex(b)) =>
                Value::VecGT(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecGT(a), Value::Index(b)) =>
                Value::GT(a[b as usize].clone()),
            (Value::VecG1Affine(a), Value::VecIndex(b)) =>
                Value::VecG1Affine(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecG1Affine(a), Value::Index(b)) =>
                Value::G1Affine(a[b as usize].clone()),
            (Value::VecG2Affine(a), Value::VecIndex(b)) =>
                Value::VecG2Affine(b.par_iter().map(|i| a[*i as usize]).collect()),
            (Value::VecG2Affine(a), Value::Index(b)) =>
                Value::G2Affine(a[b as usize].clone()),
            (Value::Vec(a), Value::VecIndex(b)) =>
                Value::Vec(b.par_iter().map(|i| a[*i as usize].clone()).collect()),
            (Value::Vec(a), Value::Index(b)) =>
                a[b as usize].clone(),
            (Value::Vec(a), Value::Vec(b)) =>
                Value::Vec(b.par_iter().map(|i| a[i.into_index() as usize].clone()).collect()),
            (a, b) => panic!("Cannot do {}[{}]", a, b)

        }
    }

    pub fn concat(self, r: &mut Self) {
        match &self {
            Value::VecScalar(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_scalar_mut());
                *r = Value::VecScalar(a);
            },
            Value::VecG1(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g1_mut());
                *r = Value::VecG1(a);
            },
            Value::VecG2(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g2_mut());
                *r = Value::VecG2(a);
            },
            Value::VecGT(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_gt_mut());
                *r = Value::VecGT(a);
            },
            Value::VecG1Affine(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g1_affine_mut());
                *r = Value::VecG1Affine(a);
            },
            Value::VecG2Affine(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g2_affine_mut());
                *r = Value::VecG2Affine(a);
            },
            Value::VecBool(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_bool_mut());
                *r = Value::VecBool(a);
            },
            Value::VecIndex(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_index_mut());
                *r = Value::VecIndex(a);
            },
            Value::Scalar(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_scalar_mut());
                *r = Value::VecScalar(a);
            },
            Value::G1(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g1_mut());
                *r = Value::VecG1(a);
            },
            Value::G2(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g2_mut());
                *r = Value::VecG2(a);
            },
            Value::GT(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_gt_mut());
                *r = Value::VecGT(a);
            },
            Value::G1Affine(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g1_affine_mut());
                *r = Value::VecG1Affine(a);
            },
            Value::G2Affine(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g2_affine_mut());
                *r = Value::VecG2Affine(a);
            },
            Value::Bool(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_bool_mut());
                *r = Value::VecBool(a);
            },
            Value::Index(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_index_mut());
                *r = Value::VecIndex(a);
            },
            Value::Vec(a) =>
                match &r {
                    Value::Vec(_) => {
                        let mut a = a.clone();
                        a.append(r.into_vec_mut());
                        *r = Value::Vec(a);
                    },
                    Value::VecBool(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_bool_mut().append(r.into_vec_bool_mut());
                        *r = slf;
                    },
                    Value::VecScalar(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_scalar_mut().append(r.into_vec_scalar_mut());
                        *r = slf;
                    },
                    Value::VecG1(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_g1_mut().append(r.into_vec_g1_mut());
                        *r = slf;
                    },
                    Value::VecG2(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_g2_mut().append(r.into_vec_g2_mut());
                        *r = slf;
                    },
                    Value::VecGT(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_gt_mut().append(r.into_vec_gt_mut());
                        *r = slf;
                    },
                    Value::VecG1Affine(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_g1_affine_mut().append(r.into_vec_g1_affine_mut());
                        *r = slf;
                    },
                    Value::VecG2Affine(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_g2_affine_mut().append(r.into_vec_g2_affine_mut());
                        *r = slf;
                    },
                    Value::VecIndex(_) => {
                        let mut slf = self.clone();
                        slf.into_vec_index_mut().append(r.into_vec_index_mut());
                        *r = slf;
                    },
                    _ => {
                        let mut a = a.clone();
                        a.push(r.clone());
                        *r = Value::Vec(a);
                    }
            }
        }
    }

    /// Generate a random value, given some parameters
    pub fn random<R: Rng + Sized>(rng: &mut R, typ: &ATyp) -> Self {
        match typ {
            ATyp::Bool => Value::Bool(rng.next_u32() % 2 == 0),
            ATyp::Fin(r) => Value::Index(r.random(rng) as u64),
            ATyp::Scalar => Value::Scalar(C::FOps::rand(rng)),
            ATyp::G1 => Value::G1(C::G1Ops::rand(rng)),
            ATyp::G2 => Value::G2(C::G2Ops::rand(rng)),
            ATyp::G1Affine => Value::G1Affine(C::G1Ops::rand(rng).into_affine()),
            ATyp::G2Affine => Value::G2Affine(C::G2Ops::rand(rng).into_affine()),
            ATyp::GT => Value::GT(C::POps::rand(rng)),
            ATyp::Vec(box ATyp::Fin(r), n) => Value::VecIndex((0..*n).map(|_| r.random(rng) as u64).collect()),
            ATyp::Vec(box ATyp::Scalar, n) => Value::VecScalar(C::FOps::vec_rand(rng, *n as usize)),
            ATyp::Vec(box ATyp::G1, n) => Value::VecG1(C::G1Ops::vec_rand(rng, *n as usize)),
            ATyp::Vec(box ATyp::G2, n) => Value::VecG2(C::G2Ops::vec_rand(rng, *n as usize)),
            ATyp::Vec(box ATyp::GT, n) => Value::VecGT(C::POps::vec_rand(rng, *n as usize)),
            ATyp::Vec(box ATyp::G1Affine, n) =>
                Value::VecG1Affine(C::G1Ops::vec_rand(rng, *n).into_iter().map(|a| a.into()).collect()),
            ATyp::Vec(box ATyp::G2Affine, n) =>
                Value::VecG2Affine(C::G2Ops::vec_rand(rng, *n).into_iter().map(|a| a.into()).collect()),
            ATyp::Vec(box t, n) => Value::Vec((0..*n).map(|_| Self::random(rng, &t)).collect()),
        }
    }

    pub fn typ(&self) -> ATyp {
        match self {
            Value::Bool(_) => ATyp::Bool,
            Value::VecBool(v) => ATyp::Vec(Box::new(ATyp::Bool), v.len()),
            Value::Index(n) => ATyp::Fin(Range::singleton(*n as usize)),
            Value::Scalar(_) => ATyp::Scalar,
            Value::G1(_) => ATyp::G1,
            Value::G2(_) => ATyp::G2,
            Value::G1Affine(_) => ATyp::G1,
            Value::G2Affine(_) => ATyp::G2,
            Value::GT(_) => ATyp::GT,
            Value::VecScalar(v) => ATyp::vec(&ATyp::Scalar, v.len()),
            Value::VecG1(v) => ATyp::vec(&ATyp::G1, v.len()),
            Value::VecG2(v) => ATyp::vec(&ATyp::G2, v.len()),
            Value::VecG1Affine(v) => ATyp::vec(&ATyp::G1Affine, v.len()),
            Value::VecG2Affine(v) => ATyp::vec(&ATyp::G2Affine, v.len()),
            Value::VecGT(v) => ATyp::vec(&ATyp::GT, v.len()),
            Value::VecIndex(v) => {
                let min = *v.iter().min().unwrap() as usize;
                let max = *v.iter().max().unwrap() as usize;
                ATyp::Vec(Box::new(ATyp::Fin(Range::new(min, max))), v.len())
            },
            Value::Vec(v) => {
                    let typ = v[0].typ();
                    for i in v.iter().skip(1) {
                        if typ != i.typ() {
                            panic!("Mismatched types in vector {} and {}", typ, i.typ());
                        }
                    }
                    ATyp::Vec(Box::new(typ), v.len())
                }
        }
    }

    /// Dynamic casts
    pub fn into_scalar(&self) -> C::F {
        match self {
            Value::Scalar(f) => *f,
            Value::Index(i) => (*i).into(),
            _ => panic!("Expected scalar, found {}", self),
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

    pub fn into_g1_mut(&mut self) -> &mut C::G1 {
        match self {
            Value::G1(g) => g,
            Value::G1Affine(g) => {
                *self = Value::G1((*g).into());
                self.into_g1_mut()
            },
            _ => panic!("Expected mut group1, found {}", self),
        }
    }
    pub fn into_g2_mut(&mut self) -> &mut C::G2 {
        match self {
            Value::G2(g) => g,
            Value::G2Affine(g) => {
                *self = Value::G2((*g).into());
                self.into_g2_mut()
            },
            _ => panic!("Expected mut group2, found {}", self),
        }
    }
    pub fn into_gt_mut(&mut self) -> &mut PairingOutput<C::P> {
        match self {
            Value::GT(g) => g,
            _ => panic!("Expected mut groupt, found {}", self),
        }
    }
    pub fn into_g1_affine_mut(&mut self) -> &mut C::G1Affine {
        match self {
            Value::G1(g) => {
                *self = Value::G1Affine((*g).into());
                self.into_g1_affine_mut()
            },
            Value::G1Affine(g) => g,
            _ => panic!("Expected mut group1, found {}", self),
        }
    }
    pub fn into_g2_affine_mut(&mut self) -> &mut C::G2Affine {
        match self {
            Value::G2(g) => {
                *self = Value::G2Affine((*g).into());
                self.into_g2_affine_mut()
            },
            Value::G2Affine(g) => g,
            _ => panic!("Expected mut group2, found {}", self),
        }
    }
    pub fn into_vec_scalar_mut(&mut self) -> &mut Vec<C::F> {
        match self {
            Value::VecScalar(v) => v,
            Value::VecIndex(v) => {
                *self = Value::VecScalar(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_scalar_mut()
            },
            Value::Vec(v) => {
                *self = Value::VecScalar(v.par_iter().map(|v| v.into_scalar()).collect());
                self.into_vec_scalar_mut()
            },
            _ => panic!("Expected mut vec scalar, found {}", self),
        }
    }

    #[inline]
    pub fn into_vec_mut(&mut self) -> &mut Vec<Self> {
        match self {
            Value::Vec(v) => v,
            Value::VecIndex(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::Index(*i)).collect());
                self.into_vec_mut()
            },
            Value::VecG1(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G1(*i)).collect());
                self.into_vec_mut()
            },
            Value::VecG2(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G2(*i)).collect());
                self.into_vec_mut()
            },
            Value::VecGT(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::GT(*i)).collect());
                self.into_vec_mut()
            },
            Value::VecG1Affine(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G1Affine(*i)).collect());
                self.into_vec_mut()
            },
            Value::VecG2Affine(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G2Affine(*i)).collect());
                self.into_vec_mut()
            },
            Value::VecBool(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::Bool(*i)).collect());
                self.into_vec_mut()
            },
            _ => panic!("Expected mut vec, found {}", self),
        }
    }

    pub fn into_vec_g1_mut(&mut self) -> &mut Vec<C::G1> {
        match self {
            Value::VecG1(v) => v,
            Value::VecG1Affine(v) => {
                *self = Value::VecG1(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g1_mut()
            },
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }
    pub fn into_vec_g2_mut(&mut self) -> &mut Vec<C::G2> {
        match self {
            Value::VecG2(v) => v,
            Value::VecG2Affine(v) => {
                *self = Value::VecG2(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g2_mut()
            },
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }
    pub fn into_vec_gt_mut(&mut self) -> &mut Vec<PairingOutput<C::P>> {
        match self {
            Value::VecGT(v) => v,
            _ => panic!("Expected mut vec groupt, found {}", self),
        }
    }
    pub fn into_vec_g1_affine_mut(&mut self) -> &mut Vec<C::G1Affine> {
        match self {
            Value::VecG1Affine(v) => v,
            Value::VecG1(v) => {
                *self = Value::VecG1Affine(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g1_affine_mut()
            },
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }
    pub fn into_vec_g2_affine_mut(&mut self) -> &mut Vec<C::G2Affine> {
        match self {
            Value::VecG2Affine(v) => v,
            Value::VecG2(v) => {
                *self = Value::VecG2Affine(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g2_affine_mut()
            },
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }
    pub fn into_vec_bool_mut(&mut self) -> &mut Vec<bool> {
        match self {
            Value::VecBool(v) => v,
            _ => panic!("Expected mut vec bool, found {}", self),
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

    pub fn is_vec(&self) -> bool {
        match self {
            Value::Vec(_) => true,
            Value::VecBool(_) => true,
            Value::VecScalar(_) => true,
            Value::VecG1(_) => true,
            Value::VecG2(_) => true,
            Value::VecGT(_) => true,
            Value::VecG1Affine(_) => true,
            Value::VecG2Affine(_) => true,
            Value::VecIndex(_) => true,
            _ => false,
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Value::Scalar(a) => a.is_zero(),
            Value::Index(a) => *a == 0,
            Value::Bool(a) => !*a,
            Value::G1(a) => a.is_zero(),
            Value::G2(a) => a.is_zero(),
            Value::GT(a) => a.is_zero(),
            Value::G1Affine(a) => a.is_zero(),
            Value::G2Affine(a) => a.is_zero(),
            Value::VecScalar(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG1(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG2(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecGT(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG1Affine(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG2Affine(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecIndex(a) => a.par_iter().all(|a| *a == 0),
            Value::VecBool(a) => a.par_iter().all(|a| !*a),
            Value::Vec(a) => a.par_iter().all(|a| a.is_zero()),
        }
    }
}

impl<C: ArkConfig> AddAssign for Value<C> {
    fn add_assign(&mut self, other: Self) {
        other.value_add(self);
    }
}

impl<C: ArkConfig> MulAssign for Value<C> {
    fn mul_assign(&mut self, other: Self) {
        other.value_mul(self);
    }
}

impl<C: ArkConfig> Add for Value<C> {
    type Output = Value<C>;

    fn add(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_add(&mut other);
        other
    }
}

impl<C: ArkConfig> Sub for Value<C> {
    type Output = Value<C>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_sub(&mut other);
        other
    }
}

impl<C: ArkConfig> Mul for Value<C> {
    type Output = Value<C>;

    fn mul(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_mul(&mut other);
        other
    }
}

impl<C: ArkConfig> Div for Value<C> {
    type Output = Value<C>;

    fn div(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_div(&mut other);
        other
    }
}

impl<C: ArkConfig> Rem for Value<C> {
    type Output = Value<C>;

    fn rem(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_rem(&mut other);
        other
    }
}

impl<C: ArkConfig> BitXor for Value<C> {
    type Output = Value<C>;

    fn bitxor(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_pow(&mut other);
        other
    }
}

impl<C: ArkConfig> BitAnd for Value<C> {
    type Output = Value<C>;

    fn bitand(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_and(&mut other);
        other
    }
}

impl<C: ArkConfig> BitOr for Value<C> {
    type Output = Value<C>;

    fn bitor(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_or(&mut other);
        other
    }
}

impl<C: ArkConfig> Add for &Value<C> {
    type Output = Value<C>;

    fn add(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_add(&mut other);
        other
    }
}

impl<C: ArkConfig> Sub for &Value<C> {
    type Output = Value<C>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_sub(&mut other);
        other
    }
}

impl<C: ArkConfig> Mul for &Value<C> {
    type Output = Value<C>;

    fn mul(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_mul(&mut other);
        other
    }
}

impl<C: ArkConfig> Div for &Value<C> {
    type Output = Value<C>;

    fn div(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_div(&mut other);
        other
    }
}

impl<C: ArkConfig> Rem for &Value<C> {
    type Output = Value<C>;

    fn rem(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_rem(&mut other);
        other
    }
}

impl<C: ArkConfig> BitXor for &Value<C> {
    type Output = Value<C>;
    fn bitxor(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_pow(&mut other);
        other
    }
}

impl<C: ArkConfig> BitAnd for &Value<C> {
    type Output = Value<C>;

    fn bitand(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_and(&mut other);
        other
    }
}

impl<C: ArkConfig> BitOr for &Value<C> {
    type Output = Value<C>;

    fn bitor(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_or(&mut other);
        other
    }
}

impl<C: ArkConfig> fmt::Display for Value<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::VecBool(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            },
            Value::Index(i) => write!(f, "{}", i),
            Value::Scalar(a) => C::FOps::write(a, f),
            Value::G1(a) => C::G1Ops::write(a, f),
            Value::G2(g) => C::G2Ops::write(g, f),
            Value::G1Affine(a) => C::G1Ops::write(&(*a).into(), f),
            Value::G2Affine(g) => C::G2Ops::write(&(*g).into(), f),
            Value::GT(g) => C::POps::write(g, f),
            Value::VecScalar(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            },
            Value::VecG1(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G1Ops::write(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecG2(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G2Ops::write(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecG1Affine(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G1Ops::write(&(*i).into(), f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecG2Affine(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G2Ops::write(&(*i).into(), f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            },
            Value::VecGT(v) => {
                write!(f, "[")?;
                for i in v {
                    C::POps::write(i, f)?;
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
            Value::Vec(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            },
        }
    }
}

#[cfg(test)] use crate::ArkBls12_381;
#[cfg(test)] use share::assert_deq;
#[cfg(test)] use ark_std::test_rng;

// Commutativity of addition
#[test]
fn test_value_add_comm() {
    // Scalar + Scalar
    let mut rng = test_rng();
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Scalar);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Scalar);
    assert_deq!(&a + &b, &b + &a);

    // Group1 + Group1
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G1);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G1);
    assert_deq!(&a + &b, &b + &a);

    // Group2 + Group2
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G2);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G2);
    assert_deq!(&a + &b, &b + &a);

    // GT + GT
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::GT);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::GT);
    assert_deq!(&a + &b, &b + &a);

    // Vec<Scalar> + Vec<Scalar>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Scalar), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Scalar), 10));
    assert_deq!(&a + &b, &b + &a);

    // Vec<Index> + Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Fin(Range::singleton(10))), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Fin(Range::singleton(10))), 10));
    assert_deq!(&a + &b, &b + &a);

    // Vec<Scalar> + Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Scalar), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Fin(Range::singleton(10))), 10));
    assert_deq!(&a + &b, &b + &a);

    // G1 + G1Affine
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G1);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G1Affine);
    assert_deq!(&a + &b, &b + &a);
}

// Commutativity of multiplication
#[test]
fn test_value_mul_comm() {
    // Scalar * Scalar
    let mut rng = test_rng();
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Scalar);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Scalar);
    assert_deq!(&a * &b, &b * &a);

    // Vec<Scalar> * Vec<Scalar>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Scalar), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Scalar), 10));
    assert_deq!(&a * &b, &b * &a);

    // Vec<Index> * Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Fin(Range::singleton(10))), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Fin(Range::singleton(10))), 10));
    assert_deq!(&a * &b, &b * &a);

    // Vec<Scalar> * Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Scalar), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::Fin(Range::singleton(10))), 10));
    assert_deq!(&a * &b, &b * &a);

    // G1 * G2
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G1);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G2);
    assert_deq!(&a * &b, &b * &a);

    // G1Affine * G2Affine
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G1Affine);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::G2Affine);
    assert_deq!(&a * &b, &b * &a);

    // Vec<G1> * Vec<G2Affine>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::G1), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::G2Affine), 10));
    assert_deq!(&a * &b, &b * &a);
}


