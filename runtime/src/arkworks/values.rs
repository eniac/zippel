use ark_ec::pairing::PairingOutput;
use ark_ff::Field;
use rayon::prelude::*;
use rand::Rng;
use std::fmt;
use core::hash::{Hash, Hasher};
use std::ops::{Add, Sub, Mul, Div};
use ark_ec::CurveGroup;
use ark_ec::hashing::map_to_curve_hasher::MapToCurveBasedHasher;

use crate::arkworks::config::{ArkConfig, ArkScalarOps, ArkGroupOps, ArkPairingOps};
use crate::typ::{RTyp, RBase};

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
                    Value::VecG2(_) =>
                        *other = Value::GT(C::POps::billinear_vec_mul(&vec![*a], other.into_vec_g2_mut())[0]),
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
                    Value::VecG1(_) =>
                        *other = Value::GT(C::POps::billinear_vec_mul(other.into_vec_g1_mut(), &vec![*a])[0]),
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
                    // Vec<Index> * Vec<Index> = Vec<Index>
                    Value::VecIndex(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b)),
                    // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                    Value::VecScalar(_) =>
                        v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b)),
                    // Vec<Index> * Vec<Group1> = Vec<Group1>
                    Value::VecG1(_) | Value::VecG1Affine(_) =>
                        v.par_iter()
                        .zip(other.into_vec_g1_mut().par_iter_mut())
                        .for_each(|(a, b)| C::G1Ops::mul(a, b)),
                    // Vec<Index> * Vec<G2> = Vec<G2>
                    Value::VecG2(_) | Value::VecG2Affine(_) =>
                        v.par_iter()
                        .zip(other.into_vec_g2_mut().par_iter_mut())
                        .for_each(|(a, b)| C::G2Ops::mul(a, b)),
                    // Vec<Index> * Vec<GT> = Vec<GT>
                    Value::VecGT(_) =>
                        v.par_iter()
                        .zip(other.into_vec_gt_mut().par_iter_mut())
                        .for_each(|(a, b)| C::POps::mul(a, b)),
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
                    _ => panic!("Expected scalar, found {}", other)
                },
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
                    _ => panic!("Expected scalar, found {}", other)
                },
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
            (a, b) => panic!("Mismatched values {} . {}", a, b)
        }
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
            (Value::G1Affine(a), Value::G1(b)) => a == &b.into_affine(),
            (Value::G2Affine(a), Value::G2(b)) => a == &b.into_affine(),
            (Value::G1(a), Value::G1Affine(b)) => &a.into_affine() == b,
            (Value::G2(a), Value::G2Affine(b)) => &a.into_affine() == b,
            (Value::VecG1(a), Value::VecG1(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b),
            (Value::VecG2(a), Value::VecG2(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b),
            (Value::VecGT(a), Value::VecGT(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b),
            (Value::VecG1(a), Value::VecG1Affine(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| &a.into_affine() == b),
            (Value::VecG1Affine(a), Value::VecG1(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == &b.into_affine()),
            (Value::VecG2(a), Value::VecG2Affine(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| &a.into_affine() == b),
            (Value::VecG2Affine(a), Value::VecG2(b)) =>
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == &b.into_affine()),
            (a, b) => panic!("Cannot compare {} == {}", a, b)
        }
    }

    /// Random
    #[inline]
    pub fn value_rand<R: Rng + Sized>(rng: &mut R, typ: RTyp) -> Self {
        match typ {
            RTyp::Base(RBase::Index) => Value::Index(rng.next_u64()),
            RTyp::Base(RBase::Scalar) => Value::Scalar(C::FOps::rand(rng)),
            RTyp::Base(RBase::G1) => Value::G1(C::G1Ops::rand(rng)),
            RTyp::Base(RBase::G2) => Value::G2(C::G2Ops::rand(rng)),
            RTyp::Base(RBase::GT) => Value::GT(C::POps::rand(rng)),
            RTyp::Vec(RBase::Index, n) => Value::VecIndex((0..n).map(|_| rng.next_u64()).collect()),
            RTyp::Vec(RBase::Scalar, n) => Value::VecG1(C::G1Ops::vec_rand(rng, n)),
            RTyp::Vec(RBase::G1, n) => Value::VecG1(C::G1Ops::vec_rand(rng, n)),
            RTyp::Vec(RBase::G2, n) => Value::VecG2(C::G2Ops::vec_rand(rng, n)),
            RTyp::Vec(RBase::GT, n) => Value::VecGT(C::POps::vec_rand(rng, n)),
        }
    }

    /// TODO: How do I sample the hasher state?
    pub fn value_challenge<H: Hasher>(typ: &RTyp, h: &mut H) -> Self {
        // TODO: Use spongefish to hash and generate challenges
        unimplemented!();
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
                *self = Value::VecScalar(v.iter().map(|i| (*i).into()).collect());
                self.into_vec_scalar_mut()
            },
            _ => panic!("Expected mut vec scalar, found {}", self),
        }
    }
    pub fn into_vec_g1_mut(&mut self) -> &mut Vec<C::G1> {
        match self {
            Value::VecG1(v) => v,
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }
    pub fn into_vec_g2_mut(&mut self) -> &mut Vec<C::G2> {
        match self {
            Value::VecG2(v) => v,
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }
    pub fn into_vec_gt_mut(&mut self) -> &mut Vec<PairingOutput<C::P>> {
        match self {
            Value::VecGT(v) => v,
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

    /// Generate a random value, given some parameters
    pub fn generate_value<R: Rng + Sized>(rng: &mut R, value: usize, e: usize) -> Self {
        if e == 0 {
            match value {
                0 => Value::Scalar(C::FOps::rand(rng)),
                1 => Value::G1(C::G1Ops::rand(rng)),
                2 => Value::G2(C::G2Ops::rand(rng)),
                3 => Value::GT(C::POps::rand(rng)),
                4 => Value::G1Affine(C::G1Ops::rand(rng).into()),
                5 => Value::G2Affine(C::G2Ops::rand(rng).into()),
                _ => Value::Index(rng.next_u64()),
            }
        } else {
            match value {
                0 => Value::VecScalar(C::FOps::vec_rand(rng, e)),
                1 => Value::VecG1(C::G1Ops::vec_rand(rng, e)),
                2 => Value::VecG2(C::G2Ops::vec_rand(rng, e)),
                3 => Value::VecGT(C::POps::vec_rand(rng, e)),
                4 => Value::VecG1Affine(C::G1Ops::vec_rand(rng, e).into_iter().map(|a| a.into()).collect()),
                5 => Value::VecG2Affine(C::G2Ops::vec_rand(rng, e).into_iter().map(|a| a.into()).collect()),
                _ => Value::VecIndex((0..e).map(|_| rng.next_u64()).collect()),
            }
        }
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
        }
    }
}

impl<C: ArkConfig> Hash for Value<C> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        match self {
            Value::Bool(b) => h.write_u8(*b as u8),
            Value::VecBool(v) => v.iter().for_each(|b| h.write_u8(*b as u8)),
            Value::Index(i) => h.write_u64(*i),
            Value::Scalar(s) => C::FOps::hash(s, h),
            Value::G1(g) => C::G1Ops::hash(g, h),
            Value::G2(g) => C::G2Ops::hash(g, h),
            Value::GT(g) => C::POps::hash(g, h),
            Value::G1Affine(g) => C::G1Ops::hash(&(*g).into(), h),
            Value::G2Affine(g) => C::G2Ops::hash(&(*g).into(), h),
            Value::VecScalar(v) => C::FOps::vec_hash(v, h),
            Value::VecIndex(v) => v.iter().for_each(|i| h.write_u64(*i)),
            Value::VecG1(v) => C::G1Ops::vec_hash(v, h),
            Value::VecG2(v) => C::G2Ops::vec_hash(v, h),
            Value::VecGT(v) => C::POps::vec_hash(v, h),
            Value::VecG1Affine(v) =>
                v.iter().for_each(|g| C::G1Ops::hash(&(*g).into(), h)),
            Value::VecG2Affine(v) =>
                v.iter().for_each(|g| C::G2Ops::hash(&(*g).into(), h)),
        }
    }
}

#[cfg(test)] use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)] use ark_std::test_rng;
#[cfg(test)]
impl<'a, C: ArkConfig> Arbitrary<'a> for Value<C> {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut rng = test_rng();
        if u.arbitrary::<bool>()? {
            // Generate elements (size = 0)
            let value = u.int_in_range(0..=4)?;
            Ok(Value::generate_value(&mut rng, value, 0))
        } else {
            // Generate vectors (size > 0)
            let value = u.int_in_range(0..=6)?;
            let e = (1 as usize) << u.int_in_range(1..=6)?;
            Ok(Value::generate_value(&mut rng, value, e))
        }
    }
}
