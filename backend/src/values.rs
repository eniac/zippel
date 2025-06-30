use ark_ec::pairing::PairingOutput;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_ff::{PrimeField, Zero};
use lang::typ::{Nothing, CRange};
use crate::types::Lub;
use rand::Rng;
use rayon::prelude::*;
use spongefish::codecs::arkworks_algebra::GroupDomainSeparator;
use spongefish::{BytesToUnitSerialize, DomainSeparator, ProverState};
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, AddAssign, BitAnd, BitOr, BitXor, Div, Mul, MulAssign, Rem, Sub};

use crate::{to_bytes, ABase, ATyp, ArkConfig, ArkGroupOps, ArkPairingOps, ArkScalarOps};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value<C: ArkConfig> {
    /// Boolean
    Bool(bool),
    VecBool(Vec<bool>),
    /// Scalars
    Index(usize),
    Scalar(C::F),
    VecIndex(Vec<usize>),
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
    Vec(Vec<Value<C>>),
}

impl<C: ArkConfig> Value<C> {
    /// Returns an integer representing the constructor order.
    /// Higher values correspond to constructors defined earlier.
    pub fn discriminant_order(&self) -> u8 {
        match self {
            Value::Bool(_) => 17,
            Value::VecBool(_) => 16,
            Value::Index(_) => 15,
            Value::Scalar(_) => 14,
            Value::VecIndex(_) => 13,
            Value::VecScalar(_) => 12,
            Value::G1(_) => 10,
            Value::G2(_) => 9,
            Value::GT(_) => 8,
            Value::VecG1(_) => 7,
            Value::VecG2(_) => 6,
            Value::VecGT(_) => 5,
            Value::G1Affine(_) => 4,
            Value::G2Affine(_) => 3,
            Value::VecG1Affine(_) => 2,
            Value::VecG2Affine(_) => 1,
            Value::Vec(_) => 0,
        }
    }

    pub fn scalar_from_usize(i: usize) -> Self {
        Value::Scalar(C::FOps::from_usize(i))
    }

    pub fn zero(typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Bool) => Value::Bool(false),
            ATyp::Base(ABase::Fin(r)) if r.contains(0) => Value::Index(0),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::F::zero()),
            ATyp::Base(ABase::G1) => Value::G1(C::G1::zero()),
            ATyp::Base(ABase::G2) => Value::G2(C::G2::zero()),
            ATyp::Base(ABase::GT) => Value::GT(PairingOutput::<C::P>::zero()),
            ATyp::Vec(box ATyp::Base(ABase::Bool), n) => Value::VecBool(vec![false; *n]),
            ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n) if r.contains(0) => {
                Value::VecIndex(vec![0; *n])
            }
            ATyp::Vec(box ATyp::Base(ABase::Scalar), n) => Value::VecScalar(vec![C::F::zero(); *n]),
            ATyp::Vec(box ATyp::Base(ABase::G1), n) => Value::VecG1(vec![C::G1::zero(); *n]),
            ATyp::Vec(box ATyp::Base(ABase::G2), n) => Value::VecG2(vec![C::G2::zero(); *n]),
            ATyp::Vec(box ATyp::Base(ABase::GT), n) => {
                Value::VecGT(vec![PairingOutput::<C::P>::zero(); *n])
            }
            ATyp::Vec(box vt, n) => {
                let mut v = Vec::<Value<C>>::with_capacity(*n);
                for _ in 0..*n {
                    v.push(Value::<C>::zero(&vt));
                }
                Value::Vec(v)
            }
            _ => panic!("Cannot create zero value for type {}", typ),
        }
    }

    /// Value addition, saves result in other
    #[inline]
    pub fn value_add(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => panic!("Cannot add bools {} + {}", self, other),
            // Indexes coerce to scalars (addition)
            Value::Index(a) => match &other {
                Value::Index(_) => *other.into_index_mut() += *a,
                Value::Scalar(_) => C::FOps::add(&C::FOps::from_usize(*a), other.into_scalar_mut()),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                Value::Index(b) => C::FOps::add(a, &mut C::FOps::from_usize(*b)),
                Value::Scalar(_) => C::FOps::add(a, other.into_scalar_mut()),
                Value::G1(other_val) => C::G1Ops::add(&(*other_val).into_affine(), self.clone().into_g1_mut()),
                _ => panic!("Expected scalar, found {}", other),
            },
            // Group addition
            Value::G1Affine(a) => C::G1Ops::add(a, other.into_g1_mut()),
            Value::G2Affine(a) => C::G2Ops::add(a, other.into_g2_mut()),
            Value::G1(a) => C::G1Ops::add(&(*a).into_affine(), other.into_g1_mut()),
            Value::G2(a) => C::G2Ops::add(&(*a).into_affine(), other.into_g2_mut()),
            Value::GT(a) => C::POps::add(a, other.into_gt_mut()),
            // The same but for vectors (scalars)
            Value::VecIndex(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_index_mut().par_iter_mut())
                    .for_each(|(a, b)| *b += *a),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::add(&C::FOps::from_usize(*a), b)),
                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecScalar(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::add(a, b)),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::add(a, b)),
                _ => panic!("Expected vec scalar, found {}", other),
            },
            Value::VecG1Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::add(a, b)),
            Value::VecG2Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::add(a, b)),
            Value::VecG1(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::add(&(*a).into_affine(), b)),
            Value::VecG2(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::add(&(*a).into_affine(), b)),
            Value::VecGT(vs) => vs
                .par_iter()
                .zip(other.into_vec_gt_mut().par_iter_mut())
                .for_each(|(a, b)| C::POps::add(a, b)),
            Value::Vec(vs) => vs
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_add(b)),
        }
    }

    #[inline]
    pub fn value_sub(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => {
                panic!("Cannot subtract bools {} - {}", self, other)
            }
            // Indexes coerce to scalars (addition)
            Value::Index(a) => match &other {
                Value::Index(b) => *other.into_index_mut() = *a - *b,
                Value::Scalar(_) => C::FOps::sub(&C::FOps::from_usize(*a), other.into_scalar_mut()),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                Value::Index(b) => C::FOps::sub(a, &mut C::FOps::from_usize(*b)),
                Value::Scalar(_) => C::FOps::sub(a, other.into_scalar_mut()),
                _ => panic!("Expected scalar, found {}", other),
            },
            // Group addition
            Value::G1Affine(a) => C::G1Ops::sub(a, other.into_g1_mut()),
            Value::G2Affine(a) => C::G2Ops::sub(a, other.into_g2_mut()),
            Value::G1(a) => C::G1Ops::sub(&(*a).into_affine(), other.into_g1_mut()),
            Value::G2(a) => C::G2Ops::sub(&(*a).into_affine(), other.into_g2_mut()),
            Value::GT(a) => C::POps::sub(a, other.into_gt_mut()),
            // The same but for vectors (scalars)
            Value::VecIndex(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_index_mut().par_iter_mut())
                    .for_each(|(a, b)| *b = *a - *b),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::sub(&C::FOps::from_usize(*a), b)),
                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecScalar(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::sub(a, b)),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::sub(a, b)),
                _ => panic!("Expected vec scalar, found {}", other),
            },
            Value::VecG1Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::sub(a, b)),
            Value::VecG2Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::sub(a, b)),
            Value::VecG1(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| C::G1Ops::sub(&(*a).into_affine(), b)),
            Value::VecG2(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| C::G2Ops::sub(&(*a).into_affine(), b)),
            Value::VecGT(vs) => vs
                .par_iter()
                .zip(other.into_vec_gt_mut().par_iter_mut())
                .for_each(|(a, b)| C::POps::sub(a, b)),
            Value::Vec(vs) => vs
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_sub(b)),
        }
    }

    #[inline]
    pub fn value_pair(&self, other: &mut Self) {
        match (self, &other) {
            (Value::G1(a), Value::G2(b))
            | (Value::G2(b), Value::G1(a)) =>
                *other = Value::GT(C::POps::billinear_map(a, b)),
            (Value::G1Affine(a), Value::G2Affine(b))
            | (Value::G2Affine(b), Value::G1Affine(a)) =>
                *other = Value::GT(C::POps::billinear_map(&(*a).into(), &(*b).into())),
            (Value::G1(a), Value::G2Affine(b)) =>
                *other = Value::GT(C::POps::billinear_map(a, &(*b).into())),
            (Value::G2(a), Value::G1Affine(b)) =>
                *other = Value::GT(C::POps::billinear_map(&(*b).into(), a)),
            (Value::G1Affine(a), Value::G2(b)) =>
                *other = Value::GT(C::POps::billinear_map(&(*a).into(), b)),
            (Value::G2Affine(a), Value::G1(b)) =>
                *other = Value::GT(C::POps::billinear_map(b, &(*a).into())),
            // Vectors
            (Value::VecG1(a), Value::VecG2(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(a, b))
            }
            (Value::VecG2(b), Value::VecG1(a)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(a, b))
            }
            (Value::VecG1Affine(a), Value::VecG2Affine(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &a.iter().map(|a| (*a).into()).collect(),
                    &b.iter().map(|b| (*b).into()).collect(),
                ))
            }
            (Value::VecG2Affine(a), Value::VecG1Affine(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &b.iter().map(|b| (*b).into()).collect(),
                    &a.iter().map(|a| (*a).into()).collect(),
                ))
            }
            (Value::VecG1(a), Value::VecG2Affine(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &a,
                    &b.iter().map(|b| (*b).into()).collect(),
                ))
            }
            (Value::VecG2(a), Value::VecG1Affine(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &b.iter().map(|b| (*b).into()).collect(),
                    &a,
                ))
            }
            (Value::VecG1Affine(a), Value::VecG2(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &a.iter().map(|a| (*a).into()).collect(),
                    &b,
                ))
            }
            (Value::VecG2Affine(a), Value::VecG1(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &b,
                    &a.iter().map(|b| (*b).into()).collect(),
                ))
            }
            _ => panic!("Cannot pair {} and {}", self, other),
        }
    }

    /// Value multiplication, saves result in other
    #[inline]
    pub fn value_mul(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => {
                panic!("Cannot multiply bools {} * {}", self, other)
            }
            Value::Index(a) => match &other {
                Value::Bool(_) | Value::VecBool(_) => {
                    panic!("Cannot multiply bools {} * {}", self, other)
                }
                // Index * Index = Index
                Value::Index(_) => {
                    *other.into_index_mut() *= *a;
                }
                // Index * whatever, cast index to scalar
                Value::Scalar(_) => {
                    C::FOps::mul(&C::FOps::from_usize(*a), other.into_scalar_mut())
                },
                // Index * groups
                Value::G1(_) | Value::G1Affine(_) => {
                    let group = other.into_g1_mut();
                    C::G1Ops::mul(&C::FOps::from_usize(*a), group);
                }
                Value::G2(_) | Value::G2Affine(_) => {
                    let group = other.into_g2_mut();
                    C::G2Ops::mul(&C::FOps::from_usize(*a), group);
                }
                Value::GT(_) => {
                    let group = other.into_gt_mut();
                    C::POps::mul(&C::FOps::from_usize(*a), group);
                }
                // Index * Vectors
                Value::VecIndex(_) => other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= *a),
                Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| C::FOps::mul(&C::FOps::from_usize(*a), b)),
                Value::VecG1(_) | Value::VecG1Affine(_) => other
                    .into_vec_g1_mut()
                    .par_iter_mut()
                    .for_each(|b| C::G1Ops::mul(&C::FOps::from_usize(*a), b)),
                Value::VecG2(_) | Value::VecG2Affine(_) => other
                    .into_vec_g2_mut()
                    .par_iter_mut()
                    .for_each(|b| C::G2Ops::mul(&C::FOps::from_usize(*a), b)),
                Value::VecGT(_) => other
                    .into_vec_gt_mut()
                    .par_iter_mut()
                    .for_each(|b| C::POps::mul(&C::FOps::from_usize(*a), b)),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
            },
            Value::Scalar(a) => match &other {
                Value::Bool(_) | Value::VecBool(_) => {
                    panic!("Cannot multiply bools {} * {}", self, other)
                }
                // Scalar * index, cast index to Scalar
                Value::Index(b) => {
                    let mut value = C::FOps::from_usize(*b);
                    C::FOps::mul(a, &mut value);
                    *other = Value::Scalar(value);
                },
                // Scalar * Scalar = Scalar
                Value::Scalar(_) => { 
                    C::FOps::mul(a, other.into_scalar_mut())
                },
                // Index * groups
                Value::G1(_) | Value::G1Affine(_) => {
                    let group = other.into_g1_mut();
                    C::G1Ops::mul(a, group);
                }
                Value::G2(_) | Value::G2Affine(_) => {
                    let group = other.into_g2_mut();
                    C::G2Ops::mul(a, group);
                }
                Value::GT(_) => {
                    let group = other.into_gt_mut();
                    C::POps::mul(a, group);
                }
                // Scalar * Vector
                Value::VecIndex(_) | Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| C::FOps::mul(a, b)),
                Value::VecG1(_) | Value::VecG1Affine(_) => other
                    .into_vec_g1_mut()
                    .par_iter_mut()
                    .for_each(|b| C::G1Ops::mul(a, b)),
                Value::VecG2(_) | Value::VecG2Affine(_) => other
                    .into_vec_g2_mut()
                    .par_iter_mut()
                    .for_each(|b| C::G2Ops::mul(a, b)),
                Value::VecGT(_) => other
                    .into_vec_gt_mut()
                    .par_iter_mut()
                    .for_each(|b| C::POps::mul(a, b)),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
            },
            Value::G1(a) => match &other {
                // Group1 * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let mut group = C::G1Ops::vec_mul(a, &vec![other.into_scalar()]);
                    *other = Value::G1Affine(group.remove(0));
                }
                // Group1 * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    *other = Value::VecG1Affine(C::G1Ops::vec_mul(a, vr));
                }
                // Group1 * Vec<T>
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                _ => panic!("Expected scalar or group2, found {}", other),
            },
            Value::G2(a) => match &other {
                // G2 * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let mut group = C::G2Ops::vec_mul(a, &vec![other.into_scalar()]);
                    *other = Value::G2Affine(group.remove(0));
                }
                // G2 * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    *other = Value::VecG2Affine(C::G2Ops::vec_mul(a, vr));
                }
                // G2 * Vec<T>
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                _ => panic!("Expected scalar or group1, found {}", other),
            },
            Value::G1Affine(a) => Self::value_mul(&Value::G1((*a).into()), other),
            Value::G2Affine(a) => Self::value_mul(&Value::G2((*a).into()), other),
            Value::GT(a) => match &other {
                // GT * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let mut vr = vec![*other.into_scalar_mut()];
                    let mut group = C::POps::vec_mul(a, &mut vr);
                    *other = Value::GT(group.remove(0));
                }
                // GT * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    *other = Value::VecGT(C::POps::vec_mul(a, vr))
                }
                // GT * Vec<T>
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecIndex(v) => match &other {
                Value::Bool(_) | Value::VecBool(_) => {
                    panic!("Cannot multiply bools {} * {}", self, other)
                }
                // Vec<Index> * Index
                Value::Index(i) => {
                    *other = Value::VecIndex(v.par_iter().map(|a| *a * *i).collect())
                }
                // Vec<Index> * Scalar
                Value::Scalar(_) => {
                    *other = Value::VecScalar(
                        std::iter::repeat(other.into_scalar())
                            .take(v.len())
                            .collect::<Vec<_>>(),
                    );
                    v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(&C::FOps::from_usize(*a), b))
                }
                // Vec<index> * Group1
                Value::G1(_) | Value::G1Affine(_) => {
                    *other = Value::VecG1Affine(C::G1Ops::vec_mul(
                        &*other.into_g1_mut(),
                        &v.par_iter()
                            .map(|a| C::FOps::from_usize(*a))
                            .collect::<Vec<_>>(),
                    ))
                }
                // Vec<index> * G2
                Value::G2(_) | Value::G2Affine(_) => {
                    *other = Value::VecG2Affine(C::G2Ops::vec_mul(
                        &*other.into_g2_mut(),
                        &v.par_iter()
                            .map(|a| C::FOps::from_usize(*a))
                            .collect::<Vec<_>>(),
                    ))
                }
                // Vec<index> * GT
                Value::GT(g) => {
                    *other = Value::VecGT(C::POps::vec_mul(
                        g,
                        &v.par_iter()
                            .map(|a| C::FOps::from_usize(*a))
                            .collect::<Vec<_>>(),
                    ))
                }
                // Vec<Index> * Vec<Index> = Vec<Index>
                Value::VecIndex(_) => v
                    .par_iter()
                    .zip(other.into_vec_index_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= *a),
                // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                Value::VecScalar(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::mul(&C::FOps::from_usize(*a), b)),
                // Vec<Index> * Vec<Group1> = Vec<Group1>
                Value::VecG1(_) | Value::VecG1Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g1_mut().par_iter_mut())
                    .for_each(|(a, b)| C::G1Ops::mul(&C::FOps::from_usize(*a), b)),
                // Vec<Index> * Vec<G2> = Vec<G2>
                Value::VecG2(_) | Value::VecG2Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g2_mut().par_iter_mut())
                    .for_each(|(a, b)| C::G2Ops::mul(&C::FOps::from_usize(*a), b)),
                // Vec<Index> * Vec<GT> = Vec<GT>
                Value::VecGT(_) => v
                    .par_iter()
                    .zip(other.into_vec_gt_mut().par_iter_mut())
                    .for_each(|(a, b)| C::POps::mul(&C::FOps::from_usize(*a), b)),
                // Vec<Index> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::Index(*a).value_mul(b)),
            },
            Value::VecScalar(v) => match &other {
                // Vec<Scalar> * Index
                Value::Index(_) | Value::Scalar(_) => {
                    *other = Value::VecScalar(
                        std::iter::repeat(other.into_scalar())
                            .take(v.len())
                            .collect::<Vec<_>>(),
                    );
                    v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| *b *= a)
                }
                // Vec<Scalar> * Group1
                Value::G1(g) => *other = Value::VecG1Affine(C::G1Ops::vec_mul(g, v)),
                // Vec<index> * G2
                Value::G2(g) => *other = Value::VecG2Affine(C::G2Ops::vec_mul(g, v)),
                // Vec<index> * GT
                Value::GT(g) => *other = Value::VecGT(C::POps::vec_mul(g, v)),
                // Vec<Scalar> * Vec<Scalar> = Vec<Scalar>
                Value::VecIndex(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::mul(a, b)),
                // Vec<Scalar> * Vec<Scalar> = Vec<Scalar>
                Value::VecScalar(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::mul(a, b)),
                // Vec<Scalar> * Vec<Group1> = Vec<Group1>
                Value::VecG1(_) | Value::VecG1Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g1_mut().par_iter_mut())
                    .for_each(|(a, b)| C::G1Ops::mul(a, b)),
                // Vec<Scalar> * Vec<G2> = Vec<G2>
                Value::VecG2(_) | Value::VecG2Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g2_mut().par_iter_mut())
                    .for_each(|(a, b)| C::G2Ops::mul(a, b)),
                // Vec<Scalar> * Vec<GT> = Vec<GT>
                Value::VecGT(_) => v
                    .par_iter()
                    .zip(other.into_vec_gt_mut().par_iter_mut())
                    .for_each(|(a, b)| C::POps::mul(a, b)),
                // Vec<Scalar> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::Scalar(*a).value_mul(b)),
                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecG1(v) => match &other {
                // Vec<Group1> * scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let a = other.into_scalar();
                    *other = Value::VecG1(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::G1Ops::mul(&a, &mut gm);
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<Group1> * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = &*other.into_vec_scalar_mut();
                    let mut vr = v.clone();
                    vl.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::G1Ops::mul(a, b));
                    *other = Value::VecG1(vr);
                }
                // Vec<Group1> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::G1(*a).value_mul(b)),
                _ => panic!("Expected scalar or group2, found {}", other),
            },
            Value::VecG2(v) => match &other {
                // Vec<G2> * scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let a = other.into_scalar();
                    *other = Value::VecG2(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::G2Ops::mul(&a, &mut gm);
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<G2> * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = &*other.into_vec_scalar_mut();
                    let mut vr = v.clone();
                    vl.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::G2Ops::mul(a, b));
                    *other = Value::VecG2(vr);
                }
                // Vec<G2> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::G2(*a).value_mul(b)),
                _ => panic!("Expected scalar or group1, found {}", other),
            },
            Value::VecG1Affine(v) => Self::value_mul(
                &Value::VecG1(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            ),
            Value::VecG2Affine(v) => Self::value_mul(
                &Value::VecG2(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            ),
            Value::VecGT(v) => match &other {
                // Vec<GT> * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let a = other.into_scalar();
                    *other = Value::VecGT(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                C::POps::mul(&a, &mut gm);
                                gm
                            })
                            .collect(),
                    );
                }
                // GT * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = &*other.into_vec_scalar_mut();
                    let mut vr = v.clone();
                    vl.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::POps::mul(a, b));
                    *other = Value::VecGT(vr);
                }
                // Vec<GT> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::GT(*a).value_mul(b)),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Vec(v) => v
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_mul(b)),
        }
    }

    /// Value division, saves result in other
    #[inline]
    pub fn value_div(&self, other: &mut Self) {
        match self {
            Value::Bool(_) | Value::VecBool(_) => {
                panic!("Cannot divide bools {} / {}", self, other)
            }
            Value::Index(a) => match &other {
                // Index / Index = Index
                Value::Index(_) => {
                    *other = Value::Index(*a / other.into_index())
                },
                // Index / whatever, cast index to scalar
                Value::Scalar(_) => C::FOps::div(&C::FOps::from_usize(*a), other.into_scalar_mut()),
                // Index / Vectors
                Value::VecIndex(_) => other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .for_each(|b| *b /= *a),
                Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| C::FOps::div(&C::FOps::from_usize(*a), b)),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_div(b)),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                // Scalar / index, cast index to Scalar
                Value::Index(b) => C::FOps::div(a, &mut C::FOps::from_usize(*b)),
                // Scalar / Scalar = Scalar
                Value::Scalar(_) => {
                    C::FOps::div(a, other.into_scalar_mut())
                },
                // Scalar / Vector
                Value::VecIndex(_) | Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| C::FOps::div(a, b)),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_div(b)),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G1(a) => match &other {
                // Group1 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = other
                        .into_scalar()
                        .inverse()
                        .expect(format!("Failed to invert scalar {}", other).as_str());
                    let mut g = *a;
                    C::G1Ops::mul(&f, &mut g);
                    *other = Value::G1(g);
                }
                // Group1 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let mut vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(&mut vr);
                    *other = Value::VecG1Affine(C::G1Ops::vec_mul(a, &vr));
                }
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_div(b)),

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G2(a) => match &other {
                // G2 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = other
                        .into_scalar()
                        .inverse()
                        .expect(format!("Failed to invert scalar {}", other).as_str());
                    let mut g = *a;
                    C::G2Ops::mul(&f, &mut g);
                    *other = Value::G2(g);
                }
                // G2 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let mut vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(&mut vr);
                    *other = Value::VecG2Affine(C::G2Ops::vec_mul(a, &vr));
                }
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_div(b)),

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G1Affine(a) => Self::value_div(&Value::G1((*a).into()), other),
            Value::G2Affine(a) => Self::value_div(&Value::G2((*a).into()), other),
            Value::GT(a) => match &other {
                // G2 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = other
                        .into_scalar()
                        .inverse()
                        .expect(format!("Failed to invert scalar {}", other).as_str());
                    let mut g = *a;
                    C::POps::mul(&f, &mut g);
                    *other = Value::GT(g);
                }
                // G2 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let mut vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(&mut vr);
                    *other = Value::VecGT(C::POps::vec_mul(a, &vr));
                }
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_div(b)),

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecIndex(v) => match &other {
                // Vec<Index> / Index
                Value::Index(i) => {
                    *other = Value::VecIndex(v.par_iter().map(|a| *a / *i).collect())
                }
                // Vec<Index> / Scalar
                Value::Scalar(_) => {
                    *other = Value::VecScalar(
                        std::iter::repeat(other.into_scalar())
                            .take(v.len())
                            .collect::<Vec<_>>(),
                    );
                    v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| C::FOps::div(&C::FOps::from_usize(*a), b));
                }
                // Vec<Index> / Vec<Index> = Vec<Index>
                Value::VecIndex(_) => v
                    .par_iter()
                    .zip(other.into_vec_index_mut().par_iter_mut())
                    .for_each(|(a, b)| *b /= *a),
                // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                Value::VecScalar(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| C::FOps::div(&C::FOps::from_usize(*a), b)),
                // Vec<Index> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::Index(*a).value_div(b)),

                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecScalar(v) => match &other {
                // Vec<Scalar> / Index
                Value::Index(_) | Value::Scalar(_) => {
                    let f = other.into_scalar_mut();
                    f.inverse()
                        .expect(format!("Failed to invert scalar {}", f).as_str());
                    let mut vr = std::iter::repeat(f.clone().inverse().unwrap())
                        .take(v.len())
                        .collect::<Vec<_>>();
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
                }
                // Vec<Scalar> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::Scalar(*a).value_div(b)),

                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecG1(v) => match &other {
                // Vec<Group1> / scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let f = other.into_scalar();
                    let f_inv = f.inverse().unwrap();
                    *other = Value::VecG1(
                        v.par_iter()
                        .map(|g| {
                            let mut gm = *g;
                            C::G1Ops::mul(&f_inv, &mut gm);
                            gm
                        })
                        .collect(), 
                    );
                }
                // Vec<Group1> / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vl);
                    let mut vr = v.clone();
                    (*vl)
                        .par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::G1Ops::mul(a, b));
                    *other = Value::VecG1(vr);
                }
                // Vec<G1> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::G1(*a).value_div(b)),

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecG2(v) => match &other {
                // Vec<Group1> / scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let f = other.into_scalar();
                    let f_inv = f.inverse().unwrap();
                    *other = Value::VecG2(
                        v.par_iter()
                        .map(|g| {
                            let mut gm = *g;
                            C::G2Ops::mul(&f_inv, &mut gm);
                            gm
                        })
                        .collect(), 
                    );
                }
                // Vec<Group1> / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vl);
                    let mut vr = v.clone();
                    (*vl)
                        .par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::G2Ops::mul(a, b));
                    *other = Value::VecG2(vr);
                }
                // Vec<G2> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::G2(*a).value_div(b)),

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecG1Affine(v) => Self::value_div(
                &Value::VecG1(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            ),
            Value::VecG2Affine(v) => Self::value_div(
                &Value::VecG2(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            ),
            Value::VecGT(v) => match &other {
                // Vec<Group1> / scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vr);
                    *other = Value::VecGT(
                        v.par_iter()
                            .zip((*vr).par_iter())
                            .map(|(g, f)| {
                                let mut gm = *g;
                                C::POps::mul(f, &mut gm);
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<Group1> / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vl);
                    let mut vr = v.clone();
                    (*vl)
                        .par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::POps::mul(a, b));
                    *other = Value::VecGT(vr);
                }
                // Vec<GT> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::GT(*a).value_div(b)),

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Vec(v) => v
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_div(b)),
        }
    }

    pub fn value_rem(&self, other: &mut Self) {
        match (self, &other) {
            (Value::Index(a), Value::Index(b)) => *other.into_index_mut() = *a % *b,
            (Value::Index(i), Value::VecIndex(_)) => {
                other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .for_each(|v| *v %= *i);
            }
            (Value::VecIndex(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| *v %= *i);
                *other = Value::VecIndex(vs);
            }
            (Value::VecIndex(vs), Value::VecIndex(_)) => {
                other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .zip(vs.par_iter())
                    .for_each(|(v, i)| *v = *i % *v);
            }
            (_, _) => panic!("Cannot do {} % {}", self, other),
        }
    }
    /// Value exponentiation, saves result in other
    pub fn value_pow(&self, other: &mut Self) {
        #[inline]
        fn pow64(a: usize, i: usize) -> usize {
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
            (Value::Index(a), Value::Index(i)) => *other.into_index_mut() = pow64(*a, *i),
            // Scalar ^ Index
            (Value::Scalar(a), Value::Index(i)) => {
                let mut a = a.clone();
                C::FOps::pow(&mut a, *i as u64);
                *other = Value::Scalar(a);
            }
            // Vec<Index> ^ Index
            (Value::VecIndex(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| *v = pow64(*v, *i));
                *other = Value::VecIndex(vs);
            }
            // Vec<Scalar> ^ Index
            (Value::VecScalar(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| C::FOps::pow(v, *i as u64));
                *other = Value::VecScalar(vs);
            }

            // Vec<T> ^ Index
            (Value::Vec(vs), Value::Index(_)) => {
                let mut vs = vs.clone();
                vs.par_iter_mut().for_each(|v| Value::value_pow(other, v));
                *other = Value::Vec(vs);
            }
            (a, b) => panic!("Mismatched values {} ^ {}", a, b),
        }
    }

    #[inline]
    pub fn value_dot(&self, other: &mut Self) {
        match (&self, &other) {
            (Value::VecIndex(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a
                    .par_iter()
                    .map(|a| C::FOps::from_usize(*a))
                    .collect::<Vec<_>>();
                *other = Value::G1(C::G1Ops::vec_dot(b, &vf));
            }
            (Value::VecIndex(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a
                    .par_iter()
                    .map(|a| C::FOps::from_usize(*a))
                    .collect::<Vec<_>>();
                *other = Value::G2(C::G2Ops::vec_dot(b, &vf));
            }
            (Value::VecIndex(a), Value::VecGT(b)) | (Value::VecGT(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a
                    .par_iter()
                    .map(|a| C::FOps::from_usize(*a))
                    .collect::<Vec<_>>();
                *other = Value::GT(C::POps::vec_dot(b, &vf));
            }
            (Value::VecScalar(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecScalar(a)) => {
                *other = Value::G1(C::G1Ops::vec_dot(b, a))
            }
            (Value::VecScalar(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecScalar(a)) => {
                *other = Value::G2(C::G2Ops::vec_dot(b, a))
            }
            (Value::VecScalar(a), Value::VecGT(b)) | (Value::VecGT(b), Value::VecScalar(a)) => {
                *other = Value::GT(C::POps::vec_dot(b, a))
            }
            (Value::VecG1(b), Value::VecIndex(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG1Affine(vg), other);
            }
            (Value::VecIndex(_), Value::VecG1(b)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::VecG1Affine(vg);
                Self::value_dot(self, other);  
            }
            (Value::VecG2(b), Value::VecIndex(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG2Affine(vg), other);
            }
            (Value::VecG1(b), Value::VecScalar(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG1Affine(vg), other);
            }
            (Value::VecScalar(_), Value::VecG1(b)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::VecG1Affine(vg);
                Self::value_dot(self, other); 
            }
            (Value::VecG2(b), Value::VecScalar(_)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Self::value_dot(&Value::VecG2Affine(vg), other);
            }
            (Value::VecScalar(_), Value::VecG2(b)) => {
                let vg = b.par_iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::VecG2Affine(vg);
                Self::value_dot(self, other); 
            }
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                *other = Value::Index(a.par_iter().zip(b.par_iter()).map(|(a, b)| *a * *b).sum())
            }
            (Value::VecIndex(v), _) => {
                let vl = v
                    .par_iter()
                    .map(|a| C::FOps::from_usize(*a))
                    .collect::<Vec<_>>();
                Self::value_dot(&Value::VecScalar(vl), other);
            }
            (Value::VecScalar(v), _) => {
                let vf = other.into_vec_scalar_mut();
                *other = Value::Scalar(
                    (*vf)
                        .par_iter()
                        .zip(v.par_iter())
                        .map(|(a, b)| {
                            let mut a = *a;
                            C::FOps::mul(b, &mut a);
                            a
                        })
                        .reduce(
                            || C::FOps::zero(),
                            |mut a, b| {
                                C::FOps::add(&b, &mut a);
                                a
                            },
                        ),
                );
            },
            (Value::Vec(a), _) => a
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_dot(b)),
            (a, b) => panic!("Mismatched values {} . {}", a, b),
        }
    }

    #[inline]
    pub fn dot(self, other: Self) -> Self {
        let mut other = other;
        self.value_dot(&mut other);
        other
    }

    #[inline]
    pub fn value_concat(self, other: Self) -> Self {
        let mut other = other;
        self.concat(&mut other);
        other
    }

    #[inline]
    pub fn pair(self, other: Self) -> Self {
        let mut other = other;
        self.value_pair(&mut other);
        other
    }

    #[inline]
    pub fn value_and(&self, other: &mut Self) {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => *b = *a && *b,
            (Value::VecBool(a), Value::VecBool(b)) => {
                *b = a
                    .par_iter()
                    .zip(b.par_iter())
                    .map(|(a, b)| *a && *b)
                    .collect();
            }
            (a, b) => panic!("Cannot AND {} and {}", a, b),
        }
    }

    #[inline]
    pub fn value_or(&self, other: &mut Self) {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => *b = *a || *b,
            (Value::VecBool(a), Value::VecBool(b)) => {
                *b = a
                    .par_iter()
                    .zip(b.par_iter())
                    .map(|(a, b)| *a || *b)
                    .collect();
            }
            (a, b) => panic!("Cannot OR {} and {}", a, b),
        }
    }

    #[inline]
    pub fn not(&self) -> Self {
        match self {
            Value::Bool(a) => Value::Bool(!*a),
            Value::VecBool(a) => Value::VecBool(a.iter().map(|a| !*a).collect()),
            a => panic!("Cannot NOT {}", a),
        }
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        match self {
            Value::Bool(a) => *a,
            Value::VecBool(a) => a.iter().all(|a| *a),
            Value::Index(a) => *a == 1,
            Value::VecIndex(a) => a.iter().all(|a| *a == 1),
            Value::Scalar(a) => a == &C::FOps::one(),
            Value::VecScalar(a) => a.iter().all(|a| a == &C::FOps::one()),
            _ => false,
        }
    }

    /// Value equality
    #[inline]
    pub fn equ(a: &Self, other: &Self) -> bool {
        match (a, other) {
            (Value::Bool(a), Value::Bool(b)) => *a == *b,
            (Value::VecBool(a), Value::VecBool(b)) => a == b,
            (Value::Index(a), Value::Index(b)) => *a == *b,
            (Value::Scalar(a), Value::Scalar(b)) => a == b,
            (Value::Scalar(a), Value::Index(b)) => *a == C::FOps::from_usize(*b),
            (Value::Index(a), Value::Scalar(b)) => C::FOps::from_usize(*a) == *b,
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| *a == *b)
            }
            (Value::VecScalar(a), Value::VecScalar(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| *a == *b)
            }
            (Value::VecIndex(a), Value::VecScalar(b)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| C::FOps::from_usize(*a) == *b),
            (Value::VecScalar(a), Value::VecIndex(b)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| C::FOps::from_usize(*b) == *a),
            (Value::G1(a), Value::G1(b)) => a == b,
            (Value::G2(a), Value::G2(b)) => a == b,
            (Value::GT(a), Value::GT(b)) => a == b,
            (Value::G1Affine(a), Value::G1(b)) | (Value::G1(b), Value::G1Affine(a)) => {
                a == &b.into_affine()
            }
            (Value::G2Affine(a), Value::G2(b)) | (Value::G2(b), Value::G2Affine(a)) => {
                a == &b.into_affine()
            }
            (Value::VecG1(a), Value::VecG1(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b)
            }
            (Value::VecG2(a), Value::VecG2(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b)
            }
            (Value::VecGT(a), Value::VecGT(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| a == b)
            }
            (Value::VecG1(a), Value::VecG1Affine(b)) | (Value::VecG1Affine(b), Value::VecG1(a)) => {
                a.par_iter()
                    .zip(b.par_iter())
                    .all(|(a, b)| &a.into_affine() == b)
            }
            (Value::VecG2(a), Value::VecG2Affine(b)) | (Value::VecG2Affine(b), Value::VecG2(a)) => {
                a.par_iter()
                    .zip(b.par_iter())
                    .all(|(a, b)| &a.into_affine() == b)
            }
            (Value::Vec(a), Value::Vec(b)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, b)),
            (Value::Vec(a), Value::VecScalar(b)) | (Value::VecScalar(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::Scalar(*b))),
            (Value::Vec(a), Value::VecIndex(b)) | (Value::VecIndex(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::Index(*b))),
            (Value::Vec(a), Value::VecG1(b)) | (Value::VecG1(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::G1(*b))),
            (Value::Vec(a), Value::VecG2(b)) | (Value::VecG2(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::G2(*b))),
            (Value::Vec(a), Value::VecGT(b)) | (Value::VecGT(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::GT(*b))),
            (Value::Vec(a), Value::VecG1Affine(b)) | (Value::VecG1Affine(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::G1Affine(*b))),
            (Value::Vec(a), Value::VecG2Affine(b)) | (Value::VecG2Affine(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::G2Affine(*b))),
            (a, b) => panic!("Cannot compare {} == {}", a, b),
        }
    }

    pub fn value_equ(&self, other: &Self) -> Self {
        Value::Bool(Value::equ(self, other))
    }

    pub fn challenge(state: &mut ProverState) -> Self {
        Value::Scalar(C::FOps::challenge(state))
    }

    pub fn hash(&self, state: &mut ProverState) {
        match self {
            Value::Bool(b) => state.add_bytes(&to_bytes!(b).unwrap()).unwrap(),
            Value::VecBool(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::Index(i) => state.add_bytes(&to_bytes!(i).unwrap()).unwrap(),
            Value::Scalar(f) => state.add_bytes(&to_bytes!(f).unwrap()).unwrap(),
            Value::VecIndex(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::VecScalar(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::G1(g1) => state.add_bytes(&to_bytes!(g1).unwrap()).unwrap(),
            Value::G2(g2) => state.add_bytes(&to_bytes!(g2).unwrap()).unwrap(),
            Value::GT(pairing_output) => state
                .add_bytes(&to_bytes!(pairing_output).unwrap())
                .unwrap(),
            Value::VecG1(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::VecG2(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::VecGT(pairing_outputs) => state
                .add_bytes(&to_bytes!(pairing_outputs).unwrap())
                .unwrap(),
            Value::G1Affine(g1) => state.add_bytes(&to_bytes!(g1).unwrap()).unwrap(),
            Value::G2Affine(g2) => state.add_bytes(&to_bytes!(g2).unwrap()).unwrap(),
            Value::VecG1Affine(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::VecG2Affine(items) => state.add_bytes(&to_bytes!(items).unwrap()).unwrap(),
            Value::Vec(values) => values.iter().map(|v| v.hash(state)).collect(),
            _ => panic!("Cannot hash {}", self),
        }
    }
    pub fn ram(self, r: Self) -> Self {
        match (self, r) {
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                Value::VecIndex(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecIndex(a), Value::Index(b)) => Value::Index(a[b].clone()),
            (Value::VecScalar(a), Value::VecIndex(b)) => {
                Value::VecScalar(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecScalar(a), Value::Index(b)) => Value::Scalar(a[b].clone()),
            (Value::VecG1(a), Value::VecIndex(b)) => {
                Value::VecG1(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG1(a), Value::Index(b)) => {
                Value::G1(a[b].clone())
            },
            (Value::VecG2(a), Value::VecIndex(b)) => {
                Value::VecG2(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG2(a), Value::Index(b)) => {
                Value::G2(a[b].clone())
            }
            (Value::VecGT(a), Value::VecIndex(b)) => {
                Value::VecGT(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecGT(a), Value::Index(b)) => Value::GT(a[b].clone()),
            (Value::VecG1Affine(a), Value::VecIndex(b)) => {
                Value::VecG1Affine(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG1Affine(a), Value::Index(b)) => Value::G1Affine(a[b].clone()),
            (Value::VecG2Affine(a), Value::VecIndex(b)) => {
                Value::VecG2Affine(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG2Affine(a), Value::Index(b)) => Value::G2Affine(a[b].clone()),
            (Value::Vec(a), Value::VecIndex(b)) => {
                Value::Vec(b.par_iter().map(|i| a[*i].clone()).collect())
            }
            (Value::Vec(a), Value::Index(b)) => {
                a[b].clone()
            }
            (Value::Vec(a), Value::Vec(b)) => {
                Value::Vec(b.par_iter().map(|i| a[i.into_index()].clone()).collect())
            }
            (a, b) => panic!("Cannot do {}[{}]", a, b),
        }
    }

    pub fn concat(self, r: &mut Self) {
        match &self {
            Value::VecScalar(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_scalar_mut());
                *r = Value::VecScalar(a);
            }
            Value::VecG1(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g1_mut());
                *r = Value::VecG1(a);
            }
            Value::VecG2(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g2_mut());
                *r = Value::VecG2(a);
            }
            Value::VecGT(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_gt_mut());
                *r = Value::VecGT(a);
            }
            Value::VecG1Affine(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g1_affine_mut());
                *r = Value::VecG1Affine(a);
            }
            Value::VecG2Affine(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_g2_affine_mut());
                *r = Value::VecG2Affine(a);
            }
            Value::VecBool(a) => {
                let mut a = a.clone();
                a.append(r.into_vec_bool_mut());
                *r = Value::VecBool(a);
            }
            Value::VecIndex(a) => match &r {
                Value::VecIndex(vs) => {
                    let mut v = Vec::with_capacity(a.len() + vs.len());
                    a.iter().for_each(|a| v.push(*a));
                    vs.iter().for_each(|b| v.push(*b));
                    *r = Value::VecIndex(v);
                }
                Value::Index(b) => {
                    *r = Value::VecIndex(a.iter().map(|a| *a).chain(std::iter::once(*b)).collect())
                }
                Value::Vec(v) => {
                    let mut x = Vec::with_capacity(a.len() + v.len());
                    a.iter().for_each(|a| x.push(Value::Index(*a)));
                    x.extend(v.clone());
                    *r = Value::Vec(x)
                }
                Value::Scalar(b) => {
                    *r = Value::VecScalar(
                        a.iter()
                            .map(|a| C::FOps::from_usize(*a))
                            .chain(std::iter::once(*b))
                            .collect(),
                    )
                }
                Value::VecScalar(b) => {
                    let mut x = Vec::with_capacity(a.len() + b.len());
                    a.iter().for_each(|a| x.push(C::FOps::from_usize(*a)));
                    x.extend(b);
                    *r = Value::VecScalar(x)
                }
                _ => panic!("Expected vec index, found {}", r),
            },
            Value::Scalar(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_scalar_mut());
                *r = Value::VecScalar(a);
            }
            Value::G1(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g1_mut());
                *r = Value::VecG1(a);
            }
            Value::G2(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g2_mut());
                *r = Value::VecG2(a);
            }
            Value::GT(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_gt_mut());
                *r = Value::VecGT(a);
            }
            Value::G1Affine(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g1_affine_mut());
                *r = Value::VecG1Affine(a);
            }
            Value::G2Affine(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_g2_affine_mut());
                *r = Value::VecG2Affine(a);
            }
            Value::Bool(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_bool_mut());
                *r = Value::VecBool(a);
            }
            Value::Index(a) => {
                let mut a = vec![*a];
                a.append(r.into_vec_index_mut());
                *r = Value::VecIndex(a);
            }
            Value::Vec(a) => match &r {
                Value::Vec(_) => {
                    let mut a = a.clone();
                    a.append(r.into_vec_mut());
                    *r = Value::Vec(a);
                }
                Value::VecBool(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_bool_mut().append(r.into_vec_bool_mut());
                    *r = slf;
                }
                Value::VecScalar(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_scalar_mut().append(r.into_vec_scalar_mut());
                    *r = slf;
                }
                Value::VecG1(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_g1_mut().append(r.into_vec_g1_mut());
                    *r = slf;
                }
                Value::VecG2(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_g2_mut().append(r.into_vec_g2_mut());
                    *r = slf;
                }
                Value::VecGT(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_gt_mut().append(r.into_vec_gt_mut());
                    *r = slf;
                }
                Value::VecG1Affine(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_g1_affine_mut()
                        .append(r.into_vec_g1_affine_mut());
                    *r = slf;
                }
                Value::VecG2Affine(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_g2_affine_mut()
                        .append(r.into_vec_g2_affine_mut());
                    *r = slf;
                }
                Value::VecIndex(_) => {
                    let mut slf = self.clone();
                    slf.into_vec_index_mut().append(r.into_vec_index_mut());
                    *r = slf;
                }
                _ => {
                    let mut a = a.clone();
                    a.push(r.clone());
                    *r = Value::Vec(a);
                }
            },
        }
    }

    /// Generate a random value, given some parameters
    pub fn random<R: Rng + Sized>(rng: &mut R, typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Bool) => Value::Bool(rng.next_u32() % 2 == 0),
            ATyp::Base(ABase::Fin(r)) => Value::Index(r.random(rng)%10 as usize),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::FOps::rand(rng)),
            ATyp::Base(ABase::G1) => Value::G1(C::G1Ops::rand(rng)),
            ATyp::Base(ABase::G2) => Value::G2(C::G2Ops::rand(rng)),
            ATyp::Base(ABase::GT) => Value::GT(C::POps::rand(rng)),
            ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n) => {
                Value::VecIndex((0..*n).map(|_| r.random(rng) as usize).collect())
            }
            ATyp::Vec(box ATyp::Base(ABase::Scalar), n) => {
                Value::VecScalar(C::FOps::vec_rand(rng, *n))
            }
            ATyp::Vec(box ATyp::Base(ABase::G1), n) => Value::VecG1(C::G1Ops::vec_rand(rng, *n)),
            ATyp::Vec(box ATyp::Base(ABase::G2), n) => Value::VecG2(C::G2Ops::vec_rand(rng, *n)),
            ATyp::Vec(box ATyp::Base(ABase::GT), n) => Value::VecGT(C::POps::vec_rand(rng, *n)),
            ATyp::Vec(box t, n) => Value::Vec((0..*n).map(|_| Self::random(rng, &t)).collect()),
            ATyp::Uni(n) => Value::VecScalar(C::FOps::vec_rand(rng, *n)),
        }
    }

    pub fn typ(&self) -> ATyp {
        match self {
            Value::Bool(_) => ATyp::bool(),
            Value::VecBool(v) => ATyp::vec_bool(v.len()),
            Value::Index(n) => ATyp::fin(CRange::singleton(*n)),
            Value::Scalar(_) => ATyp::scalar(),
            Value::G1(_) => ATyp::g1(),
            Value::G2(_) => ATyp::g2(),
            Value::G1Affine(_) => ATyp::g1(),
            Value::G2Affine(_) => ATyp::g2(),
            Value::GT(_) => ATyp::gt(),
            Value::VecScalar(v) => ATyp::vec_scalar(v.len()),
            Value::VecG1(v) => ATyp::vec_g1(v.len()),
            Value::VecG2(v) => ATyp::vec_g2(v.len()),
            Value::VecG1Affine(v) => ATyp::vec_g1(v.len()),
            Value::VecG2Affine(v) => ATyp::vec_g2(v.len()),
            Value::VecGT(v) => ATyp::vec_gt(v.len()),
            Value::VecIndex(v) => {
                let min = *v.iter().min().unwrap();
                let max = *v.iter().max().unwrap();
                ATyp::Vec(Box::new(ATyp::fin(CRange::new(min, max + 1))), v.len())
            }
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
    #[inline]
    pub fn into_scalar(&self) -> C::F {
        match self {
            Value::Scalar(f) => *f,
            Value::Index(i) => C::FOps::from_usize(*i),
            _ => panic!("Expected scalar, found {}", self),
        }
    }
    #[inline]
    pub fn into_scalar_mut(&mut self) -> &mut C::F {
        match self {
            Value::Scalar(f) => f,
            Value::Index(i) => {
                *self = Value::Scalar(C::FOps::from_usize(*i));
                self.into_scalar_mut()
            }
            _ => panic!("Expected mut scalar, found {}", self),
        }
    }

    #[inline]
    pub fn into_g1_mut(&mut self) -> &mut C::G1 {
        match self {
            Value::G1(g) => g,
            Value::G1Affine(g) => {
                *self = Value::G1((*g).into());
                self.into_g1_mut()
            }
            _ => panic!("Expected mut group1, found {}", self),
        }
    }

    #[inline]
    pub fn into_g2_mut(&mut self) -> &mut C::G2 {
        match self {
            Value::G2(g) => g,
            Value::G2Affine(g) => {
                *self = Value::G2((*g).into());
                self.into_g2_mut()
            }
            _ => panic!("Expected mut group2, found {}", self),
        }
    }
    #[inline]
    pub fn into_gt_mut(&mut self) -> &mut PairingOutput<C::P> {
        match self {
            Value::GT(g) => g,
            _ => panic!("Expected mut groupt, found {}", self),
        }
    }
    #[inline]
    pub fn into_g1_affine_mut(&mut self) -> &mut C::G1Affine {
        match self {
            Value::G1(g) => {
                *self = Value::G1Affine((*g).into());
                self.into_g1_affine_mut()
            }
            Value::G1Affine(g) => g,
            _ => panic!("Expected mut group1, found {}", self),
        }
    }
    #[inline]
    pub fn into_g2_affine_mut(&mut self) -> &mut C::G2Affine {
        match self {
            Value::G2(g) => {
                *self = Value::G2Affine((*g).into());
                self.into_g2_affine_mut()
            }
            Value::G2Affine(g) => g,
            _ => panic!("Expected mut group2, found {}", self),
        }
    }
    #[inline]
    pub fn into_vec_scalar_mut(&mut self) -> &mut Vec<C::F> {
        match self {
            Value::VecScalar(v) => v,
            Value::VecIndex(v) => {
                *self = Value::VecScalar(v.par_iter().map(|i| C::FOps::from_usize(*i)).collect());
                self.into_vec_scalar_mut()
            }
            Value::Vec(v) => {
                *self = Value::VecScalar(v.par_iter().map(|v| v.into_scalar()).collect());
                self.into_vec_scalar_mut()
            }
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
            }
            Value::VecG1(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G1(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG2(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G2(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecGT(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::GT(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG1Affine(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G1Affine(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG2Affine(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::G2Affine(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecBool(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::Bool(*i)).collect());
                self.into_vec_mut()
            }
            _ => panic!("Expected mut vec, found {}", self),
        }
    }

    pub fn into_vec_g1_mut(&mut self) -> &mut Vec<C::G1> {
        match self {
            Value::VecG1(v) => v,
            Value::VecG1Affine(v) => {
                *self = Value::VecG1(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g1_mut()
            }
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }
    pub fn into_vec_g2_mut(&mut self) -> &mut Vec<C::G2> {
        match self {
            Value::VecG2(v) => v,
            Value::VecG2Affine(v) => {
                *self = Value::VecG2(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g2_mut()
            }
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
            }
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }
    pub fn into_vec_g2_affine_mut(&mut self) -> &mut Vec<C::G2Affine> {
        match self {
            Value::VecG2Affine(v) => v,
            Value::VecG2(v) => {
                *self = Value::VecG2Affine(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g2_affine_mut()
            }
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }
    pub fn into_vec_bool_mut(&mut self) -> &mut Vec<bool> {
        match self {
            Value::VecBool(v) => v,
            _ => panic!("Expected mut vec bool, found {}", self),
        }
    }
    pub fn into_range_mut(&mut self) -> &mut Vec<usize> {
        match self {
            Value::VecIndex(r) => r,
            _ => panic!("Expected mut range, found {}", self),
        }
    }
    pub fn into_vec_index_mut(&mut self) -> &mut Vec<usize> {
        match self {
            Value::VecIndex(v) => v,
            _ => panic!("Expected mut vec index, found {}", self),
        }
    }
    pub fn into_vec_index(&self) -> &Vec<usize> {
        match self {
            Value::VecIndex(v) => v,
            _ => panic!("Expected vec index, found {}", self),
        }
    }
    pub fn into_index(&self) -> usize {
        match self {
            Value::Index(i) => *i,
            _ => panic!("Expected index, found {}", self),
        }
    }
    pub fn into_index_mut(&mut self) -> &mut usize {
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

    pub fn value_vec(vec: Vec<Self>) -> Self {
        let mut typ = vec[0].typ();
        for i in vec.iter().skip(1) {
            typ = ATyp::lub_equ(&i.typ(), &typ, &Nothing).unwrap();
        }
        let mut vec_value = Value::Vec(vec);
        match typ {
            ATyp::Base(ABase::Scalar) => { vec_value.into_vec_scalar_mut(); vec_value },
            ATyp::Base(ABase::Bool) => { vec_value.into_vec_bool_mut(); vec_value },
            ATyp::Base(ABase::Fin(r)) => {
                match vec_value {
                    Value::Vec(v) => Value::VecIndex(v.into_iter().map(|i| i.into_index()).collect()),
                    Value::VecIndex(_) => vec_value,
                    _ => panic!("Expected Vec or VecIndex, found {}", vec_value)
                }
            },
            ATyp::Base(ABase::G1) => { vec_value.into_vec_g1_mut(); vec_value }, 
            ATyp::Base(ABase::G2) => { vec_value.into_vec_g2_mut(); vec_value },
            ATyp::Base(ABase::GT) => { vec_value.into_vec_gt_mut(); vec_value },
            _ => panic!("Not yet implemented for vector")
        }
    }

    pub fn value_ifft(&self) -> Self {
        match self {
            Value::VecScalar(v) => {
                let mut v = v.clone();
                C::FOps::vec_ifft(&mut v);
                Value::VecScalar(v)
            },
            _ => panic!("Expected vec scalar, found {}", self),
        }
    }

    pub fn value_fft(&self) -> Self {
        match self {
            Value::VecScalar(v) => {
                let mut v = v.clone();
                C::FOps::vec_fft(&mut v);
                Value::VecScalar(v)
            },
            _ => panic!("Expected vec scalar, found {}", self),
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
            }
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
            }
            Value::VecG1(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G1Ops::write(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecG2(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G2Ops::write(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecG1Affine(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G1Ops::write(&(*i).into(), f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecG2Affine(v) => {
                write!(f, "[")?;
                for i in v {
                    C::G2Ops::write(&(*i).into(), f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecGT(v) => {
                write!(f, "[")?;
                for i in v {
                    C::POps::write(i, f)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecIndex(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            }
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

/// Compare group elements by their x and y coordinates
/// in affine form. Warning: Expensive!
/// Should only be used at compile time.
fn affine_group_cmp<G: CurveGroup>(a: &G::Affine, b: &G::Affine) -> Ordering {
    match (a.xy(), b.xy()) {
        (Some((x1, y1)), Some((x2, y2))) => x1.cmp(&x2).then(y1.cmp(&y2)),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

/// Hacky: PartialOrd of the things that can be ordered
impl<C: ArkConfig> PartialOrd for Value<C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let order_self = self.discriminant_order();
        let order_other = other.discriminant_order();

        // 1. Compare based on the variant kind (discriminant order)
        match order_self.cmp(&order_other) {
            Ordering::Less => Some(Ordering::Less),
            Ordering::Greater => Some(Ordering::Greater),
            Ordering::Equal => {
                // 2. Variants are the same, compare inner values *if possible*
                match (self, other) {
                    // Variants with comparable inner types
                    (Value::Bool(a), Value::Bool(b)) => a.partial_cmp(b), // bool is Ord
                    (Value::VecBool(a), Value::VecBool(b)) => a.partial_cmp(b), // Vec<bool> is Ord
                    (Value::Index(a), Value::Index(b)) => a.partial_cmp(b), // usize is Ord
                    (Value::VecIndex(a), Value::VecIndex(b)) => a.partial_cmp(b), // Vec<usize> is Ord
                    (Value::Vec(a), Value::Vec(b)) => a.partial_cmp(b), // Vec<Value<C>> uses this impl recursively

                    // Variants with non-comparable inner types (return None)
                    (Value::Scalar(a), Value::Scalar(b)) => {
                        a.into_bigint().partial_cmp(&b.into_bigint())
                    }
                    (Value::VecScalar(a), Value::VecScalar(b)) => a.partial_cmp(b), // Vec<Scalar> is Ord
                    (Value::G1(a), Value::G1(b)) => Some(affine_group_cmp::<C::G1>(
                        &a.into_affine(),
                        &b.into_affine(),
                    )),
                    (Value::G2(a), Value::G2(b)) => Some(affine_group_cmp::<C::G2>(
                        &a.into_affine(),
                        &b.into_affine(),
                    )),
                    (Value::GT(a), Value::GT(b)) => a.partial_cmp(b), // PairingOutput is Ord
                    (Value::VecG1(a), Value::VecG1(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G1>(&a.into_affine(), &b.into_affine()))
                        .find(|o| o != &Ordering::Equal),
                    (Value::VecG2(a), Value::VecG2(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G2>(&a.into_affine(), &b.into_affine()))
                        .find(|o| o != &Ordering::Equal),
                    (Value::VecGT(a), Value::VecGT(b)) => a.partial_cmp(b), // Vec<PairingOutput> is Ord
                    (Value::G1Affine(a), Value::G1Affine(b)) => {
                        Some(affine_group_cmp::<C::G1>(a, b))
                    }
                    (Value::G2Affine(a), Value::G2Affine(b)) => {
                        Some(affine_group_cmp::<C::G2>(a, b))
                    }
                    (Value::VecG1Affine(a), Value::VecG1Affine(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G1>(a, b))
                        .find(|o| o != &Ordering::Equal),
                    (Value::VecG2Affine(a), Value::VecG2Affine(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G2>(a, b))
                        .find(|o| o != &Ordering::Equal),

                    // This case should be unreachable because we've covered all variants
                    // and already established that the discriminants are equal.
                    (_, _) => {
                        unreachable!("Variants matched discriminant order but not specific arms")
                    }
                }
            }
        }
    }
}

impl<C: ArkConfig> Ord for Value<C> {
    fn cmp(&self, other: &Self) -> Ordering {
        let order_self = self.discriminant_order();
        let order_other = other.discriminant_order();

        // 1. Compare based on the variant kind (discriminant order)
        match order_self.cmp(&order_other) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => {
                // 2. Variants are the same, compare inner values *if possible*
                match (self, other) {
                    // Variants with comparable inner types
                    (Value::Bool(a), Value::Bool(b)) => a.cmp(b), // bool is Ord
                    (Value::VecBool(a), Value::VecBool(b)) => a.cmp(b), // Vec<bool> is Ord
                    (Value::Index(a), Value::Index(b)) => a.cmp(b), // usize is Ord
                    (Value::VecIndex(a), Value::VecIndex(b)) => a.cmp(b), // Vec<usize> is Ord
                    (Value::Vec(a), Value::Vec(b)) => a.cmp(b), // Vec<Value<C>> uses this impl recursively

                    // Variants with non-comparable inner types (return None)
                    (Value::Scalar(a), Value::Scalar(b)) => a.into_bigint().cmp(&b.into_bigint()),
                    (Value::VecScalar(a), Value::VecScalar(b)) => a.cmp(b), // Vec<Scalar> is Ord
                    (Value::G1(a), Value::G1(b)) => {
                        affine_group_cmp::<C::G1>(&a.into_affine(), &b.into_affine())
                    }
                    (Value::G2(a), Value::G2(b)) => {
                        affine_group_cmp::<C::G2>(&a.into_affine(), &b.into_affine())
                    }
                    (Value::GT(a), Value::GT(b)) => a.cmp(b), // PairingOutput is Ord
                    (Value::VecG1(a), Value::VecG1(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G1>(&a.into_affine(), &b.into_affine()))
                        .find(|o| o != &Ordering::Equal)
                        .unwrap_or(Ordering::Equal),
                    (Value::VecG2(a), Value::VecG2(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G2>(&a.into_affine(), &b.into_affine()))
                        .find(|o| o != &Ordering::Equal)
                        .unwrap_or(Ordering::Equal),
                    (Value::VecGT(a), Value::VecGT(b)) => a.cmp(b), // Vec<PairingOutput> is Ord
                    (Value::G1Affine(a), Value::G1Affine(b)) => affine_group_cmp::<C::G1>(a, b),
                    (Value::G2Affine(a), Value::G2Affine(b)) => affine_group_cmp::<C::G2>(a, b),
                    (Value::VecG1Affine(a), Value::VecG1Affine(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G1>(a, b))
                        .find(|o| o != &Ordering::Equal)
                        .unwrap_or(Ordering::Equal),
                    (Value::VecG2Affine(a), Value::VecG2Affine(b)) => a
                        .iter()
                        .zip(b.iter())
                        .map(|(a, b)| affine_group_cmp::<C::G2>(a, b))
                        .find(|o| o != &Ordering::Equal)
                        .unwrap_or(Ordering::Equal),

                    // This case should be unreachable because we've covered all variants
                    // and already established that the discriminants are equal.
                    (_, _) => {
                        unreachable!("Variants matched discriminant order but not specific arms")
                    }
                }
            }
        }
    }
}

#[cfg(test)]
use crate::ArkBls12_381;
#[cfg(test)]
use ark_std::test_rng;
#[cfg(test)]
use share::assert_deq;

// Commutativity of addition
#[test]
fn test_add_comm() {
    // Scalar + Scalar
    let mut rng = test_rng();
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    assert_deq!(&a + &b, &b + &a);

    // Group1 + Group1
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());
    assert_deq!(&a + &b, &b + &a);

    // Group2 + Group2
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g2());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g2());
    assert_deq!(&a + &b, &b + &a);

    // GT + GT
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::gt());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::gt());
    assert_deq!(&a + &b, &b + &a);

    // Vec<Scalar> + Vec<Scalar>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    assert_deq!(&a + &b, &b + &a);

    // Vec<Index> + Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    assert_deq!(&a + &b, &b + &a);

    // Vec<Scalar> + Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_fin(CRange::new(0, 10), 10));
    assert_deq!(&a + &b, &b + &a);
}

// Commutativity of multiplication
#[test]
fn test_mul_comm() {
    // Scalar * Scalar
    let mut rng = test_rng();
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    assert_deq!(&a * &b, &b * &a);
    
    // Vec<Scalar> * Vec<Scalar>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::scalar()), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Vec(Box::new(ATyp::scalar()), 10));
    assert_deq!(&a * &b, &b * &a);

    // Vec<Index> * Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    assert_deq!(&a * &b, &b * &a);

    // Vec<Scalar> * Vec<Index>
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_fin(CRange::singleton(10), 10));
    assert_deq!(&a * &b, &b * &a);

    let mut a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());
    let mut b1 = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g2());
    let b2 = b1.clone();
    Value::value_pair(&a, &mut b1);
    Value::value_pair(&b2, &mut a);
    assert_deq!(b1, a);
}

#[test]
fn inverse_test() {
    let mut rng = test_rng();
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_g1(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);
    
    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_g2(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);


    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g2());
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let c = (&a * &b) / b;
    assert_deq!(&a, &c);

    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = &(&b.clone() / &b.clone()) * &a;
    assert_deq!(&a, &c);
    assert_deq!(&a * &(&b.clone() / &b.clone()), &(&b.clone() / &b.clone()) * &a);
    assert_deq!((&a * &b.clone()) / b.clone(), a);

    let a = Value::<ArkBls12_381>::random(&mut rng, &&ATyp::vec_g1(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = &(&b.clone() / &b.clone()) * &a;
    assert_deq!(&a, &c); 

    let a = Value::<ArkBls12_381>::random(&mut rng, &&ATyp::vec_g2(10));
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = &(&b.clone() / &b.clone()) * &a;
    assert_deq!(&a, &c); 

    let a = Value::<ArkBls12_381>::scalar_from_usize(1);
    let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    let c = (&a/&b).dot(b.clone());
    assert_deq!(&c, &Value::<ArkBls12_381>::scalar_from_usize(10));
}


