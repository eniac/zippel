use crate::poly_variant::PolyVariant;
use crate::types::Lub;
use crate::virtual_polynomial::VirtualPolynomial;
use crate::{ABase, ATyp, ArkConfig, ArkGroupOps, ArkPairingOps, ArkScalarOps, to_bytes};
use ark_ec::pairing::PairingOutput;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_ff::{One, PrimeField, Zero};
use ark_poly::{
    DenseMultilinearExtension, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
    univariate::DensePolynomial,
};
use ark_serialize::{CanonicalSerialize, SerializationError};
use ark_std::log2;
use lang::ast::BinOp;
use lang::typ::{CRange, Nothing};
use rand::Rng;
use rayon::prelude::*;
use share::Ctx;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::cmp::Ordering;
use std::fmt;
use std::io::Write;
use std::ops::{Add, AddAssign, BitAnd, BitOr, BitXor, Div, Mul, MulAssign, Rem, Sub};

#[derive(Debug, Clone, Eq)]
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
    /// Record with named fields
    Record(Ctx<String, Value<C>>),
    /// Virtual Polynomial (sum-of-products of univariate or multilinear, dense or sparse)
    Poly(VirtualPolynomial<C::F>),
}

impl<C: ArkConfig> PartialEq for Value<C> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // For projective group elements, normalize before comparing
            (Value::G1(a), Value::G1(b)) => a.into_affine() == b.into_affine(),
            (Value::G2(a), Value::G2(b)) => a.into_affine() == b.into_affine(),
            (Value::VecG1(a), Value::VecG1(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(x, y)| x.into_affine() == y.into_affine())
            }
            (Value::VecG2(a), Value::VecG2(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(x, y)| x.into_affine() == y.into_affine())
            }
            // For all other variants, use structural equality
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::VecBool(a), Value::VecBool(b)) => a == b,
            (Value::Index(a), Value::Index(b)) => a == b,
            (Value::Scalar(a), Value::Scalar(b)) => a == b,
            (Value::VecIndex(a), Value::VecIndex(b)) => a == b,
            (Value::VecScalar(a), Value::VecScalar(b)) => a == b,
            (Value::GT(a), Value::GT(b)) => a == b,
            (Value::VecGT(a), Value::VecGT(b)) => a == b,
            (Value::G1Affine(a), Value::G1Affine(b)) => a == b,
            (Value::G2Affine(a), Value::G2Affine(b)) => a == b,
            (Value::VecG1Affine(a), Value::VecG1Affine(b)) => a == b,
            (Value::VecG2Affine(a), Value::VecG2Affine(b)) => a == b,
            (Value::Vec(a), Value::Vec(b)) => a == b,
            (Value::Record(a), Value::Record(b)) => a == b,
            (Value::Poly(a), Value::Poly(b)) => a == b,
            // Different variants are not equal
            _ => false,
        }
    }
}

impl<C: ArkConfig> std::hash::Hash for Value<C> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::Bool(b) => b.hash(state),
            Value::VecBool(v) => v.hash(state),
            Value::Index(i) => i.hash(state),
            Value::Scalar(f) => f.hash(state),
            Value::VecIndex(v) => v.hash(state),
            Value::VecScalar(v) => v.hash(state),
            // Projective → affine for canonical hashing (matches PartialEq)
            Value::G1(g) => g.into_affine().hash(state),
            Value::G2(g) => g.into_affine().hash(state),
            Value::GT(g) => g.hash(state),
            Value::VecG1(v) => {
                v.len().hash(state);
                for g in v {
                    g.into_affine().hash(state);
                }
            }
            Value::VecG2(v) => {
                v.len().hash(state);
                for g in v {
                    g.into_affine().hash(state);
                }
            }
            Value::VecGT(v) => v.hash(state),
            Value::G1Affine(g) => g.hash(state),
            Value::G2Affine(g) => g.hash(state),
            Value::VecG1Affine(v) => v.hash(state),
            Value::VecG2Affine(v) => v.hash(state),
            Value::Vec(v) => v.hash(state),
            Value::Record(r) => r.hash(state),
            Value::Poly(p) => {
                let mut bytes = Vec::new();
                p.serialize_compressed(&mut bytes).unwrap_or_default();
                bytes.hash(state);
            }
        }
    }
}

fn serialize_value_internal<C: ArkConfig, W: Write>(
    value: &Value<C>,
    writer: &mut W,
) -> Result<(), SerializationError> {
    match value {
        Value::Bool(b) => b.serialize_compressed(writer),
        Value::VecBool(vec) => {
            (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for b in vec {
                b.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::Index(i) => (*i as u64).serialize_compressed(writer),
        Value::Scalar(f) => {
            // println!("Scalar: {}", f);
            f.serialize_compressed(writer)
        }
        Value::VecIndex(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for i in vec {
                (*i as u64).serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::VecScalar(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for f in vec {
                f.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::G1(g) => g.serialize_compressed(writer),
        Value::G2(g) => g.serialize_compressed(writer),
        Value::GT(gt) => gt.serialize_compressed(writer),
        Value::VecG1(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for g in vec {
                g.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::VecG2(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for g in vec {
                g.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::VecGT(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for gt in vec {
                gt.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::G1Affine(g) => g.serialize_compressed(writer),
        Value::G2Affine(g) => g.serialize_compressed(writer),
        Value::VecG1Affine(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for g in vec {
                g.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::VecG2Affine(vec) => {
            // (vec.len() as u64).serialize_compressed(&mut *writer)?;
            for g in vec {
                g.serialize_compressed(&mut *writer)?;
            }
            Ok(())
        }
        Value::Vec(values) => {
            // (values.len() as u64).serialize_compressed(&mut *writer)?;
            for v in values {
                serialize_value_internal(v, &mut *writer)?;
            }
            Ok(())
        }
        Value::Poly(poly) => {
            // UFCS: `poly.serialize_compressed` does not reliably resolve to
            // `CanonicalSerialize` for `VirtualPolynomial` (public transcript bytes
            // must match `VirtualPolynomial`'s tagged/normalize-or-explicit encoding).
            CanonicalSerialize::serialize_compressed(poly, &mut *writer)
        }
        Value::Record(fields) => {
            // Serialize record fields
            (fields.len() as u64).serialize_compressed(&mut *writer)?;
            for (name, value) in fields.iter() {
                // Serialize field name length and name
                name.as_bytes().serialize_compressed(&mut *writer)?;
                serialize_value_internal(value, &mut *writer)?;
            }
            Ok(())
        }
    }
}

pub fn serialize_value<C: ArkConfig, W: Write>(
    value: &Value<C>,
    mut writer: W,
) -> Result<(), SerializationError> {
    serialize_value_internal(value, &mut writer)
}

pub fn value_to_bytes<C: ArkConfig>(value: &Value<C>) -> Result<Vec<u8>, SerializationError> {
    let mut buffer = Vec::new();
    serialize_value(value, &mut buffer)?;
    Ok(buffer)
}

impl<C: ArkConfig> Value<C> {
    /// Returns an integer representing the constructor order.
    /// Higher values correspond to constructors defined earlier.
    pub fn discriminant_order(&self) -> u8 {
        match self {
            Value::Poly(_) => 19,
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
            Value::Record(_) => 0,
        }
    }

    pub fn scalar_from_usize(i: usize) -> Self {
        Value::Scalar(C::FOps::from_usize(i))
    }

    /// Returns the zero value for `typ`. For polynomial types, the
    /// arkworks zero polynomial is size-independent, so the `m` / `n`
    /// parameters (which under the phase-14 encoding denote **max
    /// degree** / **num variables**, not coefficient counts — see
    /// `docs/poly-encoding.md`) are intentionally ignored.
    pub fn zero(typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Bool) => Value::Bool(false),
            ATyp::Base(ABase::Fin(r)) if r.contains(0) => Value::Index(0),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::F::zero()),
            ATyp::Base(ABase::G1) => Value::G1(C::G1::zero()),
            ATyp::Base(ABase::G2) => Value::G2(C::G2::zero()),
            ATyp::Base(ABase::GT) => Value::GT(PairingOutput::<C::P>::zero()),
            ATyp::Uni(_m) => Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                DensePolynomial::<C::F>::zero(),
            ))),
            ATyp::Mle(_n) => Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                DenseMultilinearExtension::<C::F>::zero(),
            ))),
            ATyp::VPoly(_, _) => Value::Poly(VirtualPolynomial::new()),
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
                    v.push(Value::<C>::zero(vt));
                }
                Value::Vec(v)
            }
            ATyp::Record(fields) => {
                let mut record_fields = Ctx::new();
                for (name, field_typ) in fields.iter() {
                    let v = Value::<C>::zero(field_typ);
                    record_fields.insert(name, &v);
                }
                Value::Record(record_fields)
            }
            _ => panic!("Cannot create zero value for type {}", typ),
        }
    }

    /// Creates the multiplicative identity (one) for the given type.
    pub fn one(typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Bool) => Value::Bool(true),
            ATyp::Base(ABase::Fin(r)) if r.contains(1) => Value::Index(1),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::FOps::one()),
            ATyp::Vec(box ATyp::Base(ABase::Scalar), n) => {
                Value::VecScalar(vec![C::FOps::one(); *n])
            }
            ATyp::Vec(box ATyp::Base(ABase::Bool), n) => Value::VecBool(vec![true; *n]),
            ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n) if r.contains(1) => {
                Value::VecIndex(vec![1; *n])
            }
            ATyp::Uni(_) | ATyp::Mle(_) | ATyp::VPoly(_, _) => {
                Value::Poly(VirtualPolynomial::from_scalar(C::FOps::one()))
            }
            ATyp::Vec(box vt, n) => {
                let mut v = Vec::<Value<C>>::with_capacity(*n);
                for _ in 0..*n {
                    v.push(Value::<C>::one(vt));
                }
                Value::Vec(v)
            }
            _ => panic!("Cannot create one value for type {}", typ),
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
                Value::Poly(poly) => {
                    *other = Value::Poly(poly.poly_add_scalar(C::FOps::from_usize(*a)));
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                Value::Index(b) => {
                    *other = Value::Scalar(C::FOps::from_usize(*b));
                    C::FOps::add(a, other.into_scalar_mut());
                }
                Value::Scalar(_) => C::FOps::add(a, other.into_scalar_mut()),
                Value::Poly(poly) => {
                    *other = Value::Poly(poly.poly_add_scalar(*a));
                }
                Value::G1(other_val) => {
                    C::G1Ops::add(&(*other_val).into_affine(), self.clone().into_g1_mut())
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            // Group addition
            Value::G1Affine(a) => C::G1Ops::add(a, other.into_g1_mut()),
            Value::G2Affine(a) => C::G2Ops::add(a, other.into_g2_mut()),
            Value::G1(a) => C::G1Ops::add(&(*a).into_affine(), other.into_g1_mut()),
            Value::G2(a) => C::G2Ops::add(&(*a).into_affine(), other.into_g2_mut()),
            Value::GT(a) => C::POps::add(a, other.into_gt_mut()),
            // Polynomial addition
            Value::Poly(a) => match &other {
                Value::Poly(b) => {
                    *other = Value::Poly(a.poly_add(b).expect("Polynomial addition failed"));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::Poly(a.poly_add_scalar(other.into_scalar()));
                }
                _ => panic!("Expected polynomial or scalar, found {}", other),
            },
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
            Value::Record(_) => {
                panic!("Cannot add records")
            }
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
                Value::Poly(poly) => {
                    *other = Value::Poly(
                        VirtualPolynomial::scalar_sub_poly(C::FOps::from_usize(*a), poly)
                            .expect("scalar_sub_poly failed"),
                    );
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                Value::Index(b) => {
                    *other = Value::Scalar(C::FOps::from_usize(*b));
                    C::FOps::sub(a, other.into_scalar_mut());
                }
                Value::Scalar(_) => C::FOps::sub(a, other.into_scalar_mut()),
                Value::Poly(poly) => {
                    *other = Value::Poly(
                        VirtualPolynomial::scalar_sub_poly(*a, poly)
                            .expect("scalar_sub_poly failed"),
                    );
                }
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
            Value::Poly(a) => match &other {
                Value::Poly(b) => {
                    *other = Value::Poly(a.poly_sub(b).expect("Polynomial subtraction failed"));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::Poly(a.poly_sub_scalar(other.into_scalar()));
                }
                _ => panic!("Expected polynomial or scalar, found {}", other),
            },
            Value::Record(_) => {
                panic!("Cannot subtract records")
            }
        }
    }

    #[inline]
    pub fn value_pair(&self, other: &mut Self) {
        match (self, &other) {
            (Value::G1(a), Value::G2(b)) | (Value::G2(b), Value::G1(a)) => {
                *other = Value::GT(C::POps::billinear_map(a, b))
            }
            (Value::G1Affine(a), Value::G2Affine(b)) | (Value::G2Affine(b), Value::G1Affine(a)) => {
                *other = Value::GT(C::POps::billinear_map(&(*a).into(), &(*b).into()))
            }
            (Value::G1(a), Value::G2Affine(b)) => {
                *other = Value::GT(C::POps::billinear_map(a, &(*b).into()))
            }
            (Value::G2(a), Value::G1Affine(b)) => {
                *other = Value::GT(C::POps::billinear_map(&(*b).into(), a))
            }
            (Value::G1Affine(a), Value::G2(b)) => {
                *other = Value::GT(C::POps::billinear_map(&(*a).into(), b))
            }
            (Value::G2Affine(a), Value::G1(b)) => {
                *other = Value::GT(C::POps::billinear_map(b, &(*a).into()))
            }
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
                    a,
                    &b.iter().map(|b| (*b).into()).collect(),
                ))
            }
            (Value::VecG2(a), Value::VecG1Affine(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &b.iter().map(|b| (*b).into()).collect(),
                    a,
                ))
            }
            (Value::VecG1Affine(a), Value::VecG2(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    &a.iter().map(|a| (*a).into()).collect(),
                    b,
                ))
            }
            (Value::VecG2Affine(a), Value::VecG1(b)) => {
                *other = Value::VecGT(C::POps::billinear_vec_mul(
                    b,
                    &a.iter().map(|b| (*b).into()).collect(),
                ))
            }
            (Value::Record(_), _) | (_, Value::Record(_)) => {
                panic!("Cannot pair records")
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
            Value::Poly(a) => match &other {
                Value::Poly(b) => {
                    *other = Value::Poly(a.poly_mul(b).expect("Polynomial multiplication failed"));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::Poly(a.poly_mul_scalar(other.into_scalar()));
                }
                _ => panic!("Expected polynomial or scalar, found {}", other),
            },
            Value::Index(a) => match &other {
                Value::Bool(_) | Value::VecBool(_) => {
                    panic!("Cannot multiply bools {} * {}", self, other)
                }
                // Index * Index = Index
                Value::Index(_) => {
                    *other.into_index_mut() *= *a;
                }
                // Index * whatever, cast index to scalar
                Value::Scalar(_) => C::FOps::mul(&C::FOps::from_usize(*a), other.into_scalar_mut()),
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
                Value::Poly(poly) => {
                    *other = Value::Poly(poly.poly_mul_scalar(C::FOps::from_usize(*a)));
                }
                Value::Record(_) => {
                    panic!("Cannot multiply Index and Record")
                }
            },
            Value::Record(_) => {
                panic!("Cannot multiply records")
            }
            Value::Scalar(a) => match &other {
                Value::Bool(_) | Value::VecBool(_) => {
                    panic!("Cannot multiply bools {} * {}", self, other)
                }
                // Scalar * index, cast index to Scalar
                Value::Index(b) => {
                    let mut value = C::FOps::from_usize(*b);
                    C::FOps::mul(a, &mut value);
                    *other = Value::Scalar(value);
                }
                // Scalar * Scalar = Scalar
                Value::Scalar(_) => C::FOps::mul(a, other.into_scalar_mut()),
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
                Value::Poly(poly) => {
                    *other = Value::Poly(poly.poly_mul_scalar(*a));
                }
                Value::Record(_) => {
                    panic!("Cannot multiply Scalar and Record")
                }
            },
            Value::G1(a) => match &other {
                // Group1 * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let mut group = C::G1Ops::vec_mul(a, &[other.into_scalar()]);
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
                    let mut group = C::G2Ops::vec_mul(a, &[other.into_scalar()]);
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
                    let vr = vec![*other.into_scalar_mut()];
                    let mut group = C::POps::vec_mul(a, &vr);
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
                        std::iter::repeat_n(other.into_scalar(), v.len()).collect::<Vec<_>>(),
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
                Value::Poly(_) => {
                    panic!("Cannot multiply Vec<Index> and Poly");
                }
                Value::Record(_) => {
                    panic!("Cannot multiply Vec<Index> and Record")
                }
            },
            Value::VecScalar(v) => match &other {
                // Vec<Scalar> * Index
                Value::Index(_) | Value::Scalar(_) => {
                    *other = Value::VecScalar(
                        std::iter::repeat_n(other.into_scalar(), v.len()).collect::<Vec<_>>(),
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
                Value::Index(_) => *other = Value::Index(*a / other.into_index()),
                // Index / whatever, cast index to scalar
                Value::Scalar(_) => C::FOps::div(&C::FOps::from_usize(*a), other.into_scalar_mut()),
                // Index / Poly
                Value::Poly(poly) => {
                    // Can only divide by constant polynomial
                    let mut poly_scalar = poly
                        .clone()
                        .into_scalar()
                        .expect("Cannot divide by non-constant polynomial");
                    let numerator = C::FOps::from_usize(*a);
                    C::FOps::div(&numerator, &mut poly_scalar);
                    *other = Value::Scalar(poly_scalar);
                }
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
                Value::Record(_) => {
                    panic!("Cannot divide Index and Record")
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                // Scalar / index, cast index to Scalar
                Value::Index(b) => C::FOps::div(a, &mut C::FOps::from_usize(*b)),
                // Scalar / Scalar = Scalar
                Value::Scalar(_) => C::FOps::div(a, other.into_scalar_mut()),
                // Scalar / Poly
                Value::Poly(poly) => {
                    // Can only divide by constant polynomial
                    let mut poly_scalar = poly
                        .clone()
                        .into_scalar()
                        .expect("Cannot divide by non-constant polynomial");
                    C::FOps::div(a, &mut poly_scalar);
                    *other = Value::Scalar(poly_scalar);
                }
                // Scalar / Vector
                Value::VecIndex(_) | Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| C::FOps::div(a, b)),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_div(b)),
                Value::Record(_) => {
                    panic!("Cannot divide Scalar and Record")
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G1(a) => match &other {
                // Group1 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = other
                        .into_scalar()
                        .inverse()
                        .unwrap_or_else(|| panic!("Failed to invert scalar {}", other));
                    let mut g = *a;
                    C::G1Ops::mul(&f, &mut g);
                    *other = Value::G1(g);
                }
                // Group1 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vr);
                    *other = Value::VecG1Affine(C::G1Ops::vec_mul(a, vr));
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
                        .unwrap_or_else(|| panic!("Failed to invert scalar {}", other));
                    let mut g = *a;
                    C::G2Ops::mul(&f, &mut g);
                    *other = Value::G2(g);
                }
                // G2 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vr);
                    *other = Value::VecG2Affine(C::G2Ops::vec_mul(a, vr));
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
                        .unwrap_or_else(|| panic!("Failed to invert scalar {}", other));
                    let mut g = *a;
                    C::POps::mul(&f, &mut g);
                    *other = Value::GT(g);
                }
                // G2 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vr);
                    *other = Value::VecGT(C::POps::vec_mul(a, vr));
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
                        std::iter::repeat_n(other.into_scalar(), v.len()).collect::<Vec<_>>(),
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
                        .unwrap_or_else(|| panic!("Failed to invert scalar {}", f));
                    let mut vr =
                        std::iter::repeat_n(f.inverse().unwrap(), v.len()).collect::<Vec<_>>();
                    v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b));
                    *other = Value::VecScalar(vr);
                }
                // Vec<Index> / Vec<Index> = Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    C::FOps::vec_inv(vr);
                    v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| C::FOps::mul(a, b));
                }
                // Vec<Scalar> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::Scalar(*a).value_div(b)),
                Value::Record(_) => {
                    panic!("Cannot divide Vec<Scalar> and Record")
                }
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
                Value::Record(_) => {
                    panic!("Cannot divide Vec<G1> and Record")
                }
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
                Value::Record(_) => {
                    panic!("Cannot divide Vec<G2> and Record")
                }
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
            Value::Poly(p) => match &other {
                Value::Poly(o) => {
                    *other = Value::Poly(p.poly_div(o).expect("Polynomial division failed"));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::Poly(
                        p.poly_div_scalar(other.into_scalar())
                            .expect("Polynomial division by scalar failed"),
                    );
                }
                Value::Record(_) => {
                    panic!("Cannot divide Poly and Record")
                }
                _ => panic!("Expected poly, found {}", other),
            },
            Value::Record(_) => {
                panic!("Cannot divide records")
            }
        }
    }

    /// Typed division.
    ///
    /// This delegates to `value_div` for most types, but for `ATyp::Uni(_)`
    /// it switches `value_div` into "polynomial mode" by wrapping the operands
    /// as `Value::Poly` first so that the existing `Poly/Poly` arm performs
    /// true polynomial division, and then normalizes the quotient length.
    #[inline]
    pub fn value_div_typed(self, other: Self, typ: &ATyp) -> Self {
        match typ {
            ATyp::Uni(out_len) => {
                // Use the existing `Value::Poly / Value::Poly` arm in `value_div`.
                let mut rhs = other.value_poly();
                let lhs_poly = self.value_poly();
                lhs_poly.value_div(&mut rhs);

                // `rhs` now holds the quotient as a polynomial; convert to coeffs.
                let q_coeffs = rhs.value_coef();
                let mut coeffs = match q_coeffs {
                    Value::VecScalar(v) => v,
                    _ => unreachable!("value_coef must return VecScalar"),
                };

                // Ensure coefficient vector length matches the inferred Uni size.
                if coeffs.len() < *out_len {
                    coeffs.extend(std::iter::repeat_n(C::F::zero(), *out_len - coeffs.len()));
                } else if coeffs.len() > *out_len {
                    coeffs.truncate(*out_len);
                }

                Value::VecScalar(coeffs)
            }
            _ => {
                let mut rhs = other;
                self.value_div(&mut rhs);
                rhs
            }
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
            while i.is_multiple_of(2) {
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
                let mut a = *a;
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
            // For all `VecG{1,2} <-> VecScalar/VecIndex` dot paths we
            // normalize the projective basis to affine via Montgomery's
            // batch trick (one inversion for the whole batch) before
            // dispatching to the affine MSM. The previous per-element
            // `(*a).into()` collect did N inversions and dominated
            // prover wall-clock at large K (≈90% of MSM time at
            // K=4096 on BLS12-381).
            (Value::VecG2(b), Value::VecIndex(_)) => {
                let vg = <C::G2 as ark_ec::CurveGroup>::normalize_batch(b);
                Self::value_dot(&Value::VecG2Affine(vg), other);
            }
            (Value::VecG1(b), Value::VecScalar(_)) => {
                let vg = <C::G1 as ark_ec::CurveGroup>::normalize_batch(b);
                Self::value_dot(&Value::VecG1Affine(vg), other);
            }
            (Value::VecScalar(_), Value::VecG1(b)) => {
                let vg = <C::G1 as ark_ec::CurveGroup>::normalize_batch(b);
                *other = Value::VecG1Affine(vg);
                Self::value_dot(self, other);
            }
            (Value::VecG2(b), Value::VecScalar(_)) => {
                let vg = <C::G2 as ark_ec::CurveGroup>::normalize_batch(b);
                Self::value_dot(&Value::VecG2Affine(vg), other);
            }
            (Value::VecScalar(_), Value::VecG2(b)) => {
                let vg = <C::G2 as ark_ec::CurveGroup>::normalize_batch(b);
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
                        .reduce(C::FOps::zero, |mut a, b| {
                            C::FOps::add(&b, &mut a);
                            a
                        }),
                );
            }
            // `dot(VecG1, VecG2) -> GT` is Σᵢ e(g1ᵢ, g2ᵢ) — exactly
            // `multi_pairing`. Routing it through `billinear_vec_dot` collapses
            // N final exponentiations into one (and one Miller loop over all
            // pairs), which is the standard pairing-batching trick used by
            // every native SNARK verifier (e.g. ark-poly-commit::kzg10::check,
            // garuda-pari verify). The type checker already accepts this
            // signature (types.rs:328); only the runtime arm was missing.
            (Value::VecG1(a), Value::VecG2(b)) | (Value::VecG2(b), Value::VecG1(a)) => {
                *other = Value::GT(C::POps::billinear_vec_dot(a, b))
            }
            (Value::VecG1Affine(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecG1Affine(a)) => {
                let ap: Vec<C::G1> = a.par_iter().map(|x| (*x).into()).collect();
                let bp: Vec<C::G2> = b.par_iter().map(|x| (*x).into()).collect();
                *other = Value::GT(C::POps::billinear_vec_dot(&ap, &bp))
            }
            (Value::VecG1(a), Value::VecG2Affine(b)) | (Value::VecG2Affine(b), Value::VecG1(a)) => {
                let bp: Vec<C::G2> = b.par_iter().map(|x| (*x).into()).collect();
                *other = Value::GT(C::POps::billinear_vec_dot(a, &bp))
            }
            (Value::VecG1Affine(a), Value::VecG2(b)) | (Value::VecG2(b), Value::VecG1Affine(a)) => {
                let ap: Vec<C::G1> = a.par_iter().map(|x| (*x).into()).collect();
                *other = Value::GT(C::POps::billinear_vec_dot(&ap, b))
            }
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
    pub fn value_eval(self, other: Self) -> Self {
        let mut other = other;
        match &self {
            // For Uni/MLE stored as coefficient or evaluation vectors, promote to a polynomial first.
            Value::VecScalar(_) | Value::VecIndex(_) => {
                self.value_poly().eval(&mut other);
            }
            _ => {
                self.eval(&mut other);
            }
        }
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
            (Value::Poly(a), Value::Poly(b)) => {
                // Use PolyVariant's PartialEq implementation
                a == b
            }
            (Value::Record(a), Value::Record(b)) => a == b,
            (a, b) => panic!("Cannot compare {} == {}", a, b),
        }
    }

    pub fn value_equ(&self, other: &Self) -> Self {
        Value::Bool(Value::equ(self, other))
    }

    pub fn challenge<H: DuplexSpongeInterface<U = u8>>(state: &mut ProverState<H>) -> Self {
        Value::Scalar(C::FOps::challenge(state))
    }

    #[allow(clippy::should_implement_trait)]
    pub fn hash<H: DuplexSpongeInterface<U = u8>>(&self, state: &mut ProverState<H>) {
        match self {
            Value::Bool(b) => state.public_message(to_bytes!(b).unwrap().as_slice()),
            Value::VecBool(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::Index(i) => state.public_message(to_bytes!(i).unwrap().as_slice()),
            Value::Scalar(f) => state.public_message(to_bytes!(f).unwrap().as_slice()),
            Value::VecIndex(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::VecScalar(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::G1(g1) => state.public_message(to_bytes!(g1).unwrap().as_slice()),
            Value::G2(g2) => state.public_message(to_bytes!(g2).unwrap().as_slice()),
            Value::GT(pairing_output) => {
                state.public_message(to_bytes!(pairing_output).unwrap().as_slice())
            }
            Value::VecG1(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::VecG2(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::VecGT(pairing_outputs) => {
                state.public_message(to_bytes!(pairing_outputs).unwrap().as_slice())
            }
            Value::G1Affine(g1) => state.public_message(to_bytes!(g1).unwrap().as_slice()),
            Value::G2Affine(g2) => state.public_message(to_bytes!(g2).unwrap().as_slice()),
            Value::VecG1Affine(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::VecG2Affine(items) => state.public_message(to_bytes!(items).unwrap().as_slice()),
            Value::Vec(values) => values.iter().for_each(|v| v.hash(state)),
            _ => panic!("Cannot hash {}", self),
        }
    }
    pub fn ram(self, r: Self) -> Self {
        match (self, r) {
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                Value::VecIndex(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecIndex(a), Value::Index(b)) => Value::Index(a[b]),
            (Value::VecScalar(a), Value::VecIndex(b)) => {
                Value::VecScalar(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecScalar(a), Value::Index(b)) => Value::Scalar(a[b]),
            (Value::VecG1(a), Value::VecIndex(b)) => {
                Value::VecG1(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG1(a), Value::Index(b)) => Value::G1(a[b]),
            (Value::VecG2(a), Value::VecIndex(b)) => {
                Value::VecG2(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG2(a), Value::Index(b)) => Value::G2(a[b]),
            (Value::VecGT(a), Value::VecIndex(b)) => {
                Value::VecGT(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecGT(a), Value::Index(b)) => Value::GT(a[b]),
            (Value::VecG1Affine(a), Value::VecIndex(b)) => {
                Value::VecG1Affine(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG1Affine(a), Value::Index(b)) => Value::G1Affine(a[b]),
            (Value::VecG2Affine(a), Value::VecIndex(b)) => {
                Value::VecG2Affine(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecG2Affine(a), Value::Index(b)) => Value::G2Affine(a[b]),
            (Value::Vec(a), Value::VecIndex(b)) => {
                Value::Vec(b.par_iter().map(|i| a[*i].clone()).collect())
            }
            (Value::Vec(a), Value::Index(b)) => a[b].clone(),
            (Value::Vec(a), Value::Vec(b)) => {
                Value::Vec(b.par_iter().map(|i| a[i.into_index()].clone()).collect())
            }
            (Value::Record(_), _) => {
                panic!(
                    "Records do not support indexed access. Use direct field access (record.field) instead."
                )
            }
            (a, b) => panic!("Cannot do {}[{}]", a, b),
        }
    }

    #[inline]
    pub fn eval(self, other: &mut Self) {
        match (&self, &other) {
            (Value::Poly(poly), Value::VecIndex(b)) => {
                let n_points = b.len();
                let points: Vec<C::F> = b.iter().map(|i| C::FOps::from_usize(*i)).collect();

                let uni_input = poly.is_univariate();
                let result_poly = if uni_input {
                    poly.evaluate_vec(&points)
                } else if let Ok(scalar) = poly.evaluate_mv(&points) {
                    VirtualPolynomial::from_scalar(scalar)
                } else {
                    poly.evaluate_or_fix_mle(&points)
                        .expect("MLE evaluation failed")
                };

                *other = if let Some(scalar) = result_poly.to_scalar() {
                    if n_points == 1 {
                        Value::VecScalar(vec![scalar])
                    } else {
                        Value::Scalar(scalar)
                    }
                } else if uni_input {
                    if let Some(vec) = result_poly.to_vec() {
                        Value::VecScalar(vec)
                    } else {
                        Value::Poly(result_poly)
                    }
                } else {
                    Value::Poly(result_poly)
                };
            }
            (Value::Poly(poly), Value::VecScalar(v)) => {
                let n_points = v.len();
                let uni_input = poly.is_univariate();
                let result_poly = if uni_input {
                    poly.evaluate_vec(v)
                } else if let Ok(scalar) = poly.evaluate_mv(v) {
                    VirtualPolynomial::from_scalar(scalar)
                } else {
                    poly.evaluate_or_fix_mle(v).expect("MLE evaluation failed")
                };

                *other = if let Some(scalar) = result_poly.to_scalar() {
                    if n_points == 1 {
                        Value::VecScalar(vec![scalar])
                    } else {
                        Value::Scalar(scalar)
                    }
                } else if uni_input {
                    if let Some(vec) = result_poly.to_vec() {
                        Value::VecScalar(vec)
                    } else {
                        Value::Poly(result_poly)
                    }
                } else {
                    Value::Poly(result_poly)
                };
            }
            _ => panic!("Cannot eval if not poly or index"),
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
                    *r = Value::VecIndex(a.iter().copied().chain(std::iter::once(*b)).collect())
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
            _ => panic!("Not implemented"),
        }
    }

    /// Generate a random value, given some parameters
    pub fn random<R: Rng + Sized>(rng: &mut R, typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Bool) => Value::Bool(rng.next_u32().is_multiple_of(2)),
            ATyp::Base(ABase::Fin(r)) => Value::Index(r.random(rng) % 10),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::FOps::rand(rng)),
            ATyp::Base(ABase::G1) => Value::G1(C::G1Ops::rand(rng)),
            ATyp::Base(ABase::G2) => Value::G2(C::G2Ops::rand(rng)),
            ATyp::Base(ABase::GT) => Value::GT(C::POps::rand(rng)),
            ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n) => {
                Value::VecIndex((0..*n).map(|_| r.random(rng)).collect())
            }
            ATyp::Vec(box ATyp::Base(ABase::Scalar), n) => {
                Value::VecScalar(C::FOps::vec_rand(rng, *n))
            }
            ATyp::Vec(box ATyp::Base(ABase::G1), n) => Value::VecG1(C::G1Ops::vec_rand(rng, *n)),
            ATyp::Vec(box ATyp::Base(ABase::G2), n) => Value::VecG2(C::G2Ops::vec_rand(rng, *n)),
            ATyp::Vec(box ATyp::Base(ABase::GT), n) => Value::VecGT(C::POps::vec_rand(rng, *n)),
            ATyp::Vec(box t, n) => Value::Vec((0..*n).map(|_| Self::random(rng, t)).collect()),
            // Univariate poly: m = max_degree, so m+1 coefficients.
            ATyp::Uni(m) => {
                let mut coeffs = C::FOps::vec_rand(rng, *m + 1);
                if *m > 0 {
                    while coeffs[*m].is_zero() {
                        coeffs[*m] = C::FOps::rand(rng);
                    }
                }
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                    DensePolynomial::from_coefficients_vec(coeffs),
                )))
            }
            // Multilinear extension on the {0,1}^n hypercube: 2^n evaluations.
            ATyp::Mle(n) => {
                let evals = C::FOps::vec_rand(rng, 1usize << *n);
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMultilinearExtension::from_evaluations_vec(*n, evals),
                )))
            }
            // n-variate poly, max total degree m. For n <= 1 produce a
            // univariate of degree m; otherwise a multilinear extension as
            // a representative inhabitant of the type.
            ATyp::VPoly(n, m) => {
                if *n <= 1 {
                    let mut coeffs = C::FOps::vec_rand(rng, *m + 1);
                    if *m > 0 {
                        while coeffs[*m].is_zero() {
                            coeffs[*m] = C::FOps::rand(rng);
                        }
                    }
                    Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                        DensePolynomial::from_coefficients_vec(coeffs),
                    )))
                } else {
                    let evals = C::FOps::vec_rand(rng, 1usize << *n);
                    Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                        DenseMultilinearExtension::from_evaluations_vec(*n, evals),
                    )))
                }
            }
            ATyp::Record(fields) => {
                let mut record_fields = Ctx::new();
                for (name, field_typ) in fields.iter() {
                    let v = Self::random(rng, field_typ);
                    record_fields.insert(name, &v);
                }
                Value::Record(record_fields)
            }
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
            Value::Record(fields) => {
                let mut atyp_fields = Ctx::new();
                for (name, value) in fields.iter() {
                    let t = value.typ();
                    atyp_fields.insert(name, &t);
                }
                ATyp::Record(atyp_fields)
            }
            Value::Poly(poly) => {
                if poly.is_univariate() {
                    ATyp::uni(poly.degree())
                } else {
                    ATyp::mle(poly.num_vars().unwrap())
                }
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
    pub fn into_poly(&self) -> &VirtualPolynomial<C::F> {
        match self {
            Value::Poly(p) => p,
            _ => panic!("Expected poly, found {}", self),
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
            Value::Vec(v) => {
                *self = Value::VecG1(
                    v.iter()
                        .map(|val| match val {
                            Value::G1(g) => *g,
                            Value::G1Affine(g) => (*g).into(),
                            _ => panic!("Expected G1 element in vec, found {}", val),
                        })
                        .collect(),
                );
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
            Value::Vec(v) => {
                *self = Value::VecG2(
                    v.iter()
                        .map(|val| match val {
                            Value::G2(g) => *g,
                            Value::G2Affine(g) => (*g).into(),
                            _ => panic!("Expected G2 element in vec, found {}", val),
                        })
                        .collect(),
                );
                self.into_vec_g2_mut()
            }
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }
    pub fn into_vec_gt_mut(&mut self) -> &mut Vec<PairingOutput<C::P>> {
        match self {
            Value::VecGT(v) => v,
            Value::Vec(v) => {
                *self = Value::VecGT(
                    v.iter()
                        .map(|val| match val {
                            Value::GT(g) => *g,
                            _ => panic!("Expected GT element in vec, found {}", val),
                        })
                        .collect(),
                );
                self.into_vec_gt_mut()
            }
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
            Value::Vec(v) => {
                *self = Value::VecBool(
                    v.iter()
                        .map(|val| match val {
                            Value::Bool(b) => *b,
                            _ => panic!("Expected Bool element in vec, found {}", val),
                        })
                        .collect(),
                );
                self.into_vec_bool_mut()
            }
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
        matches!(
            self,
            Value::Vec(_)
                | Value::VecBool(_)
                | Value::VecScalar(_)
                | Value::VecG1(_)
                | Value::VecG2(_)
                | Value::VecGT(_)
                | Value::VecG1Affine(_)
                | Value::VecG2Affine(_)
                | Value::VecIndex(_)
        )
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
            Value::Record(fields) => fields.iter().all(|(_, v)| v.is_zero()),
            Value::Poly(poly) => poly.is_zero(),
        }
    }

    pub fn value_vec(vec: Vec<Self>) -> Self {
        let mut typ = vec[0].typ();
        for i in vec.iter().skip(1) {
            typ = ATyp::lub_equ(&i.typ(), &typ, &Nothing).unwrap();
        }
        let mut vec_value = Value::Vec(vec);
        match typ {
            ATyp::Base(ABase::Scalar) => {
                vec_value.into_vec_scalar_mut();
                vec_value
            }
            ATyp::Base(ABase::Bool) => {
                vec_value.into_vec_bool_mut();
                vec_value
            }
            ATyp::Base(ABase::Fin(_r)) => match vec_value {
                Value::Vec(v) => Value::VecIndex(v.into_iter().map(|i| i.into_index()).collect()),
                Value::VecIndex(_) => vec_value,
                _ => panic!("Expected Vec or VecIndex, found {}", vec_value),
            },
            ATyp::Base(ABase::G1) => {
                vec_value.into_vec_g1_mut();
                vec_value
            }
            ATyp::Base(ABase::G2) => {
                vec_value.into_vec_g2_mut();
                vec_value
            }
            ATyp::Base(ABase::GT) => {
                vec_value.into_vec_gt_mut();
                vec_value
            }
            ATyp::Uni(_) | ATyp::Mle(_) | ATyp::VPoly(_, _) | ATyp::Record(_) | ATyp::Vec(_, _) => {
                vec_value
            }
        }
    }

    pub fn value_coef(&self) -> Self {
        match self {
            Value::Poly(p) => {
                let coeffs = p
                    .to_coeffs()
                    .expect("Can only get coefficients from univariate polynomials");
                Value::VecScalar(coeffs)
            }
            // `Uni` values are often represented directly as coefficient vectors already.
            Value::VecScalar(v) => Value::VecScalar(v.clone()),
            Value::VecIndex(v) => {
                Value::VecScalar(v.iter().map(|i| C::FOps::from_usize(*i)).collect())
            }
            _ => panic!("Expected poly or coefficient vector, found {}", self),
        }
    }

    pub fn value_poly(&self) -> Self {
        match self {
            Value::VecScalar(v) => Value::Poly(VirtualPolynomial::from_poly(
                PolyVariant::from_coeffs(v.clone()),
            )),
            Value::VecIndex(v) => {
                let coeffs = v.iter().map(|i| C::FOps::from_usize(*i)).collect();
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::from_coeffs(
                    coeffs,
                )))
            }
            _ => panic!("Expected vec scalar, found {}", self),
        }
    }

    pub fn value_mle(&self) -> Self {
        match self {
            Value::VecScalar(v) => {
                let mut mle = vec![];
                for i in v.iter() {
                    mle.push(*i);
                }
                let size = log2(mle.len());
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMultilinearExtension::<C::F>::from_evaluations_vec(size as usize, mle),
                )))
            }
            Value::VecIndex(v) => {
                let mut mle = vec![];
                for i in v.iter() {
                    mle.push(C::FOps::from_usize(*i));
                }
                let size = log2(mle.len());
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMultilinearExtension::<C::F>::from_evaluations_vec(size as usize, mle),
                )))
            }
            _ => panic!("Expected vec scalar or vec index, found {}", self),
        }
    }

    pub fn value_interpolate(&self, points: Option<&Self>) -> Self {
        let evals = value_as_scalar_vec::<C>(self);
        assert!(
            !evals.is_empty(),
            "interpolate expects non-empty evaluations"
        );

        match points {
            None => {
                let mut coeffs = evals;
                C::FOps::vec_ifft(&mut coeffs);
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                    DensePolynomial { coeffs },
                )))
            }
            Some(points) => {
                let xs = value_as_scalar_vec::<C>(points);
                assert_eq!(
                    xs.len(),
                    evals.len(),
                    "interpolate expects points and evaluations with same length"
                );

                if are_fft_domain_points::<C>(&xs) {
                    let mut coeffs = evals;
                    C::FOps::vec_ifft(&mut coeffs);
                    return Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                        DensePolynomial { coeffs },
                    )));
                }

                let coeffs = interpolate_univariate_from_points::<C::F>(&xs, &evals);
                Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                    DensePolynomial { coeffs },
                )))
            }
        }
    }

    pub fn value_fft(&self) -> Self {
        match self {
            Value::Poly(p) => {
                let poly = p
                    .normalize()
                    .expect("Failed to normalize polynomial for fft");
                match poly {
                    PolyVariant::DenseMle(mle) => Value::VecScalar(mle.evaluations),
                    _ => {
                        let mut coeffs = poly
                            .to_coeffs()
                            .expect("Can only fft univariate polynomial or mle");
                        C::FOps::vec_fft(&mut coeffs);
                        Value::VecScalar(coeffs)
                    }
                }
            }
            _ => panic!("Expected polynomial value, found {}", self),
        }
    }

    /// Reduce a vector using a binary operation.
    /// Commutative operations (Add, Mul, And) use parallel fold via rayon.
    /// Non-commutative operations use sequential left fold.
    pub fn value_reduce(self, op: BinOp) -> Self {
        let elements = self.into_elements();
        assert!(!elements.is_empty(), "Cannot reduce empty vector");
        match op {
            BinOp::Add => {
                let elem_typ = elements[0].typ();
                elements
                    .into_par_iter()
                    .reduce(|| Value::<C>::zero(&elem_typ), |a, b| a + b)
            }
            BinOp::Mul => {
                let elem_typ = elements[0].typ();
                elements
                    .into_par_iter()
                    .reduce(|| Value::<C>::one(&elem_typ), |a, b| a * b)
            }
            BinOp::And => {
                let elem_typ = elements[0].typ();
                elements
                    .into_par_iter()
                    .reduce(|| Value::<C>::one(&elem_typ), |a, b| a & b)
            }
            _ => {
                let mut iter = elements.into_iter();
                let first = iter.next().unwrap();
                iter.fold(first, |acc, x| match op {
                    BinOp::Sub => acc - x,
                    BinOp::Div => acc / x,
                    BinOp::Pow => acc ^ x,
                    BinOp::Rem => acc % x,
                    BinOp::Dot => acc.dot(x),
                    BinOp::Concat => acc.value_concat(x),
                    BinOp::Equ => acc.value_equ(&x),
                    _ => unreachable!(),
                })
            }
        }
    }

    /// Convert a vector Value into a Vec of element Values.
    fn into_elements(self) -> Vec<Value<C>> {
        match self {
            Value::VecScalar(v) => v.into_iter().map(Value::Scalar).collect(),
            Value::VecIndex(v) => v.into_iter().map(Value::Index).collect(),
            Value::VecBool(v) => v.into_iter().map(Value::Bool).collect(),
            Value::VecG1(v) => v.into_iter().map(Value::G1).collect(),
            Value::VecG2(v) => v.into_iter().map(Value::G2).collect(),
            Value::VecGT(v) => v.into_iter().map(Value::GT).collect(),
            Value::VecG1Affine(v) => v.into_iter().map(Value::G1Affine).collect(),
            Value::VecG2Affine(v) => v.into_iter().map(Value::G2Affine).collect(),
            Value::Vec(v) => v,
            _ => panic!("Expected vector, found {}", self),
        }
    }
}

pub fn round_univariate_from_marginalize_evals<F: PrimeField>(evals: &[F]) -> VirtualPolynomial<F> {
    #![allow(clippy::needless_range_loop)]
    let n = evals.len();
    assert!(n > 0, "marginalize evaluations must be non-empty");
    if n == 1 {
        return VirtualPolynomial::from_poly(PolyVariant::DenseUni(
            DensePolynomial::from_coefficients_vec(vec![evals[0]]),
        ));
    }
    let mut aug: Vec<Vec<F>> = (0..n)
        .map(|i| {
            let xi = F::from(i as u64);
            let mut row = Vec::with_capacity(n + 1);
            let mut pow = F::one();
            for _ in 0..n {
                row.push(pow);
                pow *= xi;
            }
            row.push(evals[i]);
            row
        })
        .collect();
    for col in 0..n {
        let mut pivot = None;
        for row in col..n {
            if !aug[row][col].is_zero() {
                pivot = Some(row);
                break;
            }
        }
        let pr = pivot.expect("singular Vandermonde in round_univariate interpolation");
        aug.swap(col, pr);
        let inv = aug[col][col].inverse().unwrap();
        for j in col..=n {
            aug[col][j] *= inv;
        }
        for row in 0..n {
            if row != col {
                let factor = aug[row][col];
                if !factor.is_zero() {
                    let pivot_row: Vec<F> = aug[col][col..=n].to_vec();
                    for j in col..=n {
                        aug[row][j] -= factor * pivot_row[j - col];
                    }
                }
            }
        }
    }
    let coeffs: Vec<F> = (0..n).map(|i| aug[i][n]).collect();
    VirtualPolynomial::from_poly(PolyVariant::DenseUni(
        DensePolynomial::from_coefficients_vec(coeffs),
    ))
}

fn value_as_scalar_vec<C: ArkConfig>(v: &Value<C>) -> Vec<C::F> {
    match v {
        Value::VecScalar(xs) => xs.clone(),
        Value::VecIndex(xs) => xs.iter().map(|i| C::FOps::from_usize(*i)).collect(),
        _ => panic!("Expected scalar vector, found {}", v),
    }
}

fn are_fft_domain_points<C: ArkConfig>(points: &[C::F]) -> bool {
    let Some(domain) = GeneralEvaluationDomain::<C::F>::new(points.len()) else {
        return false;
    };
    domain.elements().zip(points.iter()).all(|(a, b)| a == *b)
}

fn interpolate_univariate_from_points<F: PrimeField>(points: &[F], evals: &[F]) -> Vec<F> {
    let n = points.len();
    assert_eq!(n, evals.len(), "point/eval length mismatch");
    assert!(n > 0, "cannot interpolate empty point set");

    let mut prod = vec![F::one()];
    for &x in points {
        let mut next = vec![F::zero(); prod.len() + 1];
        for (i, &c) in prod.iter().enumerate() {
            next[i] -= c * x;
            next[i + 1] += c;
        }
        prod = next;
    }

    let mut coeffs = vec![F::zero(); n];
    for i in 0..n {
        let xi = points[i];
        let mut denom = F::one();
        for (j, &xj) in points.iter().enumerate() {
            if i != j {
                denom *= xi - xj;
            }
        }
        assert!(!denom.is_zero(), "interpolation points must be distinct");

        let qi = divide_by_x_minus_a(&prod, xi);
        let scale = evals[i] * denom.inverse().unwrap();
        for (k, qk) in qi.iter().enumerate() {
            coeffs[k] += *qk * scale;
        }
    }

    coeffs
}

fn divide_by_x_minus_a<F: PrimeField>(p: &[F], a: F) -> Vec<F> {
    assert!(p.len() >= 2, "polynomial degree must be at least 1");
    let n = p.len() - 1;
    let mut q = vec![F::zero(); n];
    q[n - 1] = p[n];
    for k in (1..n).rev() {
        q[k - 1] = p[k] + a * q[k];
    }
    q
}

pub fn eval_univariate_from_evals_0d<F: PrimeField>(evals: &[F], x: F) -> F {
    let g = round_univariate_from_marginalize_evals::<F>(evals);
    g.evaluate_uv(&x)
}

pub fn marginalize<C: ArkConfig>(
    poly: &VirtualPolynomial<C::F>,
    num_variables: usize,
    max_degree: usize,
    round: usize,
    challenge: Option<C::F>,
) -> (Vec<C::F>, VirtualPolynomial<C::F>) {
    #![allow(clippy::needless_range_loop)]
    // if self.round >= self.poly.aux_info.num_variables
    if num_variables == 0 {
        panic!("marginalize: num_variables must be > 0");
    }

    if let Some(n) = poly.num_vars() {
        let expected_current_vars = if round == 0 {
            num_variables
        } else {
            num_variables.saturating_sub(round - 1)
        };
        if n != expected_current_vars {
            panic!(
                "marginalize: num_variables mismatch: polynomial has {}, expected {} (num_variables={}, round={})",
                n, expected_current_vars, num_variables, round
            );
        }
    }

    // Step 1:
    // fix argument and evaluate f(x) over x_m = r; where r is the challenge
    // for the current round, and m is the round number, indexed from 1
    //
    // i.e.:
    // at round m <= n, for each mle g(x_1, ... x_n) within the flattened_mle
    // which has already been evaluated to g(r_1, ..., r_{m-1}, x_m ... x_n)
    //
    //    g(r_1, ..., r_{m-1}, x_m ... x_n)
    //
    // eval g over r_m, and mutate g to g(r_1, ... r_m, x_{m+1}... x_n)
    let next_poly = if round == 0 {
        poly.clone()
    } else if let Some(r) = challenge {
        poly.fix_first_mle_variables_factorwise(&[r])
            .unwrap_or_else(|e| {
                panic!(
                    "marginalize: failed to fix polynomial for round {} with challenge {:?} \
                     (num_variables={}, max_degree={}): {:?}",
                    round, r, num_variables, max_degree, e
                )
            })
    } else {
        poly.clone()
    };

    // Step 2: generate sum for the partial evaluated polynomial:
    // f(r_1, ... r_m, x_{m+1}... x_n); we sum over the hypercube for the remaining
    let num_remaining_vars = num_variables.saturating_sub(round + 1);
    let total: usize = 1usize << num_remaining_vars;
    let expected_mle_vars = num_variables.saturating_sub(round);

    let all_mle = next_poly
        .flattened_polys
        .iter()
        .all(|p| p.as_mle_evaluations().is_some());
    let mle_tables: Option<Vec<&[C::F]>> = if all_mle && !next_poly.flattened_polys.is_empty() {
        let tables: Vec<&[C::F]> = next_poly
            .flattened_polys
            .iter()
            .filter_map(|p| p.as_mle_evaluations())
            .collect();
        if tables.len() == next_poly.flattened_polys.len()
            && tables
                .iter()
                .all(|t| t.len() == (1usize << expected_mle_vars))
        {
            Some(tables)
        } else {
            None
        }
    } else {
        None
    };

    let mut evaluations = vec![C::F::zero(); max_degree + 1];

    if let Some(tables) = mle_tables {
        let mut products_sum = vec![C::F::zero(); max_degree + 1];

        for (coefficient, products) in &next_poly.products {
            let mut coeff_acc = vec![C::F::zero(); max_degree + 1];
            let product_tables: Vec<&[C::F]> = products.iter().map(|&idx| tables[idx]).collect();
            let k = product_tables.len();

            let partials: Vec<Vec<C::F>> = (0..total)
                .into_par_iter()
                .map(|b| {
                    let v0: Vec<C::F> = product_tables.iter().map(|tab| tab[2 * b]).collect();
                    let v1: Vec<C::F> = product_tables.iter().map(|tab| tab[2 * b + 1]).collect();
                    // P(t) = prod_i ((1-t)*v0_i + t*v1_i); compute coeffs of P (degree k).
                    let mut coeffs = vec![C::F::zero(); k + 1];
                    coeffs[0] = C::F::one();
                    for i in 0..k {
                        let a = v0[i];
                        let b_i = v1[i] - v0[i];
                        for d in (1..=i + 1).rev() {
                            coeffs[d] = coeffs[d] * a + coeffs[d - 1] * b_i;
                        }
                        coeffs[0] *= a;
                    }
                    coeffs
                })
                .collect();

            for partial in partials {
                for (acc, &p) in coeff_acc.iter_mut().zip(partial.iter()) {
                    *acc += p;
                }
            }
            for (ps, &acc) in products_sum.iter_mut().zip(coeff_acc.iter()) {
                *ps += *coefficient * acc;
            }
        }

        for t_idx in 0..=max_degree {
            let t = C::FOps::from_usize(t_idx);
            let mut val = C::F::zero();
            let mut t_pow = C::F::one();
            for d in 0..=max_degree {
                val += products_sum[d] * t_pow;
                t_pow *= t;
            }
            evaluations[t_idx] = val;
        }
    } else {
        let point_len = num_variables - round;
        for t_idx in 0..=max_degree {
            let t = C::FOps::from_usize(t_idx);
            let sum: C::F = (0..total)
                .into_par_iter()
                .map(|b| {
                    let mut point: Vec<C::F> = Vec::with_capacity(point_len);
                    point.push(t);
                    for j in 0..num_remaining_vars {
                        let bit = (b >> j) & 1;
                        point.push(if bit == 0 { C::F::zero() } else { C::F::one() });
                    }
                    next_poly
                        .evaluate_mv(&point)
                        .expect("marginalize: polynomial evaluation failed")
                })
                .sum();
            evaluations[t_idx] = sum;
        }
    }

    (evaluations, next_poly)
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
            Value::Record(fields) => {
                write!(f, "{{|")?;
                for (i, (name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, value)?;
                }
                write!(f, "|}}")
            }
            Value::Poly(poly) => write!(f, "{}", poly),
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
        Some(self.cmp(other))
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
                    (Value::Poly(a), Value::Poly(b)) => a.cmp(b),
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
mod value_tests {
    use super::*;
    use crate::ArkBn254;
    use ark_bn254::{Fr, G1Projective, G2Projective};
    use ark_std::UniformRand;
    use rand::thread_rng;

    type TestConfig = ArkBn254;
    type TestValue = Value<TestConfig>;

    // Helper to create test values
    fn scalar(x: u64) -> TestValue {
        TestValue::Scalar(Fr::from(x))
    }

    fn vec_scalar(xs: &[u64]) -> TestValue {
        TestValue::VecScalar(xs.iter().map(|&x| Fr::from(x)).collect())
    }

    fn random_scalar() -> TestValue {
        TestValue::Scalar(Fr::rand(&mut thread_rng()))
    }

    fn random_g1() -> TestValue {
        TestValue::G1(G1Projective::rand(&mut thread_rng()))
    }

    fn random_g2() -> TestValue {
        TestValue::G2(G2Projective::rand(&mut thread_rng()))
    }

    // Helper trait to extract inner values
    trait IntoG1 {
        fn into_g1(self) -> G1Projective;
    }

    trait IntoG2 {
        fn into_g2(self) -> G2Projective;
    }

    impl IntoG1 for TestValue {
        fn into_g1(self) -> G1Projective {
            match self {
                TestValue::G1(g) => g,
                _ => panic!("Expected G1"),
            }
        }
    }

    impl IntoG2 for TestValue {
        fn into_g2(self) -> G2Projective {
            match self {
                TestValue::G2(g) => g,
                _ => panic!("Expected G2"),
            }
        }
    }

    // ========== Addition Laws ==========

    #[test]
    fn test_scalar_add_associativity() {
        let a = scalar(5);
        let b = scalar(7);
        let c = scalar(11);
        assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
    }

    #[test]
    fn test_scalar_add_commutativity() {
        let a = scalar(5);
        let b = scalar(7);
        assert_eq!(a.clone() + b.clone(), b + a);
    }

    #[test]
    fn test_scalar_add_identity() {
        let a = scalar(5);
        let zero = scalar(0);
        assert_eq!(a.clone() + zero.clone(), a.clone());
        assert_eq!(zero + a.clone(), a);
    }

    #[test]
    fn test_vec_scalar_add_associativity() {
        let a = vec_scalar(&[1, 2, 3]);
        let b = vec_scalar(&[4, 5, 6]);
        let c = vec_scalar(&[7, 8, 9]);
        assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
    }

    #[test]
    fn test_vec_scalar_add_commutativity() {
        let a = vec_scalar(&[1, 2, 3]);
        let b = vec_scalar(&[4, 5, 6]);
        assert_eq!(a.clone() + b.clone(), b + a);
    }

    #[test]
    fn test_g1_add_associativity() {
        let a = random_g1();
        let b = random_g1();
        let c = random_g1();
        assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
    }

    #[test]
    fn test_g1_add_commutativity() {
        let a = random_g1();
        let b = random_g1();
        assert_eq!(a.clone() + b.clone(), b + a);
    }

    #[test]
    fn test_g2_add_associativity() {
        let a = random_g2();
        let b = random_g2();
        let c = random_g2();
        assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
    }

    #[test]
    fn test_g2_add_commutativity() {
        let a = random_g2();
        let b = random_g2();
        assert_eq!(a.clone() + b.clone(), b + a);
    }

    // ========== Multiplication Laws ==========

    #[test]
    fn test_scalar_mul_associativity() {
        let a = scalar(5);
        let b = scalar(7);
        let c = scalar(11);
        assert_eq!((a.clone() * b.clone()) * c.clone(), a * (b * c));
    }

    #[test]
    fn test_scalar_mul_commutativity() {
        let a = scalar(5);
        let b = scalar(7);
        assert_eq!(a.clone() * b.clone(), b * a);
    }

    #[test]
    fn test_scalar_mul_identity() {
        let a = scalar(5);
        let one = scalar(1);
        assert_eq!(a.clone() * one.clone(), a.clone());
        assert_eq!(one * a.clone(), a);
    }

    #[test]
    fn test_scalar_mul_zero() {
        let a = scalar(5);
        let zero = scalar(0);
        assert_eq!(a * zero, scalar(0));
    }

    #[test]
    fn test_vec_scalar_mul_commutativity() {
        let a = vec_scalar(&[1, 2, 3]);
        let b = vec_scalar(&[4, 5, 6]);
        assert_eq!(a.clone() * b.clone(), b * a);
    }

    // ========== Distributivity Laws ==========

    #[test]
    fn test_scalar_distributivity_left() {
        let a = scalar(5);
        let b = scalar(7);
        let c = scalar(11);
        assert_eq!(
            a.clone() * (b.clone() + c.clone()),
            (a.clone() * b) + (a * c)
        );
    }

    #[test]
    fn test_scalar_distributivity_right() {
        let a = scalar(5);
        let b = scalar(7);
        let c = scalar(11);
        assert_eq!(
            (a.clone() + b.clone()) * c.clone(),
            (a * c.clone()) + (b * c)
        );
    }

    #[test]
    fn test_vec_scalar_distributivity_left() {
        let a = vec_scalar(&[1, 2, 3]);
        let b = vec_scalar(&[4, 5, 6]);
        let c = vec_scalar(&[7, 8, 9]);
        assert_eq!(
            a.clone() * (b.clone() + c.clone()),
            (a.clone() * b) + (a * c)
        );
    }

    #[test]
    fn test_vec_scalar_distributivity_right() {
        let a = vec_scalar(&[1, 2, 3]);
        let b = vec_scalar(&[4, 5, 6]);
        let c = vec_scalar(&[7, 8, 9]);
        assert_eq!(
            (a.clone() + b.clone()) * c.clone(),
            (a * c.clone()) + (b * c)
        );
    }

    // ========== Subtraction Laws ==========

    #[test]
    fn test_scalar_sub_identity() {
        let a = scalar(5);
        assert_eq!(a.clone() - a, scalar(0));
    }

    #[test]
    fn test_vec_scalar_sub_identity() {
        let a = vec_scalar(&[1, 2, 3]);
        assert_eq!(a.clone() - a, vec_scalar(&[0, 0, 0]));
    }

    // ========== Scalar Multiplication (Group Action) ==========

    #[test]
    fn test_g1_scalar_mul_distributivity_scalars() {
        let g = random_g1();
        let a = random_scalar();
        let b = random_scalar();

        // (a + b) * G = a * G + b * G
        let lhs = (a.clone() + b.clone()) * g.clone();
        let rhs = (a * g.clone()) + (b * g);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g1_scalar_mul_distributivity_points() {
        let g1 = random_g1();
        let g2 = random_g1();
        let a = random_scalar();

        // a * (G1 + G2) = a * G1 + a * G2
        let lhs = a.clone() * (g1.clone() + g2.clone());
        let rhs = (a.clone() * g1) + (a * g2);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g2_scalar_mul_distributivity_scalars() {
        let g = random_g2();
        let a = random_scalar();
        let b = random_scalar();

        // (a + b) * G = a * G + b * G
        let lhs = (a.clone() + b.clone()) * g.clone();
        let rhs = (a * g.clone()) + (b * g);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g2_scalar_mul_distributivity_points() {
        let g1 = random_g2();
        let g2 = random_g2();
        let a = random_scalar();

        // a * (G1 + G2) = a * G1 + a * G2
        let lhs = a.clone() * (g1.clone() + g2.clone());
        let rhs = (a.clone() * g1) + (a * g2);
        assert_eq!(lhs, rhs);
    }

    // ========== Boolean Operations ==========

    #[test]
    fn test_bool_and_commutativity() {
        let a = TestValue::Bool(true);
        let b = TestValue::Bool(false);
        assert_eq!(a.clone() & b.clone(), b & a);
    }

    #[test]
    fn test_bool_or_commutativity() {
        let a = TestValue::Bool(true);
        let b = TestValue::Bool(false);
        assert_eq!(a.clone() | b.clone(), b | a);
    }

    #[test]
    fn test_bool_and_identity() {
        let a = TestValue::Bool(true);
        let true_val = TestValue::Bool(true);
        assert_eq!(a.clone() & true_val, a);
    }

    #[test]
    fn test_bool_or_identity() {
        let a = TestValue::Bool(false);
        let false_val = TestValue::Bool(false);
        assert_eq!(a.clone() | false_val, a);
    }

    // ========== Index Operations ==========

    #[test]
    fn test_index_add() {
        let a = TestValue::Index(5);
        let b = TestValue::Index(7);
        assert_eq!(a + b, TestValue::Index(12));
    }

    #[test]
    fn test_index_mul() {
        let a = TestValue::Index(5);
        let b = TestValue::Index(7);
        assert_eq!(a * b, TestValue::Index(35));
    }

    #[test]
    fn test_vec_index_add() {
        let a = TestValue::VecIndex(vec![1, 2, 3]);
        let b = TestValue::VecIndex(vec![4, 5, 6]);
        assert_eq!(a + b, TestValue::VecIndex(vec![5, 7, 9]));
    }

    // ========== Field Axioms for Division ==========

    #[test]
    fn test_scalar_div_mul_identity() {
        // (a / b) * b = a (when b ≠ 0)
        let a = scalar(42);
        let b = scalar(7);
        let result = (a.clone() / b.clone()) * b;
        assert_eq!(result, a);
    }

    #[test]
    fn test_scalar_multiplicative_inverse() {
        // a * (1/a) = 1 (when a ≠ 0)
        let a = scalar(5);
        let one = scalar(1);
        let a_inv = one.clone() / a.clone();
        assert_eq!(a * a_inv, one);
    }

    #[test]
    fn test_scalar_div_by_one() {
        // a / 1 = a
        let a = scalar(42);
        let one = scalar(1);
        assert_eq!(a.clone() / one, a);
    }

    #[test]
    fn test_scalar_div_self() {
        // a / a = 1 (when a ≠ 0)
        let a = scalar(7);
        assert_eq!(a.clone() / a, scalar(1));
    }

    #[test]
    fn test_vec_scalar_div_consistency() {
        // Division of vectors should be element-wise
        let a = vec_scalar(&[10, 20, 30]);
        let b = vec_scalar(&[2, 4, 5]);
        let result = a / b;
        assert_eq!(result, vec_scalar(&[5, 5, 6]));
    }

    #[test]
    fn test_index_div() {
        // Index / Index = Index
        let a = TestValue::Index(42);
        let b = TestValue::Index(7);
        assert_eq!(a / b, TestValue::Index(6));
    }

    #[test]
    fn test_index_coerce_div() {
        // Index should coerce to scalar in division
        let a = TestValue::Index(10);
        let b = scalar(2);
        let result = a / b;
        assert_eq!(result, scalar(5));
    }

    #[test]
    fn test_vec_index_div() {
        // a / b computes b = b / a (mutates second operand)
        let a = TestValue::VecIndex(vec![2, 4, 5]);
        let b = TestValue::VecIndex(vec![10, 20, 30]);
        assert_eq!(a / b, TestValue::VecIndex(vec![5, 5, 6]));
    }

    // ========== Group Identity Elements ==========

    #[test]
    fn test_g1_additive_identity() {
        let a = random_g1();
        let zero = TestValue::G1(G1Projective::zero());
        assert_eq!(a.clone() + zero.clone(), a.clone());
        assert_eq!(zero + a.clone(), a);
    }

    #[test]
    fn test_g2_additive_identity() {
        let a = random_g2();
        let zero = TestValue::G2(G2Projective::zero());
        assert_eq!(a.clone() + zero.clone(), a.clone());
        assert_eq!(zero + a.clone(), a);
    }

    #[test]
    fn test_gt_additive_identity() {
        use ark_ec::pairing::Pairing;
        let a_g1 = random_g1();
        let a_g2 = random_g2();
        let mut a = a_g2.clone();
        a_g1.value_pair(&mut a);

        let b_g1 = random_g1();
        let b_g2 = random_g2();
        let mut b = b_g2.clone();
        b_g1.value_pair(&mut b);

        // Test GT identity (zero in multiplicative group)
        let zero_gt = TestValue::GT(ark_bn254::Bn254::pairing(
            G1Projective::zero(),
            G2Projective::zero(),
        ));

        // GT is multiplicative, so zero_gt acts as zero in addition
        let result = a.clone() + zero_gt.clone();
        assert_eq!(result, a);
    }

    // ========== Group Inverse Properties ==========

    #[test]
    fn test_g1_additive_inverse() {
        // a + (-a) = 0
        let a = random_g1();
        let result = a.clone() - a;
        let zero = TestValue::G1(G1Projective::zero());
        assert_eq!(result, zero);
    }

    #[test]
    fn test_g2_additive_inverse() {
        // a + (-a) = 0
        let a = random_g2();
        let result = a.clone() - a;
        let zero = TestValue::G2(G2Projective::zero());
        assert_eq!(result, zero);
    }

    #[test]
    fn test_scalar_additive_inverse() {
        // a + (-a) = 0
        let a = scalar(42);
        let result = a.clone() - a;
        assert_eq!(result, scalar(0));
    }

    #[test]
    fn test_vec_scalar_additive_inverse() {
        let a = vec_scalar(&[1, 2, 3, 4]);
        let result = a.clone() - a;
        assert_eq!(result, vec_scalar(&[0, 0, 0, 0]));
    }

    // ========== Subtraction Anti-commutativity ==========

    #[test]
    fn test_scalar_sub_anticommutativity() {
        // a - b = -(b - a)
        let a = scalar(10);
        let b = scalar(3);
        let lhs = a.clone() - b.clone();
        let rhs = scalar(0) - (b - a);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_vec_scalar_sub_anticommutativity() {
        let a = vec_scalar(&[10, 20, 30]);
        let b = vec_scalar(&[3, 5, 7]);
        let lhs = a.clone() - b.clone();
        let rhs_temp = b - a;
        let zero = vec_scalar(&[0, 0, 0]);
        let rhs = zero - rhs_temp;
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g1_sub_anticommutativity() {
        let a = random_g1();
        let b = random_g1();
        let lhs = a.clone() - b.clone();
        let rhs_temp = b - a;
        let zero = TestValue::G1(G1Projective::zero());
        let rhs = zero - rhs_temp;
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g2_sub_anticommutativity() {
        let a = random_g2();
        let b = random_g2();
        let lhs = a.clone() - b.clone();
        let rhs_temp = b - a;
        let zero = TestValue::G2(G2Projective::zero());
        let rhs = zero - rhs_temp;
        assert_eq!(lhs, rhs);
    }

    // ========== Subtraction Relation to Addition ==========

    #[test]
    fn test_scalar_sub_as_neg_add() {
        // a - b = a + (-b), where -b = 0 - b
        let a = scalar(10);
        let b = scalar(3);
        let lhs = a.clone() - b.clone();
        let neg_b = scalar(0) - b;
        let rhs = a + neg_b;
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_vec_scalar_sub_as_neg_add() {
        let a = vec_scalar(&[10, 20, 30]);
        let b = vec_scalar(&[3, 5, 7]);
        let lhs = a.clone() - b.clone();
        let neg_b = vec_scalar(&[0, 0, 0]) - b;
        let rhs = a + neg_b;
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g1_sub_as_neg_add() {
        let a = random_g1();
        let b = random_g1();
        let lhs = a.clone() - b.clone();
        let neg_b = TestValue::G1(G1Projective::zero()) - b;
        let rhs = a + neg_b;
        assert_eq!(lhs, rhs);
    }

    // ========== Index Operations ==========

    #[test]
    fn test_index_sub() {
        let a = TestValue::Index(10);
        let b = TestValue::Index(3);
        assert_eq!(a - b, TestValue::Index(7));
    }

    #[test]
    fn test_index_mul_associativity() {
        let a = TestValue::Index(2);
        let b = TestValue::Index(3);
        let c = TestValue::Index(5);
        assert_eq!((a.clone() * b.clone()) * c.clone(), a * (b * c));
    }

    #[test]
    fn test_index_mul_commutativity() {
        let a = TestValue::Index(5);
        let b = TestValue::Index(7);
        assert_eq!(a.clone() * b.clone(), b * a);
    }

    #[test]
    fn test_index_mul_identity() {
        let a = TestValue::Index(42);
        let one = TestValue::Index(1);
        assert_eq!(a.clone() * one.clone(), a.clone());
        assert_eq!(one * a.clone(), a);
    }

    #[test]
    fn test_index_mul_zero() {
        let a = TestValue::Index(42);
        let zero = TestValue::Index(0);
        assert_eq!(a * zero, TestValue::Index(0));
    }

    #[test]
    fn test_vec_index_sub() {
        let a = TestValue::VecIndex(vec![10, 20, 30]);
        let b = TestValue::VecIndex(vec![3, 5, 7]);
        assert_eq!(a - b, TestValue::VecIndex(vec![7, 15, 23]));
    }

    #[test]
    fn test_vec_index_mul() {
        let a = TestValue::VecIndex(vec![2, 3, 4]);
        let b = TestValue::VecIndex(vec![5, 6, 7]);
        assert_eq!(a * b, TestValue::VecIndex(vec![10, 18, 28]));
    }

    // ========== Remainder Operations ==========

    #[test]
    fn test_index_rem() {
        let a = TestValue::Index(17);
        let b = TestValue::Index(5);
        assert_eq!(a % b, TestValue::Index(2));
    }

    #[test]
    fn test_vec_index_rem() {
        let a = TestValue::VecIndex(vec![17, 23, 31]);
        let b = TestValue::VecIndex(vec![5, 7, 10]);
        assert_eq!(a % b, TestValue::VecIndex(vec![2, 2, 1]));
    }

    #[test]
    fn test_index_rem_by_scalar() {
        let a = TestValue::VecIndex(vec![17, 23, 31]);
        let b = TestValue::Index(5);
        assert_eq!(a % b, TestValue::VecIndex(vec![2, 3, 1]));
    }

    #[test]
    fn test_scalar_rem_by_index() {
        // a % b computes b % a (mutates second operand)
        let a = TestValue::Index(17);
        let b = TestValue::VecIndex(vec![5, 7, 10]);
        assert_eq!(a % b, TestValue::VecIndex(vec![5, 7, 10]));
    }

    // ========== Mixed Operations: Index Coercion ==========

    #[test]
    fn test_index_scalar_add() {
        // Index should coerce to scalar
        let idx = TestValue::Index(5);
        let scal = scalar(7);
        let result = idx + scal;
        assert_eq!(result, scalar(12));
    }

    #[test]
    fn test_scalar_index_add() {
        // scalar + index: index coerces to scalar
        let scal = scalar(7);
        let idx = TestValue::Index(5);
        let result = scal + idx;
        assert_eq!(result, scalar(12));
    }

    #[test]
    fn test_index_scalar_mul() {
        let idx = TestValue::Index(5);
        let scal = scalar(7);
        let result = idx * scal;
        assert_eq!(result, scalar(35));
    }

    #[test]
    fn test_index_scalar_sub() {
        let idx = TestValue::Index(10);
        let scal = scalar(3);
        let result = idx - scal;
        assert_eq!(result, scalar(7));
    }

    #[test]
    fn test_scalar_index_sub() {
        // scalar - index: index coerces to scalar
        let scal = scalar(10);
        let idx = TestValue::Index(3);
        let result = scal - idx;
        assert_eq!(result, scalar(7));
    }

    // ========== Scalar Multiplication of Groups (Edge Cases) ==========

    #[test]
    fn test_g1_scalar_mul_zero() {
        let g = random_g1();
        let zero = scalar(0);
        let result = zero * g;
        assert_eq!(result, TestValue::G1(G1Projective::zero()));
    }

    #[test]
    fn test_g2_scalar_mul_zero() {
        let g = random_g2();
        let zero = scalar(0);
        let result = zero * g;
        assert_eq!(result, TestValue::G2(G2Projective::zero()));
    }

    #[test]
    fn test_g1_scalar_mul_one() {
        let g = random_g1();
        let one = scalar(1);
        let result = one * g.clone();
        assert_eq!(result, g);
    }

    #[test]
    fn test_g2_scalar_mul_one() {
        let g = random_g2();
        let one = scalar(1);
        let result = one * g.clone();
        assert_eq!(result, g);
    }

    #[test]
    fn test_g1_scalar_mul_associativity() {
        // (a * b) * G = a * (b * G)
        let g = random_g1();
        let a = scalar(3);
        let b = scalar(5);
        let lhs = (a.clone() * b.clone()) * g.clone();
        let rhs = a * (b * g);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g2_scalar_mul_associativity() {
        // (a * b) * G = a * (b * G)
        let g = random_g2();
        let a = scalar(3);
        let b = scalar(5);
        let lhs = (a.clone() * b.clone()) * g.clone();
        let rhs = a * (b * g);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g1_index_mul() {
        // Index should coerce to scalar for group multiplication
        let g = random_g1();
        let idx = TestValue::Index(5);
        let scal = scalar(5);
        assert_eq!(idx * g.clone(), scal * g);
    }

    #[test]
    fn test_g2_index_mul() {
        let g = random_g2();
        let idx = TestValue::Index(5);
        let scal = scalar(5);
        assert_eq!(idx * g.clone(), scal * g);
    }

    // ========== Vector Operations Edge Cases ==========

    #[test]
    fn test_vec_scalar_mul_zero() {
        let v = vec_scalar(&[1, 2, 3, 4]);
        let zero = scalar(0);
        let result = v * zero;
        assert_eq!(result, vec_scalar(&[0, 0, 0, 0]));
    }

    #[test]
    fn test_vec_scalar_mul_one() {
        let v = vec_scalar(&[1, 2, 3, 4]);
        let one = scalar(1);
        let result = v.clone() * one;
        assert_eq!(result, v);
    }

    #[test]
    fn test_empty_vec_operations() {
        // Empty vectors should work correctly
        let empty_idx: TestValue = TestValue::VecIndex(vec![]);
        let empty_idx2: TestValue = TestValue::VecIndex(vec![]);
        assert_eq!(
            empty_idx.clone() + empty_idx2.clone(),
            TestValue::VecIndex(vec![])
        );
        assert_eq!(
            empty_idx.clone() - empty_idx2.clone(),
            TestValue::VecIndex(vec![])
        );
        assert_eq!(
            empty_idx.clone() * empty_idx2.clone(),
            TestValue::VecIndex(vec![])
        );
    }

    #[test]
    fn test_single_element_vec() {
        let a = TestValue::VecIndex(vec![5]);
        let b = TestValue::VecIndex(vec![3]);
        assert_eq!(a.clone() + b.clone(), TestValue::VecIndex(vec![8]));
        assert_eq!(a.clone() - b.clone(), TestValue::VecIndex(vec![2]));
        assert_eq!(a.clone() * b.clone(), TestValue::VecIndex(vec![15]));
    }

    // ========== Operations with Zero ==========

    #[test]
    fn test_scalar_add_zero() {
        let a = scalar(42);
        let zero = scalar(0);
        assert_eq!(a.clone() + zero.clone(), a.clone());
        assert_eq!(zero + a.clone(), a);
    }

    #[test]
    fn test_scalar_sub_zero() {
        let a = scalar(42);
        let zero = scalar(0);
        assert_eq!(a.clone() - zero, a);
    }

    #[test]
    fn test_zero_sub_scalar() {
        // 0 - a = -a
        let a = scalar(42);
        let zero = scalar(0);
        let neg_a = zero - a.clone();
        // Verify: a + (-a) = 0
        assert_eq!(a + neg_a, scalar(0));
    }

    #[test]
    fn test_vec_scalar_add_zero() {
        let v = vec_scalar(&[1, 2, 3]);
        let zero = vec_scalar(&[0, 0, 0]);
        assert_eq!(v.clone() + zero.clone(), v);
    }

    // ========== G1/G2 Subtraction Tests ==========

    #[test]
    fn test_g1_sub_self() {
        let a = random_g1();
        assert_eq!(a.clone() - a, TestValue::G1(G1Projective::zero()));
    }

    #[test]
    fn test_g2_sub_self() {
        let a = random_g2();
        assert_eq!(a.clone() - a, TestValue::G2(G2Projective::zero()));
    }

    #[test]
    fn test_g1_sub_distributivity() {
        // a * (G1 - G2) = a * G1 - a * G2
        let g1 = random_g1();
        let g2 = random_g1();
        let a = random_scalar();
        let lhs = a.clone() * (g1.clone() - g2.clone());
        let rhs = (a.clone() * g1) - (a * g2);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_g2_sub_distributivity() {
        let g1 = random_g2();
        let g2 = random_g2();
        let a = random_scalar();
        let lhs = a.clone() * (g1.clone() - g2.clone());
        let rhs = (a.clone() * g1) - (a * g2);
        assert_eq!(lhs, rhs);
    }

    // ========== VecG1/VecG2 Operations ==========

    #[test]
    fn test_vec_g1_add() {
        let a = random_g1();
        let b = random_g1();
        let va = TestValue::VecG1(vec![a.clone().into_g1(), b.clone().into_g1()]);
        let c = random_g1();
        let d = random_g1();
        let vb = TestValue::VecG1(vec![c.clone().into_g1(), d.clone().into_g1()]);

        let result = va + vb;
        let expected = TestValue::VecG1(vec![(a + c).into_g1(), (b + d).into_g1()]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_vec_g2_add() {
        let a = random_g2();
        let b = random_g2();
        let va = TestValue::VecG2(vec![a.clone().into_g2(), b.clone().into_g2()]);
        let c = random_g2();
        let d = random_g2();
        let vb = TestValue::VecG2(vec![c.clone().into_g2(), d.clone().into_g2()]);

        let result = va + vb;
        let expected = TestValue::VecG2(vec![(a + c).into_g2(), (b + d).into_g2()]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_vec_g1_sub() {
        let a = random_g1();
        let b = random_g1();
        let va = TestValue::VecG1(vec![a.clone().into_g1(), b.clone().into_g1()]);
        let vb = va.clone();

        let result = va - vb;
        let zero = G1Projective::zero();
        let expected = TestValue::VecG1(vec![zero, zero]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_vec_g2_sub() {
        let a = random_g2();
        let b = random_g2();
        let va = TestValue::VecG2(vec![a.clone().into_g2(), b.clone().into_g2()]);
        let vb = va.clone();

        let result = va - vb;
        let zero = G2Projective::zero();
        let expected = TestValue::VecG2(vec![zero, zero]);
        assert_eq!(result, expected);
    }

    // ========== Boolean Edge Cases ==========

    #[test]
    fn test_bool_and_associativity() {
        let a = TestValue::Bool(true);
        let b = TestValue::Bool(false);
        let c = TestValue::Bool(true);
        assert_eq!((a.clone() & b.clone()) & c.clone(), a & (b & c));
    }

    #[test]
    fn test_bool_or_associativity() {
        let a = TestValue::Bool(true);
        let b = TestValue::Bool(false);
        let c = TestValue::Bool(true);
        assert_eq!((a.clone() | b.clone()) | c.clone(), a | (b | c));
    }

    #[test]
    fn test_bool_and_annihilator() {
        // a & false = false
        let a = TestValue::Bool(true);
        let f = TestValue::Bool(false);
        assert_eq!(a & f, TestValue::Bool(false));
    }

    #[test]
    fn test_bool_or_annihilator() {
        // a | true = true
        let a = TestValue::Bool(false);
        let t = TestValue::Bool(true);
        assert_eq!(a | t, TestValue::Bool(true));
    }

    #[test]
    fn test_bool_and_idempotent() {
        // a & a = a
        let a = TestValue::Bool(true);
        assert_eq!(a.clone() & a.clone(), a);
        let b = TestValue::Bool(false);
        assert_eq!(b.clone() & b.clone(), b);
    }

    #[test]
    fn test_bool_or_idempotent() {
        // a | a = a
        let a = TestValue::Bool(true);
        assert_eq!(a.clone() | a.clone(), a);
        let b = TestValue::Bool(false);
        assert_eq!(b.clone() | b.clone(), b);
    }

    // ========== Additional Distributivity Tests ==========

    #[test]
    fn test_vec_scalar_distributivity_with_index() {
        let v = vec_scalar(&[1, 2, 3]);
        let a = TestValue::Index(2);
        let b = TestValue::Index(3);
        // (a + b) * v = a * v + b * v
        let lhs = (a.clone() + b.clone()) * v.clone();
        let rhs = (a * v.clone()) + (b * v);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_index_distributivity() {
        let a = TestValue::Index(2);
        let b = TestValue::Index(3);
        let c = TestValue::Index(5);
        // a * (b + c) = a * b + a * c
        assert_eq!(
            a.clone() * (b.clone() + c.clone()),
            (a.clone() * b) + (a * c)
        );
    }

    #[test]
    fn test_vec_index_distributivity() {
        let a = TestValue::VecIndex(vec![2, 3]);
        let b = TestValue::VecIndex(vec![4, 5]);
        let c = TestValue::VecIndex(vec![6, 7]);
        // a * (b + c) = a * b + a * c
        assert_eq!(
            a.clone() * (b.clone() + c.clone()),
            (a.clone() * b) + (a * c)
        );
    }

    // ========== Field Axiom Completeness ==========

    #[test]
    fn test_field_division_left_identity() {
        // 1 / a * a = 1 (when a ≠ 0)
        let a = scalar(7);
        let one = scalar(1);
        let result = (one.clone() / a.clone()) * a;
        assert_eq!(result, one);
    }

    #[test]
    fn test_field_division_right_identity() {
        // a / a = 1 (when a ≠ 0)
        let a = scalar(13);
        assert_eq!(a.clone() / a, scalar(1));
    }

    #[test]
    fn test_field_division_distributivity() {
        // (a + b) / c = a / c + b / c
        let a = scalar(10);
        let b = scalar(5);
        let c = scalar(3);
        let lhs = (a.clone() + b.clone()) / c.clone();
        let rhs = (a / c.clone()) + (b / c);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_scalar_div_associativity() {
        // a / (b / c) = (a * c) / b
        let a = scalar(24);
        let b = scalar(6);
        let c = scalar(2);
        let lhs = a.clone() / (b.clone() / c.clone());
        let rhs = (a * c) / b;
        assert_eq!(lhs, rhs);
    }

    // ========== Property-Based Tests for Polynomial Values ==========

    use arbitrary::{Arbitrary, Unstructured};

    /// Random univariate polynomial value (degree 1-4, non-zero coefficients)
    #[derive(Debug, Clone)]
    struct UniPoly(TestValue);

    impl<'a> Arbitrary<'a> for UniPoly {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let degree: usize = u.int_in_range(1..=4)?;
            let mut coeffs = Vec::new();
            for _ in 0..=degree {
                coeffs.push(Fr::from(u.int_in_range(1u64..=100)?));
            }
            Ok(UniPoly(TestValue::Poly(VirtualPolynomial::from_poly(
                PolyVariant::from_coeffs(coeffs),
            ))))
        }
    }

    /// Random MLE value with exactly 2 variables (4 evaluations)
    #[derive(Debug, Clone)]
    struct Mle2Poly(TestValue);

    impl<'a> Arbitrary<'a> for Mle2Poly {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let mut evals = Vec::new();
            for _ in 0..4 {
                evals.push(Fr::from(u.int_in_range(1u64..=100)?));
            }
            Ok(Mle2Poly(TestValue::Poly(VirtualPolynomial::from_poly(
                PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(2, evals)),
            ))))
        }
    }

    /// Non-zero scalar polynomial (for division tests)
    #[derive(Debug, Clone)]
    struct NonZeroScalarPoly(TestValue);

    impl<'a> Arbitrary<'a> for NonZeroScalarPoly {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let s = Fr::from(u.int_in_range(1u64..=100)?);
            Ok(NonZeroScalarPoly(TestValue::Poly(
                VirtualPolynomial::from_scalar(s),
            )))
        }
    }

    fn zero_poly() -> TestValue {
        TestValue::Poly(VirtualPolynomial::from_scalar(Fr::from(0)))
    }

    fn one_poly() -> TestValue {
        TestValue::Poly(VirtualPolynomial::from_scalar(Fr::from(1)))
    }

    // --- Cross-type interaction: VPoly + Uni → Poly ---

    #[test]
    fn pbt_vpoly_add_uni() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            let vpoly = a.0.clone() * b.0.clone();
            let c: UniPoly = u.arbitrary()?;
            let result = vpoly + c.0;
            assert!(matches!(result, TestValue::Poly(_)));
            Ok(())
        });
    }

    // --- Cross-type interaction: VPoly + Mle → Poly ---

    #[test]
    fn pbt_vpoly_add_mle() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            let vpoly = a.0.clone() * b.0.clone();
            let c: Mle2Poly = u.arbitrary()?;
            let result = vpoly + c.0;
            assert!(matches!(result, TestValue::Poly(_)));
            Ok(())
        });
    }

    // --- Cross-type interaction: Uni + Mle → Poly ---

    #[test]
    fn pbt_uni_add_mle() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            let result = a.0 + b.0;
            assert!(matches!(result, TestValue::Poly(_)));
            Ok(())
        });
    }

    // --- Univariate add: commutativity ---

    #[test]
    fn pbt_uni_add_commutativity() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: UniPoly = u.arbitrary()?;
            assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
            Ok(())
        });
    }

    // --- Univariate add: associativity ---

    #[test]
    fn pbt_uni_add_associativity() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: UniPoly = u.arbitrary()?;
            let c: UniPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
            Ok(())
        });
    }

    // --- Univariate add: identity (zero polynomial) ---

    #[test]
    fn pbt_uni_add_identity() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let z = zero_poly();
            assert_eq!(a.0.clone() + z.clone(), a.0.clone());
            assert_eq!(z + a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- Univariate add/sub inverse: a + b - b = a ---

    #[test]
    fn pbt_uni_add_sub_inverse() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: UniPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
            Ok(())
        });
    }

    // --- Univariate mul: commutativity ---

    #[test]
    fn pbt_uni_mul_commutativity() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: UniPoly = u.arbitrary()?;
            assert_eq!(a.0.clone() * b.0.clone(), b.0 * a.0);
            Ok(())
        });
    }

    // --- Univariate mul: associativity ---

    #[test]
    fn pbt_uni_mul_associativity() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: UniPoly = u.arbitrary()?;
            let c: UniPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() * b.0.clone()) * c.0.clone(), a.0 * (b.0 * c.0));
            Ok(())
        });
    }

    // --- Univariate mul: identity (one polynomial) ---

    #[test]
    fn pbt_uni_mul_identity() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let o = one_poly();
            assert_eq!(a.0.clone() * o.clone(), a.0.clone());
            assert_eq!(o * a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- Univariate mul/div inverse: (a * b) / b = a ---

    #[test]
    fn pbt_uni_mul_div_inverse() {
        arbtest::arbtest(|u| {
            let a: UniPoly = u.arbitrary()?;
            let b: NonZeroScalarPoly = u.arbitrary()?;
            let result = (a.0.clone() * b.0.clone()) / b.0;
            assert_eq!(result, a.0);
            Ok(())
        });
    }

    // --- MLE add: commutativity ---

    #[test]
    fn pbt_mle_add_commutativity() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
            Ok(())
        });
    }

    // --- MLE add: associativity ---

    #[test]
    fn pbt_mle_add_associativity() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            let c: Mle2Poly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
            Ok(())
        });
    }

    // --- MLE add: identity (zero polynomial) ---

    #[test]
    fn pbt_mle_add_identity() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let z = zero_poly();
            assert_eq!(a.0.clone() + z.clone(), a.0.clone());
            assert_eq!(z + a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- MLE add/sub inverse: a + b - b = a ---

    #[test]
    fn pbt_mle_add_sub_inverse() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
            Ok(())
        });
    }

    // --- MLE scalar mul/div inverse: (a * s) / s = a ---

    #[test]
    fn pbt_mle_scalar_mul_div_inverse() {
        arbtest::arbtest(|u| {
            let a: Mle2Poly = u.arbitrary()?;
            let s = Fr::from(u.int_in_range(1u64..=100)?);
            let sv = TestValue::Scalar(s);
            let result = (a.0.clone() * sv.clone()) / sv;
            assert_eq!(result, a.0);
            Ok(())
        });
    }

    // ========== VPoly (product polynomial) Property-Based Tests ==========

    /// Uni-based VPoly: product of two random univariates (degree 1-3 each)
    /// Normalizes to DenseUni, so PartialEq is exact.
    #[derive(Debug, Clone)]
    struct UniVPoly(TestValue);

    impl<'a> Arbitrary<'a> for UniVPoly {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let a: UniPoly = u.arbitrary()?;
            let b: UniPoly = u.arbitrary()?;
            Ok(UniVPoly(a.0 * b.0))
        }
    }

    /// MLE-based VPoly: product of two random 2-variable MLEs.
    /// Cannot normalize (MLE multiplication unsupported at PolyVariant level),
    /// uses canonical structural comparison via sorted products.
    #[derive(Debug, Clone)]
    struct MleVPoly(TestValue);

    impl<'a> Arbitrary<'a> for MleVPoly {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            let a: Mle2Poly = u.arbitrary()?;
            let b: Mle2Poly = u.arbitrary()?;
            Ok(MleVPoly(a.0 * b.0))
        }
    }

    // --- Uni VPoly add: commutativity ---

    #[test]
    fn pbt_uni_vpoly_add_commutativity() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let b: UniVPoly = u.arbitrary()?;
            assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
            Ok(())
        });
    }

    // --- Uni VPoly add: associativity ---

    #[test]
    fn pbt_uni_vpoly_add_associativity() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let b: UniVPoly = u.arbitrary()?;
            let c: UniVPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
            Ok(())
        });
    }

    // --- Uni VPoly add: identity (zero) ---

    #[test]
    fn pbt_uni_vpoly_add_identity() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let z = zero_poly();
            assert_eq!(a.0.clone() + z.clone(), a.0.clone());
            assert_eq!(z + a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- Uni VPoly add/sub inverse: a + b - b = a ---

    #[test]
    fn pbt_uni_vpoly_add_sub_inverse() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let b: UniVPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
            Ok(())
        });
    }

    // --- Uni VPoly mul: commutativity ---

    #[test]
    fn pbt_uni_vpoly_mul_commutativity() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let b: UniVPoly = u.arbitrary()?;
            assert_eq!(a.0.clone() * b.0.clone(), b.0 * a.0);
            Ok(())
        });
    }

    // --- Uni VPoly mul: associativity ---

    #[test]
    fn pbt_uni_vpoly_mul_associativity() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let b: UniVPoly = u.arbitrary()?;
            let c: UniVPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() * b.0.clone()) * c.0.clone(), a.0 * (b.0 * c.0));
            Ok(())
        });
    }

    // --- Uni VPoly mul: identity (one) ---

    #[test]
    fn pbt_uni_vpoly_mul_identity() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let o = one_poly();
            assert_eq!(a.0.clone() * o.clone(), a.0.clone());
            assert_eq!(o * a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- Uni VPoly scalar mul/div inverse: (a * s) / s = a ---

    #[test]
    fn pbt_uni_vpoly_scalar_mul_div_inverse() {
        arbtest::arbtest(|u| {
            let a: UniVPoly = u.arbitrary()?;
            let s: NonZeroScalarPoly = u.arbitrary()?;
            let result = (a.0.clone() * s.0.clone()) / s.0;
            assert_eq!(result, a.0);
            Ok(())
        });
    }

    // --- MLE VPoly add: commutativity ---

    #[test]
    fn pbt_mle_vpoly_add_commutativity() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let b: MleVPoly = u.arbitrary()?;
            assert_eq!(a.0.clone() + b.0.clone(), b.0 + a.0);
            Ok(())
        });
    }

    // --- MLE VPoly add: associativity ---

    #[test]
    fn pbt_mle_vpoly_add_associativity() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let b: MleVPoly = u.arbitrary()?;
            let c: MleVPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) + c.0.clone(), a.0 + (b.0 + c.0));
            Ok(())
        });
    }

    // --- MLE VPoly add: identity (zero) ---

    #[test]
    fn pbt_mle_vpoly_add_identity() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let z = zero_poly();
            assert_eq!(a.0.clone() + z.clone(), a.0.clone());
            assert_eq!(z + a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- MLE VPoly add/sub inverse: a + b - b = a ---

    #[test]
    fn pbt_mle_vpoly_add_sub_inverse() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let b: MleVPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() + b.0.clone()) - b.0, a.0);
            Ok(())
        });
    }

    // --- MLE VPoly mul: commutativity ---

    #[test]
    fn pbt_mle_vpoly_mul_commutativity() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let b: MleVPoly = u.arbitrary()?;
            assert_eq!(a.0.clone() * b.0.clone(), b.0 * a.0);
            Ok(())
        });
    }

    // --- MLE VPoly mul: associativity ---

    #[test]
    fn pbt_mle_vpoly_mul_associativity() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let b: MleVPoly = u.arbitrary()?;
            let c: MleVPoly = u.arbitrary()?;
            assert_eq!((a.0.clone() * b.0.clone()) * c.0.clone(), a.0 * (b.0 * c.0));
            Ok(())
        });
    }

    // --- MLE VPoly mul: identity (one) ---

    #[test]
    fn pbt_mle_vpoly_mul_identity() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let o = one_poly();
            assert_eq!(a.0.clone() * o.clone(), a.0.clone());
            assert_eq!(o * a.0.clone(), a.0);
            Ok(())
        });
    }

    // --- MLE VPoly scalar mul/div inverse: (a * s) / s = a ---

    #[test]
    fn pbt_mle_vpoly_scalar_mul_div_inverse() {
        arbtest::arbtest(|u| {
            let a: MleVPoly = u.arbitrary()?;
            let s = Fr::from(u.int_in_range(1u64..=100)?);
            let sv = TestValue::Scalar(s);
            let result = (a.0.clone() * sv.clone()) / sv;
            assert_eq!(result, a.0);
            Ok(())
        });
    }
}
