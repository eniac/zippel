//! Typed access to a value: `into_*` views and casts between representations, and
//! predicates.

use super::Value;
use crate::poly::virtual_polynomial::VirtualPolynomial;
use crate::{Backend, Field, G1Affine, G2Affine, GT, Group};
use rayon::prelude::*;
use std::sync::Arc;

impl<C: Backend> Value<C> {
    /// Dynamic casts
    #[inline]
    pub fn into_scalar(&self) -> C::F {
        match self {
            Value::Scalar(f) => *f,
            Value::Index(i) => C::F::from_usize(*i),
            _ => panic!("Expected scalar, found {}", self),
        }
    }

    /// Borrows the virtual polynomial inside a `Value::Poly`.
    ///
    /// # Panics
    /// Panics if this value is not a polynomial.
    #[inline]
    pub fn into_poly(&self) -> &VirtualPolynomial<C::F> {
        match self {
            Value::Poly(p) => p,
            _ => panic!("Expected poly, found {}", self),
        }
    }

    /// Returns a mutable scalar view, converting an `Index` in place first.
    ///
    /// # Panics
    /// Panics if this value is neither a scalar nor an index.
    #[inline]
    pub fn into_scalar_mut(&mut self) -> &mut C::F {
        match self {
            Value::Scalar(f) => f,
            Value::Index(i) => {
                *self = Value::Scalar(C::F::from_usize(*i));
                self.into_scalar_mut()
            }
            _ => panic!("Expected mut scalar, found {}", self),
        }
    }

    /// Returns a mutable projective first-source-group view, converting an affine
    /// point in place first.
    ///
    /// # Panics
    /// Panics if this value is not a first-source-group point.
    #[inline]
    pub fn into_g1_mut(&mut self) -> &mut C::G1 {
        match self {
            Value::G1(g) => Arc::make_mut(g),
            Value::G1Affine(g) => {
                *self = Value::g1((**g).into());
                self.into_g1_mut()
            }
            _ => panic!("Expected mut group1, found {}", self),
        }
    }

    /// Returns a mutable projective second-source-group view, converting an affine
    /// point in place first.
    ///
    /// # Panics
    /// Panics if this value is not a second-source-group point.
    #[inline]
    pub fn into_g2_mut(&mut self) -> &mut C::G2 {
        match self {
            Value::G2(g) => Arc::make_mut(g),
            Value::G2Affine(g) => {
                *self = Value::g2((**g).into());
                self.into_g2_mut()
            }
            _ => panic!("Expected mut group2, found {}", self),
        }
    }

    /// Returns a mutable view of a pairing target group element.
    ///
    /// # Panics
    /// Panics if this value is not a target group element.
    #[inline]
    pub fn into_gt_mut(&mut self) -> &mut GT<C> {
        match self {
            Value::GT(g) => Arc::make_mut(g),
            _ => panic!("Expected mut groupt, found {}", self),
        }
    }

    /// Returns a mutable affine first-source-group view, normalizing a projective
    /// point in place first.
    ///
    /// # Panics
    /// Panics if this value is not a first-source-group point.
    #[inline]
    pub fn into_g1_affine_mut(&mut self) -> &mut G1Affine<C> {
        match self {
            Value::G1(g) => {
                *self = Value::g1_affine(g.normalize());
                self.into_g1_affine_mut()
            }
            Value::G1Affine(g) => Arc::make_mut(g),
            _ => panic!("Expected mut group1, found {}", self),
        }
    }

    /// Returns a mutable affine second-source-group view, normalizing a projective
    /// point in place first.
    ///
    /// # Panics
    /// Panics if this value is not a second-source-group point.
    #[inline]
    pub fn into_g2_affine_mut(&mut self) -> &mut G2Affine<C> {
        match self {
            Value::G2(g) => {
                *self = Value::g2_affine(g.normalize());
                self.into_g2_affine_mut()
            }
            Value::G2Affine(g) => Arc::make_mut(g),
            _ => panic!("Expected mut group2, found {}", self),
        }
    }

    /// Returns a mutable scalar-vector view, converting a `VecIndex` or a boxed
    /// `Value::Vec` of scalars in place first.
    ///
    /// # Panics
    /// Panics if this value cannot be re-shaped to a scalar vector, including when a
    /// boxed element is not scalar-like.
    #[inline]
    pub fn into_vec_scalar_mut(&mut self) -> &mut Vec<C::F> {
        match self {
            Value::VecScalar(v) => v.to_mut(),
            Value::VecIndex(v) => {
                *self = Value::vec_scalar(v.par_iter().map(|i| C::F::from_usize(*i)).collect());
                self.into_vec_scalar_mut()
            }
            Value::Vec(v) => {
                *self = Value::vec_scalar(v.par_iter().map(|v| v.into_scalar()).collect());
                self.into_vec_scalar_mut()
            }
            _ => panic!("Expected mut vec scalar, found {}", self),
        }
    }

    /// Returns a mutable boxed-element view, un-flattening any homogeneous flat
    /// vector variant in place first.
    ///
    /// This runs opposite to the other `into_vec_*_mut` casts and costs one
    /// allocation per element, so it is reserved for the generic element-wise
    /// fallback arms.
    ///
    /// # Panics
    /// Panics if this value is not a vector.
    #[inline]
    pub fn into_vec_mut(&mut self) -> &mut Vec<Self> {
        match self {
            Value::Vec(v) => v.to_mut(),
            Value::VecIndex(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::Index(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG1(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::g1(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG2(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::g2(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecGT(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::gt(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG1Affine(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::g1_affine(*i)).collect());
                self.into_vec_mut()
            }
            Value::VecG2Affine(v) => {
                *self = Value::Vec(v.par_iter().map(|i| Value::g2_affine(*i)).collect());
                self.into_vec_mut()
            }
            _ => panic!("Expected mut vec, found {}", self),
        }
    }

    /// Returns a mutable projective first-source-group vector view, converting
    /// affine or boxed representations in place first.
    ///
    /// # Panics
    /// Panics if this value is not such a vector, or if a boxed element is not a
    /// first-source-group point.
    pub fn into_vec_g1_mut(&mut self) -> &mut Vec<C::G1> {
        match self {
            Value::VecG1(v) => v.to_mut(),
            Value::VecG1Affine(v) => {
                *self = Value::vec_g1(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g1_mut()
            }
            Value::Vec(v) => {
                *self = Value::vec_g1(
                    v.iter()
                        .map(|val| match val {
                            Value::G1(g) => **g,
                            Value::G1Affine(g) => (**g).into(),
                            _ => panic!("Expected G1 element in vec, found {}", val),
                        })
                        .collect(),
                );
                self.into_vec_g1_mut()
            }
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }

    /// Returns a mutable projective second-source-group vector view, converting
    /// affine or boxed representations in place first.
    ///
    /// # Panics
    /// Panics if this value is not such a vector, or if a boxed element is not a
    /// second-source-group point.
    pub fn into_vec_g2_mut(&mut self) -> &mut Vec<C::G2> {
        match self {
            Value::VecG2(v) => v.to_mut(),
            Value::VecG2Affine(v) => {
                *self = Value::vec_g2(v.par_iter().map(|i| (*i).into()).collect());
                self.into_vec_g2_mut()
            }
            Value::Vec(v) => {
                *self = Value::vec_g2(
                    v.iter()
                        .map(|val| match val {
                            Value::G2(g) => **g,
                            Value::G2Affine(g) => (**g).into(),
                            _ => panic!("Expected G2 element in vec, found {}", val),
                        })
                        .collect(),
                );
                self.into_vec_g2_mut()
            }
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }

    /// Returns a mutable target-group vector view, flattening a boxed `Value::Vec`
    /// in place first.
    ///
    /// # Panics
    /// Panics if this value is not such a vector, or if a boxed element is not a
    /// target group element.
    pub fn into_vec_gt_mut(&mut self) -> &mut Vec<GT<C>> {
        match self {
            Value::VecGT(v) => v.to_mut(),
            Value::Vec(v) => {
                *self = Value::vec_gt(
                    v.iter()
                        .map(|val| match val {
                            Value::GT(g) => **g,
                            _ => panic!("Expected GT element in vec, found {}", val),
                        })
                        .collect(),
                );
                self.into_vec_gt_mut()
            }
            _ => panic!("Expected mut vec groupt, found {}", self),
        }
    }

    /// Returns a mutable affine first-source-group vector view, batch-normalizing a
    /// projective vector in place first.
    ///
    /// # Panics
    /// Panics if this value is not a first-source-group vector.
    pub fn into_vec_g1_affine_mut(&mut self) -> &mut Vec<G1Affine<C>> {
        match self {
            Value::VecG1Affine(v) => v.to_mut(),
            Value::VecG1(v) => {
                *self = Value::vec_g1_affine(C::G1::normalize_batch(v));
                self.into_vec_g1_affine_mut()
            }
            _ => panic!("Expected mut vec group1, found {}", self),
        }
    }

    /// Returns a mutable affine second-source-group vector view, batch-normalizing a
    /// projective vector in place first.
    ///
    /// # Panics
    /// Panics if this value is not a second-source-group vector.
    pub fn into_vec_g2_affine_mut(&mut self) -> &mut Vec<G2Affine<C>> {
        match self {
            Value::VecG2Affine(v) => v.to_mut(),
            Value::VecG2(v) => {
                *self = Value::vec_g2_affine(C::G2::normalize_batch(v));
                self.into_vec_g2_affine_mut()
            }
            _ => panic!("Expected mut vec group2, found {}", self),
        }
    }

    /// Returns a mutable view of the index vector backing a range value.
    ///
    /// A range is materialized as its enumerated indices, so this is the same
    /// representation as [`Value::into_vec_index_mut`].
    ///
    /// # Panics
    /// Panics if this value is not a `VecIndex`.
    pub fn into_range_mut(&mut self) -> &mut Vec<usize> {
        match self {
            Value::VecIndex(r) => r.to_mut(),
            _ => panic!("Expected mut range, found {}", self),
        }
    }

    /// Returns a mutable index-vector view.
    ///
    /// Unlike the scalar and group casts this performs no conversion: indices are
    /// never recovered from field elements.
    ///
    /// # Panics
    /// Panics if this value is not a `VecIndex`.
    pub fn into_vec_index_mut(&mut self) -> &mut Vec<usize> {
        match self {
            Value::VecIndex(v) => v.to_mut(),
            _ => panic!("Expected mut vec index, found {}", self),
        }
    }

    /// Borrows the index vector of a `VecIndex`.
    ///
    /// # Panics
    /// Panics if this value is not a `VecIndex`.
    pub fn into_vec_index(&self) -> &[usize] {
        match self {
            Value::VecIndex(v) => v,
            _ => panic!("Expected vec index, found {}", self),
        }
    }

    /// Reads the machine index out of an `Index`.
    ///
    /// # Panics
    /// Panics if this value is not an `Index`.
    pub fn into_index(&self) -> usize {
        match self {
            Value::Index(i) => *i,
            _ => panic!("Expected index, found {}", self),
        }
    }

    /// Returns a mutable view of the machine index inside an `Index`.
    ///
    /// # Panics
    /// Panics if this value is not an `Index`.
    pub fn into_index_mut(&mut self) -> &mut usize {
        match self {
            Value::Index(i) => i,
            _ => panic!("Expected mut index, found {}", self),
        }
    }

    /// Reports whether this value has vector shape, in either the boxed or any of
    /// the flat homogeneous representations.
    pub fn is_vec(&self) -> bool {
        matches!(
            self,
            Value::Vec(_)
                | Value::VecScalar(_)
                | Value::VecG1(_)
                | Value::VecG2(_)
                | Value::VecGT(_)
                | Value::VecG1Affine(_)
                | Value::VecG2Affine(_)
                | Value::VecIndex(_)
        )
    }

    /// Reports whether this value is the additive identity of its type.
    ///
    /// Vectors and records are zero only if every component is, `Unit` is vacuously
    /// zero, and `Bool` is zero when false, matching the 0/1 encoding used when
    /// booleans feed arithmetic.
    pub fn is_zero(&self) -> bool {
        match self {
            Value::Scalar(a) => a.is_zero(),
            Value::Index(a) => *a == 0,
            Value::G1(a) => a.is_zero(),
            Value::G2(a) => a.is_zero(),
            Value::GT(a) => a.is_zero(),
            Value::G1Affine(a) => Into::<C::G1>::into(**a).is_zero(),
            Value::G2Affine(a) => Into::<C::G2>::into(**a).is_zero(),
            Value::VecScalar(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG1(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG2(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecGT(a) => a.par_iter().all(|a| a.is_zero()),
            Value::VecG1Affine(a) => a.par_iter().all(|a| Into::<C::G1>::into(*a).is_zero()),
            Value::VecG2Affine(a) => a.par_iter().all(|a| Into::<C::G2>::into(*a).is_zero()),
            Value::VecIndex(a) => a.par_iter().all(|a| *a == 0),
            Value::Vec(a) => a.par_iter().all(|a| a.is_zero()),
            Value::Record(fields) => fields.iter().all(|(_, v)| v.is_zero()),
            Value::Poly(poly) => poly.is_zero(),
            Value::Unit => true,
            Value::Bool(b) => !b,
        }
    }
}
