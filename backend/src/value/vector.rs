//! Vectors: indexing and slicing, concatenation, and building or splitting vector values.

use super::Value;
use crate::backends::keys::{Key, Keyed};
use crate::ir::types::Lub;
use crate::value::points::Points;
use crate::{ABase, ATyp, Backend, Field, Group};
use lang::typ::Nothing;
use rayon::prelude::*;
use std::sync::Arc;

impl<C: Backend> Value<C> {
    /// Owning form of [`Value::concat`]: returns the concatenation of `self` and
    /// `other`.
    ///
    /// # Panics
    /// Panics under the same conditions as [`Value::concat`].
    #[inline]
    pub fn value_concat(self, other: Self) -> Self {
        let mut other = other;
        self.concat(&mut other);
        other
    }

    /// Owning form of [`Value::ram_ref`]: indexes `self` by `r`.
    ///
    /// # Panics
    /// Panics under the same conditions as [`Value::ram_ref`].
    pub fn ram(self, r: Self) -> Self {
        self.ram_ref(&r)
    }

    /// Random-access read: gathers the entries of `self` named by the index value
    /// `r`.
    ///
    /// An `Index` selector returns a single element; a `VecIndex` selector returns a
    /// vector shaped like the selector, gathered in parallel. This is the runtime
    /// meaning of source-level `a[i]`.
    ///
    /// # Panics
    /// Panics if `self` is a record (record components are reached by field name,
    /// not by index), if the operand pair has no indexing rule, or if any index is
    /// out of bounds for `self`.
    pub fn ram_ref(&self, r: &Self) -> Self {
        // Field and group vectors select through `Shared::select`: a slice
        // `v[a..b]` (a contiguous index run) is a view of `v`'s buffer, any
        // other index list a copy.
        match (self, r) {
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                Value::VecIndex(b.par_iter().map(|i| a[*i]).collect())
            }
            (Value::VecIndex(a), Value::Index(b)) => Value::Index(a[*b]),
            (Value::VecScalar(a), Value::VecIndex(b)) => Value::VecScalar(a.select(b)),
            (Value::VecScalar(a), Value::Index(b)) => Value::Scalar(a[*b]),
            (Value::VecG1(a), Value::VecIndex(b)) => Value::VecG1(a.select(b)),
            (Value::VecG1(a), Value::Index(b)) => Value::g1(a[*b]),
            (Value::VecG2(a), Value::VecIndex(b)) => Value::VecG2(a.select(b)),
            (Value::VecG2(a), Value::Index(b)) => Value::g2(a[*b]),
            (Value::VecGT(a), Value::VecIndex(b)) => Value::VecGT(a.select(b)),
            (Value::VecGT(a), Value::Index(b)) => Value::GT(a[*b].into()),
            (Value::VecG1Affine(a), Value::VecIndex(b)) => Value::VecG1Affine(a.select(b)),
            (Value::VecG1Affine(a), Value::Index(b)) => Value::g1_affine(a[*b]),
            (Value::VecG2Affine(a), Value::VecIndex(b)) => Value::VecG2Affine(a.select(b)),
            (Value::VecG2Affine(a), Value::Index(b)) => Value::g2_affine(a[*b]),
            (Value::Vec(a), Value::VecIndex(b)) => {
                Value::Vec(b.par_iter().map(|i| a[*i].clone()).collect())
            }
            (Value::Vec(a), Value::Index(b)) => a[*b].clone(),
            (Value::Vec(a), Value::Vec(b)) => Value::Vec(
                b.par_iter()
                    .map(|i| a[i.clone().into_index()].clone())
                    .collect(),
            ),
            (Value::Record(_), _) => {
                panic!(
                    "Records do not support indexed access. Use direct field access (record.field) instead."
                )
            }
            (a, b) => panic!("Cannot do {}[{}]", a, b),
        }
    }

    #[inline]
    fn promote_to_vec(&mut self) {
        match self {
            Value::Scalar(s) => *self = Value::vec_scalar(vec![*s]),
            Value::Index(i) => *self = Value::VecIndex(vec![*i].into()),
            Value::G1(g) => *self = Value::vec_g1(vec![**g]),
            Value::G2(g) => *self = Value::vec_g2(vec![**g]),
            Value::GT(g) => *self = Value::vec_gt(vec![**g]),
            Value::G1Affine(g) => *self = Value::vec_g1_affine(vec![**g]),
            Value::G2Affine(g) => *self = Value::vec_g2_affine(vec![**g]),
            _ => {}
        }
    }

    /// Appends `r` onto `self`, storing the concatenation in `r`.
    ///
    /// Scalar-shaped operands are first promoted to one-element vectors, and a mixed
    /// index/scalar pair widens to `VecScalar`. Concatenating a flat homogeneous
    /// vector with a boxed `Value::Vec` re-flattens the boxed side so the result
    /// keeps the batched representation.
    ///
    /// # Panics
    /// Panics if `self` is a polynomial, record, unit or bool (no concatenation
    /// rule), or if `r` cannot be re-shaped to match `self`.
    pub fn concat(self, r: &mut Self) {
        if let Value::VecG2Affine(b) = &r
            && let Some(right) = b.key()
        {
            // A right side with a key keeps what of it follows the concatenation; the
            // left side brings its own key or the backend's for its points.
            let left_points = match &self {
                Value::VecG2Affine(a) => a.to_vec(),
                Value::G2(a) => vec![a.normalize()],
                Value::G2Affine(a) => vec![**a],
                Value::VecG2(a) => C::G2::normalize_batch(a),
                _ => panic!("Cannot concat {} with a G2 vector", self),
            };
            let left_keyed = match &self {
                Value::VecG2Affine(a) => a.key(),
                _ => None,
            };
            let prepared = match left_keyed {
                Some(_) => None,
                None => <C::G2Key as Key<_>>::prepare(&left_points),
            };
            let left =
                left_keyed.or_else(|| prepared.as_ref().map(|key| Keyed { key, view: None }));
            let key = left.and_then(|left| left.key.concat(left.view, right.key, right.view));
            let mut points = left_points;
            points.extend_from_slice(b);
            *r = Value::VecG2Affine(Points::keyed(points, |_| key));
            return;
        }
        // A vector left side is moved out: no copy when this is its only owner.
        match self {
            Value::VecScalar(a) => {
                r.promote_to_vec();
                let mut a = a.into_vec();
                a.append(r.into_vec_scalar_mut());
                *r = Value::vec_scalar(a);
            }
            Value::VecG1(a) => {
                r.promote_to_vec();
                let mut a = a.into_vec();
                a.append(r.into_vec_g1_mut());
                *r = Value::vec_g1(a);
            }
            Value::VecG2(a) => {
                r.promote_to_vec();
                let mut a = a.into_vec();
                a.append(r.into_vec_g2_mut());
                *r = Value::vec_g2(a);
            }
            Value::VecGT(a) => {
                r.promote_to_vec();
                let mut a = a.into_vec();
                a.append(r.into_vec_gt_mut());
                *r = Value::vec_gt(a);
            }
            Value::VecG1Affine(a) => {
                r.promote_to_vec();
                let mut a = a.into_vec();
                a.append(r.into_vec_g1_affine_mut());
                *r = Value::vec_g1_affine(a);
            }
            Value::VecG2Affine(a) => {
                r.promote_to_vec();
                let mut a = a.into_vec();
                a.append(r.into_vec_g2_affine_mut());
                *r = Value::vec_g2_affine(a);
            }
            Value::VecIndex(a) => match &r {
                Value::VecIndex(vs) => {
                    let mut v = Vec::with_capacity(a.len() + vs.len());
                    a.iter().for_each(|a| v.push(*a));
                    vs.iter().for_each(|b| v.push(*b));
                    *r = Value::VecIndex(v.into());
                }
                Value::Index(b) => {
                    *r = Value::VecIndex(a.iter().copied().chain(std::iter::once(*b)).collect())
                }
                Value::Vec(v) => {
                    let mut x = Vec::with_capacity(a.len() + v.len());
                    a.iter().for_each(|a| x.push(Value::Index(*a)));
                    x.extend(v.iter().cloned());
                    *r = Value::Vec(x.into())
                }
                Value::Scalar(b) => {
                    *r = Value::vec_scalar(
                        a.iter()
                            .map(|a| C::F::from_usize(*a))
                            .chain(std::iter::once(*b))
                            .collect(),
                    )
                }
                Value::VecScalar(b) => {
                    let mut x = Vec::with_capacity(a.len() + b.len());
                    a.iter().for_each(|a| x.push(C::F::from_usize(*a)));
                    x.extend(b);
                    *r = Value::vec_scalar(x)
                }
                _ => panic!("Expected vec index, found {}", r),
            },
            Value::Scalar(a) => {
                r.promote_to_vec();
                let mut a = vec![a];
                a.append(r.into_vec_scalar_mut());
                *r = Value::vec_scalar(a);
            }
            Value::G1(a) => {
                r.promote_to_vec();
                let mut a = vec![*a];
                a.append(r.into_vec_g1_mut());
                *r = Value::vec_g1(a);
            }
            Value::G2(a) => {
                r.promote_to_vec();
                let mut a = vec![*a];
                a.append(r.into_vec_g2_mut());
                *r = Value::vec_g2(a);
            }
            Value::GT(a) => {
                r.promote_to_vec();
                let mut a = vec![*a];
                a.append(r.into_vec_gt_mut());
                *r = Value::vec_gt(a);
            }
            Value::G1Affine(a) => {
                r.promote_to_vec();
                let mut a = vec![*a];
                a.append(r.into_vec_g1_affine_mut());
                *r = Value::vec_g1_affine(a);
            }
            Value::G2Affine(a) => {
                r.promote_to_vec();
                let mut a = vec![*a];
                a.append(r.into_vec_g2_affine_mut());
                *r = Value::vec_g2_affine(a);
            }
            Value::Index(a) => {
                r.promote_to_vec();
                let mut a = vec![a];
                a.append(r.into_vec_index_mut());
                *r = Value::VecIndex(a.into());
            }
            Value::Vec(a) => match &r {
                Value::Vec(_) => {
                    let mut a = a;
                    a.to_mut().append(r.into_vec_mut());
                    *r = Value::Vec(a);
                }
                Value::VecScalar(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_scalar_mut().append(r.into_vec_scalar_mut());
                    *r = slf;
                }
                Value::VecG1(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_g1_mut().append(r.into_vec_g1_mut());
                    *r = slf;
                }
                Value::VecG2(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_g2_mut().append(r.into_vec_g2_mut());
                    *r = slf;
                }
                Value::VecGT(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_gt_mut().append(r.into_vec_gt_mut());
                    *r = slf;
                }
                Value::VecG1Affine(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_g1_affine_mut()
                        .append(r.into_vec_g1_affine_mut());
                    *r = slf;
                }
                Value::VecG2Affine(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_g2_affine_mut()
                        .append(r.into_vec_g2_affine_mut());
                    *r = slf;
                }
                Value::VecIndex(_) => {
                    let mut slf = Value::Vec(a);
                    slf.into_vec_index_mut().append(r.into_vec_index_mut());
                    *r = slf;
                }
                _ => {
                    let mut a = a;
                    a.to_mut().push(r.clone());
                    *r = Value::Vec(a);
                }
            },
            _ => panic!("Not implemented"),
        }
    }

    /// Builds a vector value from element values, collapsing to the flat
    /// homogeneous representation whenever the elements share a base type.
    ///
    /// The element type is derived by folding `ATyp::lub_equ` over the elements, so
    /// this both checks homogeneity and picks the carrier. Element types with no
    /// flat carrier (polynomials, records, nested vectors, unit, bool) stay as a
    /// boxed `Value::Vec`.
    ///
    /// # Panics
    /// Panics if `vec` is empty, if the element types have no least upper bound, or
    /// if an element does not match the derived carrier.
    pub fn value_vec(vec: Vec<Self>) -> Self {
        // Only the kind of the element type matters here (it picks the
        // Vec variant; every polynomial kind keeps `Value::Vec`).
        let mut typ = vec[0].shape_typ();
        for i in vec.iter().skip(1) {
            typ = ATyp::lub_equ(&i.shape_typ(), &typ, &Nothing).unwrap();
        }
        let mut vec_value = Value::Vec(vec.into());
        match typ {
            ATyp::Base(ABase::Scalar) => {
                vec_value.into_vec_scalar_mut();
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
            ATyp::Base(ABase::Unit)
            | ATyp::Base(ABase::Bool)
            | ATyp::Uni(_)
            | ATyp::Mle(_)
            | ATyp::VPoly(_, _)
            | ATyp::Record(_)
            | ATyp::Vec(_, _) => vec_value,
        }
    }

    /// Convert a vector Value into a Vec of element Values.
    pub fn into_elements(self) -> Vec<Value<C>> {
        match self {
            Value::VecScalar(v) => v.into_vec().into_iter().map(Value::Scalar).collect(),
            Value::VecIndex(v) => v.iter().map(|&i| Value::Index(i)).collect(),
            Value::VecG1(v) => v.into_vec().into_iter().map(Value::g1).collect(),
            Value::VecG2(v) => v
                .into_vec()
                .into_iter()
                .map(|g| Value::G2(Arc::new(g)))
                .collect(),
            Value::VecGT(v) => v
                .into_vec()
                .into_iter()
                .map(|g| Value::GT(Arc::new(g)))
                .collect(),
            Value::VecG1Affine(v) => v.into_vec().into_iter().map(Value::g1_affine).collect(),
            Value::VecG2Affine(v) => v
                .into_vec()
                .into_iter()
                .map(|g| Value::G2Affine(Arc::new(g)))
                .collect(),
            Value::Vec(v) => v.into_vec(),
            _ => panic!("Expected vector, found {}", self),
        }
    }
}
