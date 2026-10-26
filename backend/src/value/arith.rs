//! Arithmetic on values: `+`, `-`, `*`, `/`, `%`, powers, reductions, and the
//! operator traits.

use super::Value;
use crate::algebra::batch_inverse;
use crate::poly::variant::PolyError;
use crate::poly::virtual_polynomial::VirtualPolynomial;
use crate::{Backend, DivisionByZero, Field, Group, Pairing};
use lang::ast::BinOp;
use rayon::prelude::*;
use std::ops::{Add, AddAssign, BitXor, Mul, MulAssign, Sub};
use std::sync::Arc;

/// Whether `i` is one of the values `range` steps through.
/// `a / b` on indices.
fn index_div(a: usize, b: usize) -> Result<usize, DivisionByZero> {
    a.checked_div(b).ok_or(DivisionByZero)
}

/// `a % b` on indices.
fn index_rem(a: usize, b: usize) -> Result<usize, DivisionByZero> {
    a.checked_rem(b).ok_or(DivisionByZero)
}

/// `f⁻¹`.
fn scalar_inverse<F: Field>(f: &F) -> Result<F, DivisionByZero> {
    f.inverse().ok_or(DivisionByZero)
}

/// The quotient of a polynomial division. A zero divisor is a
/// [`DivisionByZero`]; any other failure is an operand the type checker
/// rules out.
fn poly_quotient<T, F: Field>(quotient: Result<T, PolyError<F>>) -> Result<T, DivisionByZero> {
    match quotient {
        Ok(q) => Ok(q),
        Err(PolyError::DivisionByZero { .. }) => Err(DivisionByZero),
        Err(e) => panic!("Polynomial division failed: {e}"),
    }
}

fn reduce_univariate_poly_sum<C: Backend>(
    elements: &[Value<C>],
) -> Option<VirtualPolynomial<C::F>> {
    let polys = elements
        .iter()
        .map(|element| match element {
            Value::Poly(poly) => Some(&**poly),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    VirtualPolynomial::sum_univariate_products_dense(&polys)
}

/// `b := a / b`.
///
/// # Errors
/// [`DivisionByZero`] if `b` is zero; `b` is then unchanged.
fn div<F: Field>(a: &F, b: &mut F) -> Result<(), DivisionByZero> {
    *b = *a * b.inverse().ok_or(DivisionByZero)?;
    Ok(())
}

impl<C: Backend> AddAssign for Value<C> {
    fn add_assign(&mut self, other: Self) {
        other.value_add(self);
    }
}

impl<C: Backend> MulAssign for Value<C> {
    fn mul_assign(&mut self, other: Self) {
        other.value_mul(self);
    }
}

impl<C: Backend> Add for Value<C> {
    type Output = Value<C>;

    fn add(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_add(&mut other);
        other
    }
}

impl<C: Backend> Sub for Value<C> {
    type Output = Value<C>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_sub(&mut other);
        other
    }
}

impl<C: Backend> Mul for Value<C> {
    type Output = Value<C>;

    fn mul(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_mul(&mut other);
        other
    }
}

impl<C: Backend> BitXor for Value<C> {
    type Output = Value<C>;

    fn bitxor(self, other: Self) -> Self::Output {
        let mut other = other;
        self.value_pow(&mut other);
        other
    }
}

impl<C: Backend> Add for &Value<C> {
    type Output = Value<C>;

    fn add(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_add(&mut other);
        other
    }
}

impl<C: Backend> Sub for &Value<C> {
    type Output = Value<C>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_sub(&mut other);
        other
    }
}

impl<C: Backend> Mul for &Value<C> {
    type Output = Value<C>;

    fn mul(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_mul(&mut other);
        other
    }
}

impl<C: Backend> BitXor for &Value<C> {
    type Output = Value<C>;
    fn bitxor(self, other: Self) -> Self::Output {
        let mut other = other.clone();
        self.value_pow(&mut other);
        other
    }
}

impl<C: Backend> Value<C> {
    /// Value addition, saves result in other
    #[inline]
    pub fn value_add(&self, other: &mut Self) {
        match self {
            // Indexes coerce to scalars (addition)
            Value::Index(a) => match &other {
                Value::Index(_) => *other.into_index_mut() += *a,
                Value::Scalar(_) => *other.into_scalar_mut() += C::F::from_usize(*a),
                Value::Poly(poly) => {
                    *other = Value::poly(poly.poly_add_scalar(C::F::from_usize(*a)));
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                Value::Index(b) => {
                    *other = Value::Scalar(C::F::from_usize(*b));
                    *other.into_scalar_mut() += *a;
                }
                Value::Scalar(_) => *other.into_scalar_mut() += *a,
                Value::Poly(poly) => {
                    *other = Value::poly(poly.poly_add_scalar(*a));
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            // Group addition
            Value::G1Affine(a) => other.into_g1_mut().add_affine(a),
            Value::G2Affine(a) => other.into_g2_mut().add_affine(a),
            Value::G1(a) => other.into_g1_mut().add_affine(&(*a).normalize()),
            Value::G2(a) => other.into_g2_mut().add_affine(&(*a).normalize()),
            Value::GT(a) => other.into_gt_mut().add_affine(a),
            // Polynomial addition
            Value::Poly(a) => match &other {
                Value::Poly(b) => {
                    *other = Value::poly(a.poly_add(b));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::poly(a.poly_add_scalar(other.into_scalar()));
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
                    .for_each(|(a, b)| *b += C::F::from_usize(*a)),
                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecScalar(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b += *a),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b += *a),
                _ => panic!("Expected vec scalar, found {}", other),
            },
            Value::VecG1Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| b.add_affine(a)),
            Value::VecG2Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| b.add_affine(a)),
            Value::VecG1(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| b.add_affine(&(*a).normalize())),
            Value::VecG2(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| b.add_affine(&(*a).normalize())),
            Value::VecGT(vs) => vs
                .par_iter()
                .zip(other.into_vec_gt_mut().par_iter_mut())
                .for_each(|(a, b)| b.add_affine(a)),
            Value::Vec(vs) => vs
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_add(b)),
            Value::Record(_) => {
                panic!("Cannot add records")
            }
            Value::Unit => panic!("Cannot add Unit"),
            Value::Bool(_) => panic!("Cannot add Bool"),
        }
    }

    /// Subtracts `other` from `self`, storing `self - other` back into `other`.
    ///
    /// As with [`Value::value_add`] the destination operand re-shapes itself as
    /// needed (`Index` promotes to `Scalar`, affine points promote to projective),
    /// and a mixed scalar/polynomial pair lifts the scalar to a constant polynomial.
    /// Vector arms subtract element-wise in parallel.
    ///
    /// # Panics
    /// Panics when the operand pair has no subtraction rule: `Record`, `Unit` and
    /// `Bool` receivers, a mismatched variant pair, or a polynomial subtraction that
    /// reports incompatible arities. These are IR invariant violations; user-facing
    /// checks happen during `lang` type inference.
    #[inline]
    pub fn value_sub(&self, other: &mut Self) {
        match self {
            // Indexes coerce to scalars (addition)
            Value::Index(a) => match &other {
                Value::Index(b) => *other.into_index_mut() = *a - *b,
                Value::Scalar(_) => {
                    *other.into_scalar_mut() = C::F::from_usize(*a) - *other.into_scalar_mut()
                }
                Value::Poly(poly) => {
                    *other = Value::poly(VirtualPolynomial::scalar_sub_poly(
                        C::F::from_usize(*a),
                        poly,
                    ));
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                Value::Index(b) => {
                    *other = Value::Scalar(C::F::from_usize(*b));
                    *other.into_scalar_mut() = *a - *other.into_scalar_mut();
                }
                Value::Scalar(_) => *other.into_scalar_mut() = *a - *other.into_scalar_mut(),
                Value::Poly(poly) => {
                    *other = Value::poly(VirtualPolynomial::scalar_sub_poly(*a, poly));
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            // Group addition
            Value::G1Affine(a) => {
                let y = other.into_g1_mut();
                *y = -*y;
                y.add_affine(a)
            }
            Value::G2Affine(a) => {
                let y = other.into_g2_mut();
                *y = -*y;
                y.add_affine(a)
            }
            Value::G1(a) => {
                let y = other.into_g1_mut();
                *y = -*y;
                y.add_affine(&(*a).normalize())
            }
            Value::G2(a) => {
                let y = other.into_g2_mut();
                *y = -*y;
                y.add_affine(&(*a).normalize())
            }
            Value::GT(a) => {
                let y = other.into_gt_mut();
                *y = -*y;
                y.add_affine(a)
            }
            // The same but for vectors (scalars)
            Value::VecIndex(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_index_mut().par_iter_mut())
                    .for_each(|(a, b)| *b = *a - *b),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b = C::F::from_usize(*a) - *b),
                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecScalar(vs) => match &other {
                Value::VecIndex(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b = *a - *b),
                Value::VecScalar(_) => vs
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b = *a - *b),
                _ => panic!("Expected vec scalar, found {}", other),
            },
            Value::VecG1Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| {
                    let y = b;
                    *y = -*y;
                    y.add_affine(a)
                }),
            Value::VecG2Affine(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| {
                    let y = b;
                    *y = -*y;
                    y.add_affine(a)
                }),
            Value::VecG1(vs) => vs
                .par_iter()
                .zip(other.into_vec_g1_mut().par_iter_mut())
                .for_each(|(a, b)| {
                    let y = b;
                    *y = -*y;
                    y.add_affine(&(*a).normalize())
                }),
            Value::VecG2(vs) => vs
                .par_iter()
                .zip(other.into_vec_g2_mut().par_iter_mut())
                .for_each(|(a, b)| {
                    let y = b;
                    *y = -*y;
                    y.add_affine(&(*a).normalize())
                }),
            Value::VecGT(vs) => vs
                .par_iter()
                .zip(other.into_vec_gt_mut().par_iter_mut())
                .for_each(|(a, b)| {
                    let y = b;
                    *y = -*y;
                    y.add_affine(a)
                }),
            Value::Vec(vs) => vs
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_sub(b)),
            Value::Poly(a) => match &other {
                Value::Poly(b) => {
                    *other = Value::poly(a.poly_sub(b));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::poly(a.poly_sub_scalar(other.into_scalar()));
                }
                _ => panic!("Expected polynomial or scalar, found {}", other),
            },
            Value::Record(_) => {
                panic!("Cannot subtract records")
            }
            Value::Unit => panic!("Cannot subtract Unit"),
            Value::Bool(_) => panic!("Cannot subtract Bool"),
        }
    }

    /// Value multiplication, saves result in other
    #[inline]
    pub fn value_mul(&self, other: &mut Self) {
        match self {
            Value::Poly(a) => match &other {
                Value::Poly(b) => {
                    *other = Value::poly(a.poly_mul(b));
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::poly(a.poly_mul_scalar(other.into_scalar()));
                }
                _ => panic!("Expected polynomial or scalar, found {}", other),
            },
            Value::Index(a) => match &other {
                // Index * Index = Index
                Value::Index(_) => {
                    *other.into_index_mut() *= *a;
                }
                // Index * whatever, cast index to scalar
                Value::Scalar(_) => *other.into_scalar_mut() *= C::F::from_usize(*a),
                // Index * groups
                Value::G1(_) | Value::G1Affine(_) => {
                    let group = other.into_g1_mut();
                    *group *= C::F::from_usize(*a);
                }
                Value::G2(_) | Value::G2Affine(_) => {
                    let group = other.into_g2_mut();
                    *group *= C::F::from_usize(*a);
                }
                Value::GT(_) => {
                    let group = other.into_gt_mut();
                    *group *= C::F::from_usize(*a);
                }
                // Index * Vectors
                Value::VecIndex(_) => other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= *a),
                Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= C::F::from_usize(*a)),
                Value::VecG1(_) | Value::VecG1Affine(_) => other
                    .into_vec_g1_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= C::F::from_usize(*a)),
                Value::VecG2(_) | Value::VecG2Affine(_) => other
                    .into_vec_g2_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= C::F::from_usize(*a)),
                Value::VecGT(_) => other
                    .into_vec_gt_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= C::F::from_usize(*a)),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                Value::Poly(poly) => {
                    *other = Value::poly(poly.poly_mul_scalar(C::F::from_usize(*a)));
                }
                Value::Record(_) => {
                    panic!("Cannot multiply Index and Record")
                }
                Value::Unit => panic!("Cannot multiply Index and Unit"),
                Value::Bool(_) => panic!("Cannot multiply Index and Bool"),
            },
            Value::Record(_) => {
                panic!("Cannot multiply records")
            }
            Value::Scalar(a) => match &other {
                // Scalar * index, cast index to Scalar
                Value::Index(b) => {
                    let mut value = C::F::from_usize(*b);
                    value *= *a;
                    *other = Value::Scalar(value);
                }
                // Scalar * Scalar = Scalar
                Value::Scalar(_) => *other.into_scalar_mut() *= *a,
                // Index * groups
                Value::G1(_) | Value::G1Affine(_) => {
                    let group = other.into_g1_mut();
                    *group *= *a;
                }
                Value::G2(_) | Value::G2Affine(_) => {
                    let group = other.into_g2_mut();
                    *group *= *a;
                }
                Value::GT(_) => {
                    let group = other.into_gt_mut();
                    *group *= *a;
                }
                // Scalar * Vector
                Value::VecIndex(_) | Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= *a),
                Value::VecG1(_) | Value::VecG1Affine(_) => other
                    .into_vec_g1_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= *a),
                Value::VecG2(_) | Value::VecG2Affine(_) => other
                    .into_vec_g2_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= *a),
                Value::VecGT(_) => other
                    .into_vec_gt_mut()
                    .par_iter_mut()
                    .for_each(|b| *b *= *a),
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                Value::Poly(poly) => {
                    *other = Value::poly(poly.poly_mul_scalar(*a));
                }
                Value::Record(_) => {
                    panic!("Cannot multiply Scalar and Record")
                }
                Value::Unit => panic!("Cannot multiply Scalar and Unit"),
                Value::Bool(_) => panic!("Cannot multiply Scalar and Bool"),
            },
            Value::G1(a) => match &other {
                // G1 * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let mut group = a.batch_mul(&[other.into_scalar()]);
                    *other = Value::g1_affine(group.remove(0));
                }
                // G1 * Vec<Index/Scalar> = VecG1Affine (broadcast scalar mul)
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    *other = Value::vec_g1_affine(a.batch_mul(vr));
                }
                // G1 * G2 = GT (pairing)
                Value::G2(b) => *other = Value::GT(<C::P as Pairing>::pairing(a, b).into()),
                Value::G2Affine(b) => {
                    *other = Value::GT(<C::P as Pairing>::pairing(a, &(**b).into()).into())
                }
                // G1 * VecG2 = VecGT (broadcast pairing)
                Value::VecG2(b) => {
                    let g1_vec = vec![**a; b.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(&g1_vec, b))
                }
                Value::VecG2Affine(b) => {
                    let g2: Vec<_> = b.iter().map(|b| (*b).into()).collect();
                    let g1_vec = vec![**a; g2.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(&g1_vec, &g2))
                }
                // G1 * Vec<T> = Vec<T'> (broadcast)
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                _ => panic!("Cannot multiply G1 and {}", other),
            },
            Value::G2(a) => match &other {
                // G2 * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let mut group = a.batch_mul(&[other.into_scalar()]);
                    *other = Value::g2_affine(group.remove(0));
                }
                // G2 * Vec<Index/Scalar> = VecG2Affine (broadcast scalar mul)
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    *other = Value::vec_g2_affine(a.batch_mul(vr));
                }
                // G2 * G1 = GT (pairing)
                Value::G1(b) => *other = Value::GT(<C::P as Pairing>::pairing(b, a).into()),
                Value::G1Affine(b) => {
                    *other = Value::GT(<C::P as Pairing>::pairing(&(**b).into(), a).into())
                }
                // G2 * VecG1 = VecGT (broadcast pairing)
                Value::VecG1(b) => {
                    let g2_vec = vec![**a; b.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(b, &g2_vec))
                }
                Value::VecG1Affine(b) => {
                    let g1: Vec<_> = b.iter().map(|b| (*b).into()).collect();
                    let g2_vec = vec![**a; g1.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(&g1, &g2_vec))
                }
                // G2 * Vec<T> = Vec<T'> (broadcast)
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                _ => panic!("Cannot multiply G2 and {}", other),
            },
            Value::G1Affine(a) => Self::value_mul(&Value::g1((**a).into()), other),
            Value::G2Affine(a) => Self::value_mul(&Value::g2((**a).into()), other),
            Value::GT(a) => match &other {
                // GT * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let vr = vec![*other.into_scalar_mut()];
                    let mut group = a.batch_mul(&vr);
                    *other = Value::GT(group.remove(0).into());
                }
                // GT * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    *other = Value::vec_gt(a.batch_mul(vr))
                }
                // GT * Vec<T>
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .for_each(|b| self.value_mul(b)),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecIndex(v) => match &other {
                // Vec<Index> * Index
                Value::Index(i) => {
                    *other = Value::VecIndex(v.par_iter().map(|a| *a * *i).collect())
                }
                // Vec<Index> * Scalar
                Value::Scalar(_) => {
                    *other = Value::vec_scalar(
                        std::iter::repeat_n(other.into_scalar(), v.len()).collect::<Vec<_>>(),
                    );
                    v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| *b *= C::F::from_usize(*a))
                }
                // Vec<index> * Group1
                Value::G1(_) | Value::G1Affine(_) => {
                    *other = Value::vec_g1_affine(
                        other.into_g1_mut().batch_mul(
                            &v.par_iter()
                                .map(|a| C::F::from_usize(*a))
                                .collect::<Vec<_>>(),
                        ),
                    )
                }
                // Vec<index> * G2
                Value::G2(_) | Value::G2Affine(_) => {
                    *other = Value::vec_g2_affine(
                        other.into_g2_mut().batch_mul(
                            &v.par_iter()
                                .map(|a| C::F::from_usize(*a))
                                .collect::<Vec<_>>(),
                        ),
                    )
                }
                // Vec<index> * GT
                Value::GT(g) => {
                    *other = Value::vec_gt(
                        g.batch_mul(
                            &v.par_iter()
                                .map(|a| C::F::from_usize(*a))
                                .collect::<Vec<_>>(),
                        ),
                    )
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
                    .for_each(|(a, b)| *b *= C::F::from_usize(*a)),
                // Vec<Index> * Vec<Group1> = Vec<Group1>
                Value::VecG1(_) | Value::VecG1Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g1_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= C::F::from_usize(*a)),
                // Vec<Index> * Vec<G2> = Vec<G2>
                Value::VecG2(_) | Value::VecG2Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g2_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= C::F::from_usize(*a)),
                // Vec<Index> * Vec<GT> = Vec<GT>
                Value::VecGT(_) => v
                    .par_iter()
                    .zip(other.into_vec_gt_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= C::F::from_usize(*a)),
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
                Value::Unit => panic!("Cannot multiply Vec<Index> and Unit"),
                Value::Bool(_) => panic!("Cannot multiply Vec<Index> and Bool"),
            },
            Value::VecScalar(v) => match &other {
                // Vec<Scalar> * Index
                Value::Index(_) | Value::Scalar(_) => {
                    *other = Value::vec_scalar(
                        std::iter::repeat_n(other.into_scalar(), v.len()).collect::<Vec<_>>(),
                    );
                    v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .for_each(|(a, b)| *b *= a)
                }
                // Vec<Scalar> * Group1
                Value::G1(g) => *other = Value::vec_g1_affine(g.batch_mul(v)),
                // Vec<index> * G2
                Value::G2(g) => *other = Value::vec_g2_affine(g.batch_mul(v)),
                // Vec<index> * GT
                Value::GT(g) => *other = Value::vec_gt(g.batch_mul(v)),
                // Vec<Scalar> * Vec<Scalar> = Vec<Scalar>
                Value::VecIndex(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= *a),
                // Vec<Scalar> * Vec<Scalar> = Vec<Scalar>
                Value::VecScalar(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= *a),
                // Vec<Scalar> * Vec<Group1> = Vec<Group1>
                Value::VecG1(_) | Value::VecG1Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g1_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= *a),
                // Vec<Scalar> * Vec<G2> = Vec<G2>
                Value::VecG2(_) | Value::VecG2Affine(_) => v
                    .par_iter()
                    .zip(other.into_vec_g2_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= *a),
                // Vec<Scalar> * Vec<GT> = Vec<GT>
                Value::VecGT(_) => v
                    .par_iter()
                    .zip(other.into_vec_gt_mut().par_iter_mut())
                    .for_each(|(a, b)| *b *= *a),
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
                    *other = Value::vec_g1(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                gm *= a;
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<Group1> * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vl = &*other.into_vec_scalar_mut();
                    let mut vr = v.to_vec();
                    vl.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_g1(vr);
                }
                // VecG1 * G2 = VecGT (broadcast pairing)
                Value::G2(b) => {
                    let g2_vec = vec![**b; v.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(v, &g2_vec))
                }
                Value::G2Affine(b) => {
                    let g2_vec = vec![(**b).into(); v.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(v, &g2_vec))
                }
                // VecG1 * VecG2 = VecGT (element-wise pairing)
                Value::VecG2(b) => *other = Value::vec_gt(<C::P as Pairing>::pairings(v, b)),
                Value::VecG2Affine(b) => {
                    let g2: Vec<_> = b.iter().map(|b| (*b).into()).collect();
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(v, &g2))
                }
                // Vec<Group1> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::g1(*a).value_mul(b)),
                _ => panic!("Cannot multiply VecG1 and {}", other),
            },
            Value::VecG2(v) => match &other {
                // Vec<G2> * scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let a = other.into_scalar();
                    *other = Value::vec_g2(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                gm *= a;
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<G2> * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vl = &*other.into_vec_scalar_mut();
                    let mut vr = v.to_vec();
                    vl.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_g2(vr);
                }
                // VecG2 * G1 = VecGT (broadcast pairing)
                Value::G1(b) => {
                    let g1_vec = vec![**b; v.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(&g1_vec, v))
                }
                Value::G1Affine(b) => {
                    let g1_vec = vec![(**b).into(); v.len()];
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(&g1_vec, v))
                }
                // VecG2 * VecG1 = VecGT (element-wise pairing)
                Value::VecG1(b) => *other = Value::vec_gt(<C::P as Pairing>::pairings(b, v)),
                Value::VecG1Affine(b) => {
                    let g1: Vec<_> = b.iter().map(|b| (*b).into()).collect();
                    *other = Value::vec_gt(<C::P as Pairing>::pairings(&g1, v))
                }
                // Vec<G2> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::g2(*a).value_mul(b)),
                _ => panic!("Cannot multiply VecG2 and {}", other),
            },
            Value::VecG1Affine(v) => Self::value_mul(
                &Value::vec_g1(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            ),
            Value::VecG2Affine(v) => Self::value_mul(
                &Value::vec_g2(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            ),
            Value::VecGT(v) => match &other {
                // Vec<GT> * scalar multiplication
                Value::Scalar(_) | Value::Index(_) => {
                    let a = other.into_scalar();
                    *other = Value::vec_gt(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                gm *= a;
                                gm
                            })
                            .collect(),
                    );
                }
                // GT * Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = &*other.into_vec_scalar_mut();
                    let mut vr = v.to_vec();
                    vl.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_gt(vr);
                }
                // Vec<GT> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .for_each(|(a, b)| Value::gt(*a).value_mul(b)),
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Vec(v) => v
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_mul(b)),
            Value::Unit => panic!("Cannot multiply Unit"),
            // && is multiplication in the GB encoding (Bool values are 0/1)
            Value::Bool(a) => match &other {
                Value::Bool(b) => *other = Value::Bool(*a && *b),
                _ => panic!("Cannot multiply Bool and {}", other),
            },
        }
    }

    /// Value division, saves result in other
    ///
    /// # Errors
    /// [`DivisionByZero`] if a divisor (`other`, or an entry of it) is zero.
    #[inline]
    pub fn value_div(&self, other: &mut Self) -> Result<(), DivisionByZero> {
        match self {
            Value::Index(a) => match &other {
                // Index / Index = Index
                Value::Index(b) => *other = Value::Index(index_div(*a, *b)?),
                // Index / whatever, cast index to scalar
                Value::Scalar(_) => {
                    div(&C::F::from_usize(*a), other.into_scalar_mut())?;
                }
                // Index / Poly
                Value::Poly(poly) => {
                    // Can only divide by constant polynomial
                    let mut poly_scalar = poly
                        .to_scalar()
                        .expect("Cannot divide by non-constant polynomial");
                    let numerator = C::F::from_usize(*a);
                    div(&numerator, &mut poly_scalar)?;
                    *other = Value::Scalar(poly_scalar);
                }
                // Index / Vectors
                Value::VecIndex(_) => {
                    other
                        .into_vec_index_mut()
                        .par_iter_mut()
                        .try_for_each(|b| {
                            *b = index_div(*a, *b)?;
                            Ok(())
                        })?
                }
                Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .try_for_each(|b| div(&C::F::from_usize(*a), b))?,
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .try_for_each(|b| self.value_div(b))?,
                Value::Record(_) => {
                    panic!("Cannot divide Index and Record")
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Scalar(a) => match &other {
                // Scalar / index, cast index to Scalar
                Value::Index(b) => {
                    let mut quotient = C::F::from_usize(*b);
                    div(a, &mut quotient)?;
                    *other = Value::Scalar(quotient);
                }
                // Scalar / Scalar = Scalar
                Value::Scalar(_) => div(a, other.into_scalar_mut())?,
                // Scalar / Poly
                Value::Poly(poly) => {
                    // Can only divide by constant polynomial
                    let mut poly_scalar = poly
                        .to_scalar()
                        .expect("Cannot divide by non-constant polynomial");
                    div(a, &mut poly_scalar)?;
                    *other = Value::Scalar(poly_scalar);
                }
                // Scalar / Vector
                Value::VecIndex(_) | Value::VecScalar(_) => other
                    .into_vec_scalar_mut()
                    .par_iter_mut()
                    .try_for_each(|b| div(a, b))?,
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .try_for_each(|b| self.value_div(b))?,
                Value::Record(_) => {
                    panic!("Cannot divide Scalar and Record")
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G1(a) => match &other {
                // Group1 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = scalar_inverse(&other.into_scalar())?;
                    let mut g = **a;
                    g *= f;
                    *other = Value::g1(g);
                }
                // Group1 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    batch_inverse(vr)?;
                    *other = Value::vec_g1_affine(a.batch_mul(vr));
                }
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .try_for_each(|b| self.value_div(b))?,

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G2(a) => match &other {
                // G2 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = scalar_inverse(&other.into_scalar())?;
                    let mut g = **a;
                    g *= f;
                    *other = Value::G2(Arc::new(g));
                }
                // G2 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    batch_inverse(vr)?;
                    *other = Value::vec_g2_affine(a.batch_mul(vr));
                }
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .try_for_each(|b| self.value_div(b))?,

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::G1Affine(a) => Self::value_div(&Value::g1((**a).into()), other)?,
            Value::G2Affine(a) => Self::value_div(&Value::g2((**a).into()), other)?,
            Value::GT(a) => match &other {
                // G2 / scalar
                Value::Scalar(_) | Value::Index(_) => {
                    let f = scalar_inverse(&other.into_scalar())?;
                    let mut g = **a;
                    g *= f;
                    *other = Value::GT(Arc::new(g));
                }
                // G2 / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    batch_inverse(vr)?;
                    *other = Value::vec_gt(a.batch_mul(vr));
                }
                Value::Vec(_) => other
                    .into_vec_mut()
                    .par_iter_mut()
                    .try_for_each(|b| self.value_div(b))?,

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecIndex(v) => match &other {
                // Vec<Index> / Index
                Value::Index(i) => {
                    let quotients = v
                        .par_iter()
                        .map(|a| index_div(*a, *i))
                        .collect::<Result<Vec<_>, _>>()?;
                    *other = Value::VecIndex(quotients.into());
                }
                // Vec<Index> / Scalar
                Value::Scalar(_) => {
                    *other = Value::vec_scalar(
                        std::iter::repeat_n(other.into_scalar(), v.len()).collect::<Vec<_>>(),
                    );
                    v.par_iter()
                        .zip(other.into_vec_scalar_mut().par_iter_mut())
                        .try_for_each(|(a, b)| div(&C::F::from_usize(*a), b))?;
                }
                // Vec<Index> / Vec<Index> = Vec<Index>
                Value::VecIndex(_) => v
                    .par_iter()
                    .zip(other.into_vec_index_mut().par_iter_mut())
                    .try_for_each(|(a, b)| {
                        *b = index_div(*a, *b)?;
                        Ok(())
                    })?,
                // Vec<Index> * Vec<Scalar> = Vec<Scalar>
                Value::VecScalar(_) => v
                    .par_iter()
                    .zip(other.into_vec_scalar_mut().par_iter_mut())
                    .try_for_each(|(a, b)| div(&C::F::from_usize(*a), b))?,
                // Vec<Index> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .try_for_each(|(a, b)| Value::Index(*a).value_div(b))?,

                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecScalar(v) => match &other {
                // Vec<Scalar> / Index
                Value::Index(_) | Value::Scalar(_) => {
                    let f_inv = scalar_inverse(&other.into_scalar())?;
                    let mut vr = vec![f_inv; v.len()];
                    v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_scalar(vr);
                }
                // Vec<Index> / Vec<Index> = Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    let vr = other.into_vec_scalar_mut();
                    batch_inverse(vr)?;
                    v.par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                }
                // Vec<Scalar> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .try_for_each(|(a, b)| Value::Scalar(*a).value_div(b))?,
                Value::Record(_) => {
                    panic!("Cannot divide Vec<Scalar> and Record")
                }
                _ => panic!("Expected vec index, found {}", other),
            },
            Value::VecG1(v) => match &other {
                // Vec<Group1> / scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let f_inv = scalar_inverse(&other.into_scalar())?;
                    *other = Value::vec_g1(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                gm *= f_inv;
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<Group1> / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = other.into_vec_scalar_mut();
                    batch_inverse(vl)?;
                    let mut vr = v.to_vec();
                    (*vl)
                        .par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_g1(vr);
                }
                // Vec<G1> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .try_for_each(|(a, b)| Value::g1(*a).value_div(b))?,
                Value::Record(_) => {
                    panic!("Cannot divide Vec<G1> and Record")
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecG2(v) => match &other {
                // Vec<Group1> / scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let f_inv = scalar_inverse(&other.into_scalar())?;
                    *other = Value::vec_g2(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                gm *= f_inv;
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<Group1> / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = other.into_vec_scalar_mut();
                    batch_inverse(vl)?;
                    let mut vr = v.to_vec();
                    (*vl)
                        .par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_g2(vr);
                }
                // Vec<G2> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .try_for_each(|(a, b)| Value::g2(*a).value_div(b))?,
                Value::Record(_) => {
                    panic!("Cannot divide Vec<G2> and Record")
                }
                _ => panic!("Expected scalar, found {}", other),
            },
            Value::VecG1Affine(v) => Self::value_div(
                &Value::vec_g1(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            )?,
            Value::VecG2Affine(v) => Self::value_div(
                &Value::vec_g2(v.par_iter().map(|a| (*a).into()).collect()),
                other,
            )?,
            Value::VecGT(v) => match &other {
                // Vec<GT> / scalar multiplication
                Value::Index(_) | Value::Scalar(_) => {
                    let f_inv = scalar_inverse(&other.into_scalar())?;
                    *other = Value::vec_gt(
                        v.par_iter()
                            .map(|g| {
                                let mut gm = *g;
                                gm *= f_inv;
                                gm
                            })
                            .collect(),
                    );
                }
                // Vec<Group1> / Vec<Index>
                Value::VecIndex(_) | Value::VecScalar(_) => {
                    // TODO: There has to be a better way to do this...
                    let vl = other.into_vec_scalar_mut();
                    batch_inverse(vl)?;
                    let mut vr = v.to_vec();
                    (*vl)
                        .par_iter()
                        .zip(vr.par_iter_mut())
                        .for_each(|(a, b)| *b *= *a);
                    *other = Value::vec_gt(vr);
                }
                // Vec<GT> * Vec<T>
                Value::Vec(_) => v
                    .par_iter()
                    .zip(other.into_vec_mut().par_iter_mut())
                    .try_for_each(|(a, b)| Value::gt(*a).value_div(b))?,

                _ => panic!("Expected scalar, found {}", other),
            },
            Value::Vec(v) => v
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .try_for_each(|(a, b)| a.value_div(b))?,
            Value::Poly(p) => match &other {
                Value::Poly(o) => {
                    *other = Value::poly(poly_quotient(p.poly_div(o))?);
                }
                Value::Scalar(_) | Value::Index(_) => {
                    *other = Value::poly(poly_quotient(p.poly_div_scalar(other.into_scalar()))?);
                }
                Value::Record(_) => {
                    panic!("Cannot divide Poly and Record")
                }
                _ => panic!("Expected poly, found {}", other),
            },
            Value::Record(_) => {
                panic!("Cannot divide records")
            }
            Value::Unit => panic!("Cannot divide Unit"),
            Value::Bool(_) => panic!("Cannot divide Bool"),
        }
        Ok(())
    }

    /// Computes `self % other`, storing the result in `other`.
    ///
    /// Defined only on index-typed values, which are the loop and array-offset
    /// domain; a field has no remainder operation.
    ///
    /// # Errors
    /// [`DivisionByZero`] if a divisor (`other`, or an entry of it) is zero.
    ///
    /// # Panics
    /// Panics if either operand is not an `Index` or `VecIndex`.
    pub fn value_rem(&self, other: &mut Self) -> Result<(), DivisionByZero> {
        match (self, &other) {
            (Value::Index(a), Value::Index(b)) => *other = Value::Index(index_rem(*a, *b)?),
            (Value::Index(i), Value::VecIndex(_)) => {
                other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .try_for_each(|v| {
                        *v = index_rem(*i, *v)?;
                        Ok(())
                    })?;
            }
            (Value::VecIndex(vs), Value::Index(i)) => {
                let remainders = vs
                    .par_iter()
                    .map(|v| index_rem(*v, *i))
                    .collect::<Result<Vec<_>, _>>()?;
                *other = Value::VecIndex(remainders.into());
            }
            (Value::VecIndex(vs), Value::VecIndex(_)) => {
                other
                    .into_vec_index_mut()
                    .par_iter_mut()
                    .zip(vs.par_iter())
                    .try_for_each(|(v, i)| {
                        *v = index_rem(*i, *v)?;
                        Ok(())
                    })?;
            }
            (_, _) => panic!("Cannot do {} % {}", self, other),
        }
        Ok(())
    }

    /// Value exponentiation, saves result in other
    pub fn value_pow(&self, other: &mut Self) {
        #[inline]
        fn pow64(mut base: usize, mut exp: usize) -> usize {
            let mut acc = 1usize;
            while exp > 0 {
                if exp % 2 == 1 {
                    acc *= base;
                }
                exp /= 2;
                if exp > 0 {
                    base *= base;
                }
            }
            acc
        }
        match (self, &other) {
            // Index ^ Index = Index
            (Value::Index(a), Value::Index(i)) => *other.into_index_mut() = pow64(*a, *i),
            // Scalar ^ Index
            (Value::Scalar(a), Value::Index(i)) => {
                let mut a = *a;
                a = a.pow(*i as u64);
                *other = Value::Scalar(a);
            }
            // Vec<Index> ^ Index
            (Value::VecIndex(vs), Value::Index(i)) => {
                let mut vs = vs.clone();
                vs.to_mut().par_iter_mut().for_each(|v| *v = pow64(*v, *i));
                *other = Value::VecIndex(vs);
            }
            // Vec<Scalar> ^ Index
            (Value::VecScalar(vs), Value::Index(i)) => {
                let mut vs = vs.to_vec();
                vs.par_iter_mut().for_each(|v| *v = v.pow(*i as u64));
                *other = Value::vec_scalar(vs);
            }

            // Vec<T> ^ Index
            (Value::Vec(vs), Value::Index(_)) => {
                let mut vs = vs.clone();
                vs.to_mut()
                    .par_iter_mut()
                    .for_each(|v| Value::value_pow(other, v));
                *other = Value::Vec(vs);
            }
            (a, b) => panic!("Mismatched values {} ^ {}", a, b),
        }
    }

    /// Reports whether this value is the multiplicative identity.
    ///
    /// A vector is one only if every element is, and `Bool(true)` counts as one
    /// under the 0/1 encoding used when booleans feed arithmetic. Every other
    /// variant, including a constant-one polynomial, answers `false`.
    #[inline]
    pub fn is_one(&self) -> bool {
        match self {
            Value::Index(a) => *a == 1,
            Value::VecIndex(a) => a.iter().all(|a| *a == 1),
            Value::Scalar(a) => a == &C::F::one(),
            Value::VecScalar(a) => a.iter().all(|a| a == &C::F::one()),
            Value::Bool(b) => *b,
            _ => false,
        }
    }

    /// Value equality
    #[inline]
    pub fn equ(a: &Self, other: &Self) -> bool {
        match (a, other) {
            (Value::Index(a), Value::Index(b)) => *a == *b,
            (Value::Scalar(a), Value::Scalar(b)) => a == b,
            (Value::Scalar(a), Value::Index(b)) => *a == C::F::from_usize(*b),
            (Value::Index(a), Value::Scalar(b)) => C::F::from_usize(*a) == *b,
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| *a == *b)
            }
            (Value::VecScalar(a), Value::VecScalar(b)) => {
                a.par_iter().zip(b.par_iter()).all(|(a, b)| *a == *b)
            }
            (Value::VecIndex(a), Value::VecScalar(b)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| C::F::from_usize(*a) == *b),
            (Value::VecScalar(a), Value::VecIndex(b)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| C::F::from_usize(*b) == *a),
            (Value::G1(a), Value::G1(b)) => a == b,
            (Value::G2(a), Value::G2(b)) => a == b,
            (Value::GT(a), Value::GT(b)) => a == b,
            (Value::G1Affine(a), Value::G1(b)) | (Value::G1(b), Value::G1Affine(a)) => {
                **a == b.normalize()
            }
            (Value::G2Affine(a), Value::G2(b)) | (Value::G2(b), Value::G2Affine(a)) => {
                **a == b.normalize()
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
                    .all(|(a, b)| &a.normalize() == b)
            }
            (Value::VecG2(a), Value::VecG2Affine(b)) | (Value::VecG2Affine(b), Value::VecG2(a)) => {
                a.par_iter()
                    .zip(b.par_iter())
                    .all(|(a, b)| &a.normalize() == b)
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
                .all(|(a, b)| Value::equ(a, &Value::g1(*b))),
            (Value::Vec(a), Value::VecG2(b)) | (Value::VecG2(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::g2(*b))),
            (Value::Vec(a), Value::VecGT(b)) | (Value::VecGT(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::gt(*b))),
            (Value::Vec(a), Value::VecG1Affine(b)) | (Value::VecG1Affine(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::g1_affine(*b))),
            (Value::Vec(a), Value::VecG2Affine(b)) | (Value::VecG2Affine(b), Value::Vec(a)) => a
                .par_iter()
                .zip(b.par_iter())
                .all(|(a, b)| Value::equ(a, &Value::g2_affine(*b))),
            (Value::G1Affine(a), Value::G1Affine(b)) => a == b,
            (Value::G2Affine(a), Value::G2Affine(b)) => a == b,
            (Value::VecG1Affine(a), Value::VecG1Affine(b)) => a == b,
            (Value::VecG2Affine(a), Value::VecG2Affine(b)) => a == b,
            (Value::Poly(a), Value::Poly(b)) => {
                // Use PolyVariant's PartialEq implementation
                a == b
            }
            (Value::Record(a), Value::Record(b)) => a == b,
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (a, b) => panic!("Cannot compare {} == {}", a, b),
        }
    }

    /// `self op other`.
    ///
    /// # Errors
    /// [`DivisionByZero`] if `op` is `/` or `%` and a divisor is zero.
    pub fn value_bin(self, op: BinOp, other: Self) -> Result<Self, DivisionByZero> {
        // Each `value_*` writes its result into `other`.
        let mut other = other;
        match op {
            BinOp::Add => self.value_add(&mut other),
            BinOp::Sub => self.value_sub(&mut other),
            // && is multiplication in the GB encoding (Bool values are 0/1).
            BinOp::Mul | BinOp::And => self.value_mul(&mut other),
            BinOp::Div => self.value_div(&mut other)?,
            BinOp::Rem => self.value_rem(&mut other)?,
            BinOp::Pow => self.value_pow(&mut other),
            BinOp::Dot => self.value_dot(&mut other),
            BinOp::Concat => return Ok(self.value_concat(other)),
            BinOp::Equ => return Ok(Value::Bool(Value::equ(&self, &other))),
        }
        Ok(other)
    }

    /// Reduce a vector using a binary operation.
    /// Commutative operations (Add, Mul) use parallel fold via rayon.
    /// Non-commutative operations use sequential left fold.
    ///
    /// # Errors
    /// [`DivisionByZero`] if `op` is `/` or `%` and a divisor is zero.
    pub fn value_reduce(self, op: BinOp) -> Result<Self, DivisionByZero> {
        let elements = self.into_elements();
        assert!(!elements.is_empty(), "Cannot reduce empty vector");
        Ok(match op {
            BinOp::Add => {
                if let Some(poly) = reduce_univariate_poly_sum(&elements) {
                    return Ok(Value::poly(poly));
                }
                // The identity element only depends on the kind of the type.
                let elem_typ = elements[0].shape_typ();
                elements
                    .into_par_iter()
                    .reduce(|| Value::<C>::zero(&elem_typ), |a, b| a + b)
            }
            BinOp::Mul => {
                let elem_typ = elements[0].shape_typ();
                elements
                    .into_par_iter()
                    .reduce(|| Value::<C>::one(&elem_typ), |a, b| a * b)
            }
            // && is multiplication in the GB encoding (Bool values are 0/1)
            BinOp::And => {
                let elem_typ = elements[0].shape_typ();
                elements
                    .into_par_iter()
                    .reduce(|| Value::<C>::one(&elem_typ), |a, b| a * b)
            }
            _ => {
                let mut iter = elements.into_iter();
                let first = iter.next().unwrap();
                return iter.try_fold(first, |acc, x| acc.value_bin(op, x));
            }
        })
    }
}
