//! Group operations on values: inner products (MSMs, multi-pairings) and pairings,
//! using a key a vector carries when it speeds one up.

use super::Value;
use crate::{Backend, Field, GT, Group, Pairing};
use rayon::prelude::*;

impl<C: Backend> Value<C> {
    /// Applies the bilinear pairing to `self` and `other`, storing the target group
    /// result in `other`.
    ///
    /// Accepts the two source groups in either order and in either affine or
    /// projective form; vector operands pair component-wise and yield a vector of
    /// target group elements.
    ///
    /// # Panics
    /// Panics if the operands are not a source-group pair of matching shape, or if
    /// either operand is a record.
    #[inline]
    pub fn value_pair(&self, other: &mut Self) {
        match (self, &other) {
            (Value::G1(a), Value::G2(b)) | (Value::G2(b), Value::G1(a)) => {
                *other = Value::GT(<C::P as Pairing>::pairing(a, b).into())
            }
            (Value::G1Affine(a), Value::G2Affine(b)) | (Value::G2Affine(b), Value::G1Affine(a)) => {
                *other = Value::GT(<C::P as Pairing>::pairing(&(**a).into(), &(**b).into()).into())
            }
            (Value::G1(a), Value::G2Affine(b)) => {
                *other = Value::GT(<C::P as Pairing>::pairing(a, &(**b).into()).into())
            }
            (Value::G2(a), Value::G1Affine(b)) => {
                *other = Value::GT(<C::P as Pairing>::pairing(&(**b).into(), a).into())
            }
            (Value::G1Affine(a), Value::G2(b)) => {
                *other = Value::GT(<C::P as Pairing>::pairing(&(**a).into(), b).into())
            }
            (Value::G2Affine(a), Value::G1(b)) => {
                *other = Value::GT(<C::P as Pairing>::pairing(b, &(**a).into()).into())
            }
            // Vectors
            (Value::VecG1(a), Value::VecG2(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(a, b))
            }
            (Value::VecG2(b), Value::VecG1(a)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(a, b))
            }
            (Value::VecG1Affine(a), Value::VecG2Affine(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(
                    &a.iter().map(|a| (*a).into()).collect::<Vec<_>>(),
                    &b.iter().map(|b| (*b).into()).collect::<Vec<_>>(),
                ))
            }
            (Value::VecG2Affine(a), Value::VecG1Affine(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(
                    &b.iter().map(|b| (*b).into()).collect::<Vec<_>>(),
                    &a.iter().map(|a| (*a).into()).collect::<Vec<_>>(),
                ))
            }
            (Value::VecG1(a), Value::VecG2Affine(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(
                    a,
                    &b.iter().map(|b| (*b).into()).collect::<Vec<_>>(),
                ))
            }
            (Value::VecG2(a), Value::VecG1Affine(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(
                    &b.iter().map(|b| (*b).into()).collect::<Vec<_>>(),
                    a,
                ))
            }
            (Value::VecG1Affine(a), Value::VecG2(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(
                    &a.iter().map(|a| (*a).into()).collect::<Vec<_>>(),
                    b,
                ))
            }
            (Value::VecG2Affine(a), Value::VecG1(b)) => {
                *other = Value::vec_gt(<C::P as Pairing>::pairings(
                    b,
                    &a.iter().map(|b| (*b).into()).collect::<Vec<_>>(),
                ))
            }
            (Value::Record(_), _) | (_, Value::Record(_)) => {
                panic!("Cannot pair records")
            }
            _ => panic!("Cannot pair {} and {}", self, other),
        }
    }

    /// Computes the dot product of `self` and `other`, storing it in `other`.
    ///
    /// This is the hot prover primitive. Scalar-times-group arms lower to a batched
    /// multi-scalar multiplication, and a projective basis is first converted with
    /// `normalize_batch` so the whole batch costs one field inversion instead of one
    /// per element. Group-times-group arms lower to a multi-pairing, and nested
    /// `Value::Vec` operands recurse element-wise.
    ///
    /// # Panics
    /// Panics if the operand pair has no dot-product rule, and on a length
    /// mismatch in the group arms (MSMs and pairings). The scalar arm's zipped
    /// iteration truncates to the shorter operand instead.
    #[inline]
    pub fn value_dot(&self, other: &mut Self) {
        // A G2 vector with a key pairs through the backend, which may use the key; any
        // other dot sees its points.
        let keyed_pairing = match (self, &*other) {
            (Value::VecG1(a), Value::VecG2Affine(b)) | (Value::VecG2Affine(b), Value::VecG1(a))
                if b.key().is_some() =>
            {
                Some(C::multi_pairing(a, b))
            }
            (Value::VecG1Affine(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecG1Affine(a))
                if b.key().is_some() =>
            {
                let g1 = a.iter().map(|a| (*a).into()).collect::<Vec<_>>();
                Some(C::multi_pairing(&g1, b))
            }
            _ => None,
        };
        if let Some(gt) = keyed_pairing {
            *other = Value::GT(gt.into());
            return;
        }
        match (&self, &other) {
            (Value::VecG1(a), Value::VecG2(b)) => {
                *other = Value::GT(<C::P as Pairing>::multi_pairing(a, b).into())
            }
            (Value::VecG2(b), Value::VecG1(a)) => {
                *other = Value::GT(<C::P as Pairing>::multi_pairing(a, b).into())
            }
            (Value::VecG1Affine(a), Value::VecG2Affine(b)) => {
                let g1 = a.iter().map(|a| (*a).into()).collect::<Vec<_>>();
                let g2 = b.iter().map(|b| (*b).into()).collect::<Vec<_>>();
                *other = Value::GT(<C::P as Pairing>::multi_pairing(&g1, &g2).into())
            }
            (Value::VecG2Affine(b), Value::VecG1Affine(a)) => {
                let g1 = a.iter().map(|a| (*a).into()).collect::<Vec<_>>();
                let g2 = b.iter().map(|b| (*b).into()).collect::<Vec<_>>();
                *other = Value::GT(<C::P as Pairing>::multi_pairing(&g1, &g2).into())
            }
            (Value::VecG1(a), Value::VecG2Affine(b)) => {
                let g2 = b.iter().map(|b| (*b).into()).collect::<Vec<_>>();
                *other = Value::GT(<C::P as Pairing>::multi_pairing(a, &g2).into())
            }
            (Value::VecG2Affine(b), Value::VecG1(a)) => {
                let g2 = b.iter().map(|b| (*b).into()).collect::<Vec<_>>();
                *other = Value::GT(<C::P as Pairing>::multi_pairing(a, &g2).into())
            }
            (Value::VecG1Affine(a), Value::VecG2(b)) => {
                let g1 = a.iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::GT(<C::P as Pairing>::multi_pairing(&g1, b).into())
            }
            (Value::VecG2(b), Value::VecG1Affine(a)) => {
                let g1 = a.iter().map(|a| (*a).into()).collect::<Vec<_>>();
                *other = Value::GT(<C::P as Pairing>::multi_pairing(&g1, b).into())
            }
            (Value::VecIndex(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a
                    .par_iter()
                    .map(|a| C::F::from_usize(*a))
                    .collect::<Vec<_>>();
                *other = Value::g1(C::G1::msm(b, &vf));
            }
            (Value::VecIndex(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a
                    .par_iter()
                    .map(|a| C::F::from_usize(*a))
                    .collect::<Vec<_>>();
                *other = Value::g2(C::G2::msm(b, &vf));
            }
            (Value::VecIndex(a), Value::VecGT(b)) | (Value::VecGT(b), Value::VecIndex(a)) => {
                let vf: Vec<C::F> = a
                    .par_iter()
                    .map(|a| C::F::from_usize(*a))
                    .collect::<Vec<_>>();
                *other = Value::GT(GT::<C>::msm(b, &vf).into());
            }
            (Value::VecScalar(a), Value::VecG1Affine(b))
            | (Value::VecG1Affine(b), Value::VecScalar(a)) => *other = Value::g1(C::msm_g1(b, a)),
            (Value::VecScalar(a), Value::VecG2Affine(b))
            | (Value::VecG2Affine(b), Value::VecScalar(a)) => *other = Value::g2(C::msm_g2(b, a)),
            (Value::VecScalar(a), Value::VecGT(b)) | (Value::VecGT(b), Value::VecScalar(a)) => {
                *other = Value::GT(GT::<C>::msm(b, a).into())
            }
            (Value::VecG1(b), Value::VecIndex(_)) => {
                let vg = C::G1::normalize_batch(b);
                Self::value_dot(&Value::vec_g1_affine(vg), other);
            }
            (Value::VecIndex(_), Value::VecG1(b)) => {
                let vg = C::G1::normalize_batch(b);
                *other = Value::vec_g1_affine(vg);
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
                let vg = C::G2::normalize_batch(b);
                Self::value_dot(&Value::vec_g2_affine(vg), other);
            }
            (Value::VecG1(b), Value::VecScalar(_)) => {
                let vg = C::G1::normalize_batch(b);
                Self::value_dot(&Value::vec_g1_affine(vg), other);
            }
            (Value::VecScalar(_), Value::VecG1(b)) => {
                let vg = C::G1::normalize_batch(b);
                *other = Value::vec_g1_affine(vg);
                Self::value_dot(self, other);
            }
            (Value::VecG2(b), Value::VecScalar(_)) => {
                let vg = C::G2::normalize_batch(b);
                Self::value_dot(&Value::vec_g2_affine(vg), other);
            }
            (Value::VecScalar(_), Value::VecG2(b)) => {
                let vg = C::G2::normalize_batch(b);
                *other = Value::vec_g2_affine(vg);
                Self::value_dot(self, other);
            }
            (Value::VecIndex(a), Value::VecIndex(b)) => {
                *other = Value::Index(a.par_iter().zip(b.par_iter()).map(|(a, b)| *a * *b).sum())
            }
            (Value::VecIndex(v), _) => {
                let vl = v
                    .par_iter()
                    .map(|a| C::F::from_usize(*a))
                    .collect::<Vec<_>>();
                Self::value_dot(&Value::vec_scalar(vl), other);
            }
            (Value::VecScalar(v), _) => {
                let vf = other.into_vec_scalar_mut();
                *other = Value::Scalar(
                    (*vf)
                        .par_iter()
                        .zip(v.par_iter())
                        .map(|(a, b)| {
                            let mut a = *a;
                            a *= *b;
                            a
                        })
                        .reduce(C::F::zero, |mut a, b| {
                            a += b;
                            a
                        }),
                );
            }
            (Value::Vec(a), _) => a
                .par_iter()
                .zip(other.into_vec_mut().par_iter_mut())
                .for_each(|(a, b)| a.value_dot(b)),
            (a, b) => panic!("Mismatched values {} . {}", a, b),
        }
    }

    /// Owning form of [`Value::value_dot`]: consumes both operands and returns the
    /// dot product.
    ///
    /// # Panics
    /// Panics under the same conditions as [`Value::value_dot`].
    #[inline]
    pub fn dot(self, other: Self) -> Self {
        let mut other = other;
        self.value_dot(&mut other);
        other
    }

    /// Owning form of [`Value::value_pair`]: consumes both operands and returns the
    /// target group result.
    ///
    /// # Panics
    /// Panics under the same conditions as [`Value::value_pair`].
    #[inline]
    pub fn pair(self, other: Self) -> Self {
        let mut other = other;
        self.value_pair(&mut other);
        other
    }
}
