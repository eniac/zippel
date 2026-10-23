//! Sampling: random values, Fiat–Shamir challenges, and exclusions.

use super::Value;
use super::poly::value_scalars;
use crate::algebra::vec_rand;
use crate::poly::variant::{DenseMle, DenseUni, PolyVariant};
use crate::poly::virtual_polynomial::VirtualPolynomial;
use crate::{ABase, ATyp, Backend, Field, GT, Group};
use lang::ast::Exclusion;
use rand::Rng;
use share::Ctx;
use spongefish::{DuplexSpongeInterface, ProverState};

impl<C: Backend> Value<C> {
    /// Squeezes a fresh scalar-field challenge out of the Fiat-Shamir transcript
    /// held in `state`: 32 sponge bytes, of which the modulus-sized prefix is
    /// reduced modulo the field's prime, so prover and verifier derive the same
    /// value.
    pub fn challenge<H: DuplexSpongeInterface<U = u8>>(state: &mut ProverState<H>) -> Self {
        let bytes: [u8; 32] = state.verifier_message();
        let len = (C::F::MODULUS_BITS as usize).div_ceil(8).min(32);
        Value::Scalar(C::F::from_le_bytes_mod_order(&bytes[..len]))
    }

    /// Generate a random value, given some parameters
    pub fn random<R: Rng + Sized>(rng: &mut R, typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Fin(r)) => Value::Index(r.random(rng) % 10),
            ATyp::Base(ABase::Unit) => Value::Unit,
            ATyp::Base(ABase::Bool) => Value::Bool(rng.r#gen()),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::F::rand(rng)),
            ATyp::Base(ABase::G1) => Value::g1(C::G1::rand(rng)),
            ATyp::Base(ABase::G2) => Value::g2(C::G2::rand(rng)),
            ATyp::Base(ABase::GT) => Value::GT(GT::<C>::rand(rng).into()),
            ATyp::Vec(ATyp::Base(ABase::Fin(r)), n) => {
                Value::VecIndex((0..*n).map(|_| r.random(rng)).collect())
            }
            ATyp::Vec(ATyp::Base(ABase::Scalar), n) => Value::vec_scalar(vec_rand(rng, *n)),
            ATyp::Vec(ATyp::Base(ABase::G1), n) => {
                Value::vec_g1((0..*n).map(|_| C::G1::rand(rng)).collect())
            }
            ATyp::Vec(ATyp::Base(ABase::G2), n) => {
                Value::vec_g2((0..*n).map(|_| C::G2::rand(rng)).collect())
            }
            ATyp::Vec(ATyp::Base(ABase::GT), n) => {
                Value::vec_gt((0..*n).map(|_| GT::<C>::rand(rng)).collect())
            }
            ATyp::Vec(deref!(t), n) => Value::Vec((0..*n).map(|_| Self::random(rng, t)).collect()),
            // Univariate poly: m = max_degree, so m+1 coefficients.
            ATyp::Uni(m) => {
                let mut coeffs: Vec<C::F> = vec_rand(rng, *m + 1);
                if *m > 0 {
                    while coeffs[*m].is_zero() {
                        coeffs[*m] = C::F::rand(rng);
                    }
                }
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                    DenseUni::new(coeffs),
                )))
            }
            // Multilinear extension on the {0,1}^n hypercube: 2^n evaluations.
            ATyp::Mle(n) => {
                let evals = vec_rand(rng, 1usize << *n);
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMle::new(*n, evals),
                )))
            }
            // n-variate poly, max total degree m. For n <= 1 produce a
            // univariate of degree m; otherwise a multilinear extension as
            // a representative inhabitant of the type.
            ATyp::VPoly(n, m) => {
                if *n <= 1 {
                    let mut coeffs: Vec<C::F> = vec_rand(rng, *m + 1);
                    if *m > 0 {
                        while coeffs[*m].is_zero() {
                            coeffs[*m] = C::F::rand(rng);
                        }
                    }
                    Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseUni(
                        DenseUni::new(coeffs),
                    )))
                } else {
                    let evals = vec_rand(rng, 1usize << *n);
                    Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                        DenseMle::new(*n, evals),
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

    /// Whether `exclusion` excludes this sample: an entry of a scalar or
    /// index vector, or an `n`-th root of unity.
    ///
    /// # Panics
    /// Panics if this is not a scalar.
    pub fn is_excluded_by(&self, exclusion: &Exclusion<Self, usize>) -> bool {
        match (exclusion, self) {
            (Exclusion::Values(values), Value::Scalar(x)) => value_scalars::<C>(values).contains(x),
            (Exclusion::RootsOfUnity(n), Value::Scalar(x)) => x.pow(*n as u64) == C::F::one(),
            _ => panic!("Expected a scalar sample, found {self}"),
        }
    }
}
