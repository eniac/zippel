//! Polynomial operations on values: evaluation, coefficients and MLE encodings,
//! interpolation and FFTs.

use super::Value;
use crate::poly::variant::{DenseMle, DenseUni, PolyVariant};
use crate::poly::virtual_polynomial::{SelectedEvalShape, VirtualPolynomial};
use crate::{ATyp, Backend, DivisionByZero, Field};
use lang::typ::CRange;
use std::sync::Arc;

/// The scalars of a scalar or index vector, borrowed when they are stored as
/// scalars.
pub(super) fn value_scalars<C: Backend>(v: &Value<C>) -> std::borrow::Cow<'_, [C::F]> {
    match v {
        Value::VecScalar(xs) => std::borrow::Cow::Borrowed(xs),
        Value::VecIndex(xs) => xs.iter().map(|i| C::F::from_usize(*i)).collect(),
        _ => panic!("Expected scalar vector, found {}", v),
    }
}

/// `ceil(log2(n))`, and 0 for `n <= 1` (as `ark_std::log2`).
fn ilog2_ceil(n: usize) -> u32 {
    n.next_power_of_two().trailing_zeros()
}

/// The scalars of a scalar or index vector, moved out when `v` is their only
/// owner.
fn value_into_scalar_vec<C: Backend>(v: Value<C>) -> Vec<C::F> {
    match v {
        Value::VecScalar(xs) => xs.into_vec(),
        Value::VecIndex(xs) => xs.iter().map(|i| C::F::from_usize(*i)).collect(),
        _ => panic!("Expected scalar vector, found {}", v),
    }
}

/// Whether `points` are the FFT domain of their length: the powers of a
/// primitive `points.len()`-th root of unity, in order.
fn are_fft_domain_points<C: Backend>(points: &[C::F]) -> bool {
    let n = points.len();
    let Some(root) = n
        .is_power_of_two()
        .then(|| C::F::two_adic_root(n.trailing_zeros()))
        .flatten()
    else {
        return false;
    };
    let mut x = C::F::one();
    points.iter().all(|p| {
        let matches = *p == x;
        x *= root;
        matches
    })
}

impl<C: Backend> Value<C> {
    /// Evaluates `self` at the point `other` and returns the result.
    ///
    /// A `VecScalar`/`VecIndex` receiver is first lifted into a univariate
    /// polynomial via [`Value::value_poly`], because a `Uni` value is often still
    /// carried as its bare coefficient vector at runtime; anything else goes
    /// straight to [`Value::eval`].
    ///
    /// # Panics
    /// Panics if `self` is neither a polynomial nor a coefficient vector, or if
    /// `other` is not a valid point shape; see [`Value::eval`].
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

    /// Partially evaluates a multivariate polynomial, fixing every variable outside
    /// `free_range` to the corresponding entry of `fixed`.
    ///
    /// This backs the selected-evaluation op used by sum-check style protocols.
    /// `shape` carries the statically known input and output arities so the result
    /// keeps the arity its `ATyp` promises instead of collapsing to whatever the
    /// data happens to permit.
    ///
    /// # Panics
    /// Panics if `self` is not (and cannot be lifted to) a polynomial, if `fixed` is
    /// not a scalar vector, or if the fixed-point arity is inconsistent with `shape`
    /// and `free_range`.
    #[inline]
    pub fn value_eval_selected(
        self,
        free_range: CRange,
        fixed: Self,
        shape: SelectedEvalShape,
    ) -> Self {
        let poly_value = if matches!(&self, Value::VecScalar(_) | Value::VecIndex(_)) {
            self.value_poly()
        } else {
            self
        };

        let poly = match poly_value {
            Value::Poly(poly) => poly,
            other => panic!("Selected eval expects a polynomial, found {}", other),
        };

        let mut fixed = fixed;
        let fixed_points = fixed.into_vec_scalar_mut().clone();
        Value::Poly(
            Arc::new(poly.fix_variables_except_range_with_shape(shape, free_range.clone(), &fixed_points)
                .unwrap_or_else(|e| {
                    panic!(
                        "Selected eval failed for static shape {:?}, range {:?}, fixed arity {}: {:?}",
                        shape,
                        free_range,
                        fixed_points.len(),
                        e
                    )
                })),
        )
    }

    /// Produces the univariate round polynomial obtained by summing `self` over the
    /// Boolean hypercube of every variable outside `free_range`.
    ///
    /// This fuses the "fix all but one variable, then sum over the cube" pair of ops
    /// into a single pass. A fast path handles polynomials that are sums of products
    /// of multilinear factors; otherwise the round polynomial is recovered by
    /// evaluating at `0..=degree` and interpolating. Both paths bump the
    /// optimization counters so the fusion rate stays observable.
    ///
    /// # Panics
    /// Panics unless `free_range` is exactly one variable within the input shape,
    /// `shape.output_num_vars` is `1`, and `tail_num_vars` equals
    /// `shape.input_num_vars - 1`. Also panics if `self` is not a polynomial, if
    /// `tail_num_vars` exceeds the `usize` bit width, or if a hypercube evaluation
    /// fails.
    #[inline]
    pub fn value_hypercube_reduce_selected(
        self,
        free_range: CRange,
        tail_num_vars: usize,
        shape: SelectedEvalShape,
    ) -> Self {
        assert_eq!(
            free_range.len(),
            1,
            "hypercube reduce fusion currently requires a single free variable"
        );
        assert_eq!(
            shape.output_num_vars, 1,
            "hypercube reduce fusion currently returns a univariate round polynomial"
        );
        assert_eq!(
            tail_num_vars,
            shape.input_num_vars.saturating_sub(1),
            "hypercube reduce tail arity must match the selected-eval static input shape"
        );

        let poly_value = if matches!(&self, Value::VecScalar(_) | Value::VecIndex(_)) {
            self.value_poly()
        } else {
            self
        };
        let poly = match poly_value {
            Value::Poly(poly) => poly,
            other => panic!("Hypercube reduce expects a polynomial, found {}", other),
        };

        let round =
            poly.sum_over_hypercube_except(free_range.start(), tail_num_vars, shape.max_degree);
        Value::poly(round)
    }

    /// Evaluates the polynomial `self` at the point held in `other`, storing the
    /// result back into `other`.
    ///
    /// A scalar or index point performs univariate evaluation. A vector point
    /// performs multivariate evaluation; when fewer points are supplied than the
    /// polynomial's declared arity, the residual polynomial is kept as a
    /// `Value::Poly` so the value still matches its declared type instead of
    /// silently collapsing to a scalar.
    ///
    /// # Panics
    /// Panics if `self` is not a `Value::Poly`, if `other` is not a valid point
    /// shape, or if the underlying multilinear evaluation fails.
    #[inline]
    pub fn eval(self, other: &mut Self) {
        match (&self, &other) {
            (Value::Poly(poly), Value::VecIndex(b)) => {
                let n_points = b.len();
                let points: Vec<C::F> = b.iter().map(|i| C::F::from_usize(*i)).collect();

                let original_num_vars = poly.num_vars();
                let result_poly = if poly.is_full_point(n_points) {
                    VirtualPolynomial::from_scalar(
                        poly.evaluate_mv(&points).expect("full point evaluates"),
                    )
                } else {
                    poly.evaluate_or_fix(&points)
                        .expect("MLE evaluation failed")
                };

                let keep_typed_residual = original_num_vars.is_some_and(|n| n_points < n)
                    && result_poly.num_vars().is_some();
                *other = if !keep_typed_residual {
                    if let Some(scalar) = result_poly.to_scalar() {
                        if n_points == 1 {
                            Value::vec_scalar(vec![scalar])
                        } else {
                            Value::Scalar(scalar)
                        }
                    } else {
                        Value::poly(result_poly)
                    }
                } else {
                    Value::poly(result_poly)
                };
            }
            (Value::Poly(poly), Value::VecScalar(v)) => {
                let n_points = v.len();

                let original_num_vars = poly.num_vars();
                let result_poly = if poly.is_full_point(n_points) {
                    VirtualPolynomial::from_scalar(
                        poly.evaluate_mv(v).expect("full point evaluates"),
                    )
                } else {
                    poly.evaluate_or_fix(v).expect("MLE evaluation failed")
                };

                let keep_typed_residual = original_num_vars.is_some_and(|n| n_points < n)
                    && result_poly.num_vars().is_some();
                *other = if !keep_typed_residual {
                    if let Some(scalar) = result_poly.to_scalar() {
                        if n_points == 1 {
                            Value::vec_scalar(vec![scalar])
                        } else {
                            Value::Scalar(scalar)
                        }
                    } else {
                        Value::poly(result_poly)
                    }
                } else {
                    Value::poly(result_poly)
                };
            }
            (Value::Poly(poly), Value::Scalar(x)) => {
                *other = Value::Scalar(poly.evaluate_uv(x));
            }
            (Value::Poly(poly), Value::Index(i)) => {
                *other = Value::Scalar(poly.evaluate_uv(&C::F::from_usize(*i)));
            }
            _ => panic!("Cannot eval if not poly or index"),
        }
    }

    /// Extracts the raw coefficient (or multilinear evaluation) vector of a
    /// polynomial.
    ///
    /// A value that is already a coefficient vector is returned unchanged, since a
    /// `Uni` value is frequently never materialized as a polynomial at all. The
    /// canonical representation drops trailing zeros, so use
    /// [`Value::value_coef_typed`] when the declared width matters.
    ///
    /// # Panics
    /// Panics if this value is neither a polynomial nor a scalar/index vector, or if
    /// the polynomial is a virtual product with no flat coefficient form.
    pub fn value_coef(&self) -> Self {
        match self {
            Value::Poly(p) => {
                let coeffs = p.to_vec().or_else(|| p.to_coeffs()).expect(
                    "Can only get coefficients/evaluations from univariate or MLE polynomials",
                );
                Value::vec_scalar(coeffs)
            }
            // `Uni` values are often represented directly as coefficient vectors already.
            Value::VecScalar(v) => Value::VecScalar(v.clone()),
            Value::VecIndex(v) => {
                Value::vec_scalar(v.iter().map(|i| C::F::from_usize(*i)).collect())
            }
            _ => panic!("Expected poly or coefficient vector, found {}", self),
        }
    }

    /// Coefficient extraction at a *declared* type.
    ///
    /// `ATyp::Uni(m)` promises exactly `m + 1` coefficient slots, but the
    /// canonical Arkworks representation
    /// drops trailing zero coefficients, so a value of declared type
    /// `Uni(m)` may carry fewer. Zero-pad the raw extraction up to the
    /// declared width so the runtime value always matches the shape its
    /// type promises. Never truncate: a payload wider than the declared
    /// bound is a genuine bound violation, not something to hide.
    ///
    /// Non-`Uni` types keep the raw [`Value::value_coef`] behavior.
    pub fn value_coef_typed(&self, typ: &ATyp) -> Self {
        let coefs = self.value_coef();
        match typ {
            ATyp::Uni(m) => {
                let expected = typ.physical_len();
                let Value::VecScalar(mut v) = coefs else {
                    unreachable!("value_coef must return VecScalar")
                };
                assert!(
                    v.len() <= expected,
                    "value_coef_typed: actual univariate coefficient count {} exceeds declared Uni({}) bound of {}",
                    v.len(),
                    m,
                    expected
                );
                v.to_mut().resize(expected, C::F::zero());
                Value::VecScalar(v)
            }
            _ => coefs,
        }
    }

    /// Lifts a scalar or index vector into a univariate polynomial by reading it as
    /// a coefficient list.
    ///
    /// This is the explicit `poly([...])` coercion; the type system has no implicit
    /// vector-to-polynomial conversion.
    ///
    /// # Panics
    /// Panics if this value is not a scalar or index vector.
    pub fn value_poly(&self) -> Self {
        self.clone().value_poly_owned()
    }

    /// [`Self::value_poly`] consuming the vector: when this is its only owner,
    /// it becomes the coefficients without a copy.
    ///
    /// # Panics
    /// As [`Self::value_poly`].
    pub fn value_poly_owned(self) -> Self {
        match self {
            Value::VecScalar(v) => Value::poly(VirtualPolynomial::from_poly(
                PolyVariant::from_coeffs(v.into_vec()),
            )),
            Value::VecIndex(v) => {
                let coeffs = v.iter().map(|i| C::F::from_usize(*i)).collect();
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::from_coeffs(
                    coeffs,
                )))
            }
            // A polynomial, materialized as one table: what a protocol asks for when it
            // reuses the polynomial enough to pay for it (across sumcheck rounds, say).
            Value::Poly(p) => Value::poly(VirtualPolynomial::from_poly(
                p.normalize()
                    .expect("the type checker admits only polynomials of this encoding"),
            )),
            _ => panic!("Expected vec scalar, found {}", self),
        }
    }

    /// Lifts a scalar or index vector into a multilinear extension by reading it as
    /// the evaluation table over the Boolean hypercube.
    ///
    /// This is the explicit `mle([...])` coercion; the arity is `ilog2_ceil(len)`.
    ///
    /// # Panics
    /// Panics if this value is not a scalar or index vector. A length that is not a
    /// power of two yields a truncated arity rather than an error, so the
    /// power-of-two check belongs to the `Op::Mle` typing rule.
    pub fn value_mle(&self) -> Self {
        match self {
            Value::VecScalar(v) => {
                let mle = v.to_vec();
                let size = ilog2_ceil(mle.len()) as usize;
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMle::new(size, mle),
                )))
            }
            Value::VecIndex(v) => {
                let mut mle = Vec::with_capacity(v.len());
                mle.extend(v.iter().map(|i| C::F::from_usize(*i)));
                let size = ilog2_ceil(mle.len()) as usize;
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMle::new(size, mle),
                )))
            }
            // A polynomial, materialized as one table: what a protocol asks for when it
            // reuses the polynomial enough to pay for it (across sumcheck rounds, say).
            Value::Poly(p) => Value::poly(VirtualPolynomial::from_poly(
                p.normalize()
                    .expect("the type checker admits only polynomials of this encoding"),
            )),
            _ => panic!("Expected vec scalar or vec index, found {}", self),
        }
    }

    /// Consuming variant of [`Value::value_mle`]: for the vector-typed
    /// variants (`VecScalar`/`VecIndex`), moves the underlying `Vec<F>`
    /// into the resulting `DenseMle` rather than cloning it. Other
    /// variants fall through to the borrowing `value_mle()` path.
    ///
    /// Used by the runtime's `Op::Mle` arm to skip a clone when the
    /// `Arc<Value>` is unique (via `Arc::unwrap_or_clone`).
    pub fn value_mle_owned(self) -> Self {
        match self {
            Value::VecScalar(v) => {
                let size = ilog2_ceil(v.len()) as usize;
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMle::new(size, v.into_vec()),
                )))
            }
            Value::VecIndex(v) => {
                let mut mle = Vec::with_capacity(v.len());
                mle.extend(v.iter().map(|i| C::F::from_usize(*i)));
                let size = ilog2_ceil(mle.len()) as usize;
                Value::poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                    DenseMle::new(size, mle),
                )))
            }
            other => other.value_mle(),
        }
    }

    /// Interpolates the univariate polynomial through the evaluations held in
    /// `self`.
    ///
    /// With no `points` the evaluations are assumed to lie on the FFT evaluation
    /// domain and an inverse FFT is used. With explicit `points` the domain is
    /// checked first: FFT-domain points still take the inverse FFT path, while
    /// arbitrary points fall back to general interpolation.
    ///
    /// # Errors
    /// [`DivisionByZero`] if two of the `points` are equal.
    ///
    /// # Panics
    /// Panics if the evaluations are empty, if `points` and evaluations have
    /// different lengths, or if either operand is not a scalar/index vector.
    pub fn value_interpolate(&self, points: Option<&Self>) -> Result<Self, DivisionByZero> {
        self.clone().value_interpolate_owned(points)
    }

    /// [`Self::value_interpolate`] consuming the evaluations: when this is
    /// their only owner, they become the coefficients in place.
    ///
    /// # Errors
    /// As [`Self::value_interpolate`].
    ///
    /// # Panics
    /// As [`Self::value_interpolate`].
    pub fn value_interpolate_owned(self, points: Option<&Self>) -> Result<Self, DivisionByZero> {
        let evals = value_into_scalar_vec::<C>(self);
        assert!(
            !evals.is_empty(),
            "interpolate expects non-empty evaluations"
        );

        match points {
            None => {
                let mut coeffs = evals;
                C::F::ifft(&mut coeffs);
                Ok(Value::poly(VirtualPolynomial::from_poly(
                    PolyVariant::DenseUni(DenseUni::new(coeffs)),
                )))
            }
            Some(points) => {
                let xs = value_scalars::<C>(points);
                assert_eq!(
                    xs.len(),
                    evals.len(),
                    "interpolate expects points and evaluations with same length"
                );

                if are_fft_domain_points::<C>(&xs) {
                    let mut coeffs = evals;
                    C::F::ifft(&mut coeffs);
                    return Ok(Value::poly(VirtualPolynomial::from_poly(
                        PolyVariant::DenseUni(DenseUni::new(coeffs)),
                    )));
                }

                let coeffs = crate::poly::virtual_polynomial::interpolate_univariate_from_points(
                    &xs, &evals,
                )?;
                Ok(Value::poly(VirtualPolynomial::from_poly(
                    PolyVariant::DenseUni(DenseUni::new(coeffs)),
                )))
            }
        }
    }

    /// Evaluates a polynomial of declared type `typ` over the FFT domain,
    /// returning the evaluation vector.
    ///
    /// A multilinear polynomial already stores its hypercube evaluations, so that
    /// case is a direct read; a univariate polynomial is transformed from
    /// coefficients by a forward FFT, over the `m + 1` coefficients its type
    /// `Uni(m)` promises: storage drops trailing zero coefficients, which would
    /// otherwise shrink the domain.
    ///
    /// # Panics
    /// Panics if this value is not a polynomial, if the virtual polynomial cannot be
    /// normalized to a concrete representation, if it has no coefficient form, or if
    /// it has more coefficients than `typ` allows.
    pub fn value_fft(&self, typ: &ATyp) -> Self {
        let Value::Poly(p) = self else {
            panic!("Expected polynomial value, found {}", self)
        };
        let poly = p
            .normalize()
            .expect("Failed to normalize polynomial for fft");
        if let PolyVariant::DenseMle(mle) = poly {
            return Value::vec_scalar(mle.into_evals());
        }
        let mut coeffs = poly
            .to_coeffs()
            .expect("Can only fft univariate polynomial or mle");
        if let ATyp::Uni(m) = typ {
            assert!(
                coeffs.len() <= m + 1,
                "value_fft: {} coefficients exceed the declared Uni({m})",
                coeffs.len()
            );
            coeffs.resize(m + 1, C::F::zero());
        }
        C::F::fft(&mut coeffs);
        Value::vec_scalar(coeffs)
    }
}
