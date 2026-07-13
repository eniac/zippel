#![allow(refining_impl_trait)]

mod error;
#[cfg(test)]
mod tests;

pub use error::TypeError;

use crate::ast::sig::CSig;
use crate::ast::{BinOp, CBody, CExp};
use crate::id::{Tid, Vid};
use crate::typ::lub::{Lub, LubError};
use crate::typ::range::Range;
use crate::typ::{CKind, CTyp, CTyps};
use share::{Ctx, Set};

pub trait Typeable {
    type Context;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError>;
}

/// Type inference for [CExp]
impl Typeable for CExp {
    type Context = Ctx<Vid, CTyp>;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError> {
        match self {
            // Infer the type of a literal [n] as a Fin<n> type
            CExp::Lit(n) => Ok(CTyp::fin(Range::singleton(*n))),

            // Unit value
            CExp::Unit => Ok(CTyp::Unit),

            // Unary: FFT-grid interpolation; binary: explicit points + evaluations
            CExp::Interpolate(points_opt, box evals) => {
                let evals_typ = evals
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match points_opt {
                    None => match evals_typ {
                        CTyp::Vec(box b, n) => {
                            let i = b
                                .to_scalar(kctx)
                                .ok_or(TypeError::interpolate_unary(kctx, vctx, self))?;
                            if !n.is_power_of_two() {
                                return Err(TypeError::interpolate_unary_not_pow2(
                                    kctx, vctx, self, n,
                                ));
                            }
                            // n evaluations on the n-th roots of unity uniquely
                            // determine a polynomial of max degree n-1
                            // (n coefficients under the m+1 convention).
                            // Pow2 check above rules out n == 0, so n >= 1.
                            let deg = n
                                .checked_sub(1)
                                .ok_or_else(|| TypeError::interpolate_unary(kctx, vctx, self))?;
                            Ok(CTyp::Poly(i, 1, deg))
                        }
                        _ => Err(TypeError::interpolate_unary(kctx, vctx, self)),
                    },
                    Some(points) => {
                        let points_typ = points
                            .infer(kctx, fctx, vctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        match (points_typ, evals_typ) {
                            (CTyp::Vec(box bp, np), CTyp::Vec(box be, ne)) if np == ne => {
                                if ne == 0 {
                                    return Err(TypeError::interpolate(kctx, vctx, self));
                                }
                                let ip = bp
                                    .to_scalar(kctx)
                                    .ok_or(TypeError::interpolate(kctx, vctx, self))?;
                                let ie = be
                                    .to_scalar(kctx)
                                    .ok_or(TypeError::interpolate(kctx, vctx, self))?;
                                if ip != ie {
                                    return Err(TypeError::interpolate(kctx, vctx, self));
                                }
                                // Lagrange interpolation at ne distinct points
                                // yields a polynomial of max degree ne-1
                                // (ne coefficients under the m+1 convention).
                                // np == ne and ne >= 1 since vector typing
                                // rejects empty literals upstream.
                                let deg = ne
                                    .checked_sub(1)
                                    .ok_or_else(|| TypeError::interpolate(kctx, vctx, self))?;
                                Ok(CTyp::Poly(ie, 1, deg))
                            }
                            _ => Err(TypeError::interpolate(kctx, vctx, self)),
                        }
                    }
                }
            }

            // `poly(v: [F; k])` with `k >= 1` yields `Poly<F, 1, k - 1>`
            // (degree convention: `m = k - 1`).
            CExp::Poly(box v) => {
                let typ = v
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match typ {
                    CTyp::Vec(box b, k) => {
                        if k == 0 {
                            return Err(TypeError::poly(kctx, vctx, self));
                        }
                        let i = b.to_scalar(kctx).ok_or(TypeError::poly(kctx, vctx, self))?;
                        let deg = k
                            .checked_sub(1)
                            .ok_or_else(|| TypeError::poly(kctx, vctx, self))?;
                        Ok(CTyp::Poly(i, 1, deg))
                    }
                    _ => Err(TypeError::poly(kctx, vctx, self)),
                }
            }

            // `coef(p: Poly<F, 1, m>)` yields `[F; m + 1]` (coefficient count
            // is degree + 1 under the Phase 14 degree convention).
            CExp::Coef(box p) => {
                let typ = p
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match typ {
                    CTyp::Poly(tid, 1, m) => {
                        let k = kctx.get(&tid).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(&tid),
                        ))?;
                        // Only field elements can be evaluated
                        if k.is_scalar() {
                            let len = m
                                .checked_add(1)
                                .ok_or_else(|| TypeError::coef(kctx, vctx, self))?;
                            Ok(CTyp::vec(&CTyp::Base(tid), len))
                        } else {
                            Err(TypeError::coef(kctx, vctx, self))
                        }
                    }
                    CTyp::Poly(tid, n, 1) if n > 1 => {
                        let k = kctx.get(&tid).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(&tid),
                        ))?;
                        if k.is_scalar() {
                            if let Some(len) = 1_usize.checked_shl(n as u32) {
                                Ok(CTyp::vec(&CTyp::Base(tid), len))
                            } else {
                                Err(TypeError::coef(kctx, vctx, self))
                            }
                        } else {
                            Err(TypeError::coef(kctx, vctx, self))
                        }
                    }
                    _ => Err(TypeError::coef(kctx, vctx, self)),
                }
            }

            CExp::Evaluate(box p, selector, opt_points) => {
                let p_typ = p
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match (selector, opt_points) {
                    // Unary form: eval(p) — evaluation on the FFT grid (n roots of unity).
                    (None, None) => {
                        let t = p_typ;
                        match t.clone() {
                            CTyp::Poly(tid, 1, n) => {
                                let k = kctx.get(&tid).ok_or(TypeError::lub(
                                    TypeError::exp(kctx, vctx, self),
                                    LubError::kind_not_found(&tid),
                                ))?;
                                if !k.is_scalar() {
                                    return Err(TypeError::evaluate_grid(kctx, vctx, p, &t));
                                }
                                // Phase 14 m+1 convention: Poly<F, 1, n> has n+1
                                // coefficients. The runtime FFT requires the
                                // coefficient count to be a power of two
                                // (`GeneralEvaluationDomain::new(n+1)` else pads).
                                // Check the coefficient count, not the max-degree.
                                let coef_count = n
                                    .checked_add(1)
                                    .ok_or_else(|| TypeError::evaluate_grid(kctx, vctx, p, &t))?;
                                if !coef_count.is_power_of_two() {
                                    return Err(TypeError::evaluate_grid_not_pow2(
                                        kctx, vctx, p, n, &t,
                                    ));
                                }
                                Ok(CTyp::vec(&CTyp::Base(tid), coef_count))
                            }
                            _ => Err(TypeError::evaluate_grid(kctx, vctx, p, &t)),
                        }
                    }
                    // Binary form: eval(p, points) — point or vector evaluation.
                    (None, Some(box x)) => {
                        let x_typ = x
                            .infer(kctx, fctx, vctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        match (p_typ, x_typ) {
                            // Univariate polynomial evaluated at a single scalar point.
                            // Result is a scalar of the same base type. (The
                            // pre-Phase-B path desugared `p(x)` into
                            // `dot(p, [x^0, ..., x^n])`, which routed through
                            // `lub_dot(Poly, Vec)` — that arm has been
                            // removed, and the App desugaring now produces
                            // `evaluate(p, x)` directly.)
                            (CTyp::Poly(i, 1, _n), CTyp::Base(b)) if i == b => {
                                let k =
                                    kctx.get(&i).ok_or(TypeError::evaluate(kctx, vctx, p, x))?;
                                if !k.is_scalar() {
                                    return Err(TypeError::evaluate(kctx, vctx, p, x));
                                }
                                Ok(CTyp::Base(i))
                            }
                            // Univariate polynomial evaluated at a vector of points is a
                            // hard type error: evaluate at a single scalar via `p(x)`, or
                            // write `[p(x) for x in points]` to evaluate at many points.
                            (CTyp::Poly(_i, 1, _n), CTyp::Vec(_b, _len)) => {
                                Err(TypeError::evaluate_univariate_vector(kctx, vctx, p, x))
                            }
                            // Multivariate polynomial (MLE, virtual, etc.): n > 1.
                            (CTyp::Poly(i_poly, n, d), CTyp::Vec(b, len_vec)) if n > 1 => {
                                // Scalar-castable points evaluate the MLE generically.
                                if b.to_scalar(kctx).as_ref() != Some(&i_poly) {
                                    return Err(TypeError::evaluate(kctx, vctx, p, x));
                                }
                                if len_vec == n {
                                    return Ok(CTyp::Base(i_poly.clone()));
                                }
                                if len_vec < n {
                                    let rem = n
                                        .checked_sub(len_vec)
                                        .ok_or_else(|| TypeError::evaluate(kctx, vctx, p, x))?;
                                    return Ok(CTyp::Poly(i_poly.clone(), rem, d));
                                }
                                Err(TypeError::evaluate_mle_too_many_arguments(kctx, vctx, p, x))
                            }
                            _ => Err(TypeError::evaluate(kctx, vctx, p, x)),
                        }
                    }
                    // Selected form: eval<range>(p, fixed).
                    (Some(range), Some(box fixed)) => {
                        let fixed_typ = fixed
                            .infer(kctx, fctx, vctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        let fail = || TypeError::evaluate_selected(kctx, vctx, p, fixed, *range);
                        if range.step != 1 || range.start >= range.end {
                            return Err(fail());
                        }

                        match (p_typ, fixed_typ) {
                            (CTyp::Poly(poly_tid, n, d), CTyp::Vec(box fixed_elem, fixed_len)) => {
                                let fixed_tid = fixed_elem.to_scalar(kctx).ok_or_else(fail)?;
                                let range_len = range.len();
                                if fixed_tid != poly_tid
                                    || range.end > n
                                    || fixed_len != n.checked_sub(range_len).ok_or_else(fail)?
                                {
                                    return Err(fail());
                                }
                                Ok(CTyp::Poly(poly_tid, range_len, d))
                            }
                            _ => Err(fail()),
                        }
                    }
                    // Parser conversion rejects this mode for source programs.
                    // Keep inference defensive in case an internal caller builds
                    // the impossible shape directly.
                    (Some(range), None) => Err(TypeError::evaluate_selector_without_points(
                        kctx, vctx, p, *range,
                    )),
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CExp::Mle(box v) => {
                // It must be a vector of fields, or a vector of Fin
                let typ = v
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match typ {
                    CTyp::Vec(box b, n) => {
                        if n == 0 || !n.is_power_of_two() {
                            return Err(TypeError::mle(kctx, vctx, self));
                        }
                        let n_pow = n.ilog2() as usize;
                        let i = b.to_scalar(kctx).ok_or(TypeError::mle(kctx, vctx, self))?;
                        Ok(CTyp::Poly(i, n_pow, 1))
                    }
                    _ => Err(TypeError::mle(kctx, vctx, self)),
                }
            }

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CExp::Vec(v) => {
                let ts: CTyps = v
                    .iter()
                    .map(|aexp| aexp.infer(kctx, fctx, vctx))
                    .collect::<Result<_, _>>()
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Vectors cannot be empty for type inference to work
                if ts.is_empty() {
                    return Err(TypeError::vec_empty(kctx, vctx));
                }

                // For reference, the type of the first element
                let mut t = ts.0[0].clone();

                // Unify types of all elements in the vector to [t]
                for tx in ts.0[1..].iter() {
                    t = CTyp::lub_equ(&t, tx, kctx)
                        .map_err(|e| TypeError::vec(kctx, vctx, tx, &t, e.into()))?;
                }

                // Vector length
                let n = ts.len();

                // Generalize the type of the parameters
                Ok(CTyp::vec(&t, n))
            }

            CExp::Pair(box t, box e) => {
                let ta = t
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = e
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_pair(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle +
            CExp::Bin(BinOp::Add, box a, box b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_add(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle -
            CExp::Bin(BinOp::Sub, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_sub(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle *
            CExp::Bin(BinOp::Mul, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_mul(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle /
            CExp::Bin(BinOp::Div, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_div(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle ^
            CExp::Bin(BinOp::Pow, box a, box b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_pow(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle .
            CExp::Bin(BinOp::Dot, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_dot(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle %
            CExp::Bin(BinOp::Rem, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_rem(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }
            // Handle ++
            CExp::Bin(BinOp::Concat, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_concat(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Range expression
            CExp::Range(r) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start, r.step, r.end)
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(&CTyp::Fin(rr), rr.len()))
            }

            // Map comprehension
            CExp::Map(box x, id, box r) => {
                // Type infer the range expression
                let tr = r
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match tr {
                    CTyp::Vec(box inner, n) if n > 0 => {
                        // Clone the context
                        let mut innerctx = vctx.clone();

                        // Add variable [id] to the context with type [inner]
                        innerctx.insert(id, &inner);

                        // Type infer the expression [x] with the new context
                        let tx = x
                            .infer(kctx, fctx, &innerctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        Ok(CTyp::vec(&tx, n))
                    }
                    _ => Err(TypeError::exp(kctx, vctx, self)),
                }
            }

            CExp::Reduce(op, box v) => {
                let tv = v
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match tv {
                    CTyp::Vec(box elem, n) if n > 0 => {
                        // Multiplying a vector of polynomials multiplies all factors, so
                        // the resulting degree is the element degree times vector length.
                        if *op == BinOp::Mul {
                            if let CTyp::Poly(_, _, d) = &elem {
                                // Validate the pairwise multiplication under the kind context first.
                                let res_t = CTyp::lub_op(*op, &elem, &elem, kctx).map_err(|e| {
                                    TypeError::lub(TypeError::exp(kctx, vctx, self), e)
                                })?;
                                if let CTyp::Poly(res_a, num_vars, _) = res_t {
                                    let degree = d.checked_mul(n).ok_or_else(|| {
                                        TypeError::lub(
                                            TypeError::exp(kctx, vctx, self),
                                            LubError::DegreeOverflow(*d, n),
                                        )
                                    })?;
                                    return Ok(CTyp::Poly(res_a, num_vars, degree));
                                }
                            }
                        }

                        let result = CTyp::lub_op(*op, &elem, &elem, kctx)
                            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                        if result == elem {
                            Ok(elem.clone())
                        } else {
                            Err(TypeError::next(
                                TypeError::exp(kctx, vctx, self),
                                TypeError::ReduceAcc(
                                    kctx.clone(),
                                    vctx.clone(),
                                    *op,
                                    self.clone(),
                                    elem.clone(),
                                    result,
                                ),
                            ))
                        }
                    }
                    _ => Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::reduce(kctx, vctx, *op, v, &tv),
                    )),
                }
            }
            // Variable context lookup
            CExp::Var(id) => vctx
                .get(id)
                .cloned()
                .ok_or(TypeError::var_not_found(id, vctx)),

            // Random oracle challenge
            CExp::Challenge(t, _) | CExp::Random(t, _) => {
                // What kind of [t]?
                let k = kctx.get(t).ok_or(TypeError::lub(
                    TypeError::exp(kctx, vctx, self),
                    LubError::kind_not_found(t),
                ))?;

                if !k.is_scalar() {
                    return Err(TypeError::challenge(kctx, vctx, t, k));
                }

                Ok(CTyp::base(t))
            }

            // Random access into vectors
            CExp::Ram(a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Must be a vector and a Fin type (random access/slice)
                match (ta.clone(), tb.clone()) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(r)) => {
                        if r.end <= n {
                            Ok(typ)
                        } else {
                            Err(TypeError::ram(kctx, vctx, a, ta, b, tb))
                        }
                    }
                    (CTyp::Vec(box typ, n), CTyp::Vec(box CTyp::Fin(r), m)) => {
                        if r.end <= n {
                            Ok(CTyp::vec(&typ, m))
                        } else {
                            Err(TypeError::ram(kctx, vctx, a, ta, b, tb))
                        }
                    }
                    (_, _) => Err(TypeError::ram(kctx, vctx, a, ta, b, tb)),
                }
            }

            // Function or polynomial application
            CExp::App(id, params) => {
                // type inference for each parameter
                let param_types: CTyps = params
                    .iter()
                    .map(|p| p.infer(kctx, fctx, vctx))
                    .collect::<Result<_, _>>()
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Is it a polynomial, MLE, or a function?
                match vctx.get(id) {
                    Some(CTyp::Poly(tbase, 1, _)) => {
                        // It is a univariate polynomial
                        let k = kctx.get(tbase).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(tbase),
                        ))?;

                        // Only field elements can be evaluated and only 1 argument can be given
                        if !k.is_scalar() || param_types.len() != 1 {
                            return Err(TypeError::uni(kctx, vctx, id, params, &param_types));
                        }

                        // The argument must be a field and the same as the polynomial
                        if let Some(tb) = param_types.0[0].clone().to_scalar(kctx) {
                            if &tb == tbase {
                                // The polynomial is a field
                                Ok(CTyp::base(tbase))
                            } else {
                                Err(TypeError::uni(kctx, vctx, id, params, &param_types))
                            }
                        } else {
                            Err(TypeError::uni(kctx, vctx, id, params, &param_types))
                        }
                    }
                    Some(CTyp::Poly(tbase, n, 1)) => {
                        // It is a multilinear extension
                        let k = kctx.get(tbase).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(tbase),
                        ))?;
                        // Only field elements can be evaluated and only 1 argument can be given
                        if !k.is_scalar() || param_types.len() != 1 {
                            return Err(TypeError::mle_app(kctx, vctx, id, params, &param_types));
                        }

                        // The argument must be a field and the same as the MLE
                        match param_types.0[0].clone() {
                            CTyp::Fin(_r) if *n > 0 => {
                                let rem = n.checked_sub(1).ok_or_else(|| {
                                    TypeError::mle_app(kctx, vctx, id, params, &param_types)
                                })?;
                                Ok(CTyp::mle(tbase, rem))
                            }
                            CTyp::Base(tb) if &tb == tbase && *n > 0 => {
                                let rem = n.checked_sub(1).ok_or_else(|| {
                                    TypeError::mle_app(kctx, vctx, id, params, &param_types)
                                })?;
                                Ok(CTyp::mle(tbase, rem))
                            }
                            CTyp::Vec(box CTyp::Base(tb), m) if &tb == tbase && *n == m => {
                                Ok(CTyp::base(tbase))
                            }
                            CTyp::Vec(box CTyp::Fin(_), m) if *n == m => Ok(CTyp::base(tbase)),
                            CTyp::Vec(box CTyp::Fin(_), m) if *n > m => {
                                let rem = n.checked_sub(m).ok_or_else(|| {
                                    TypeError::mle_app(kctx, vctx, id, params, &param_types)
                                })?;
                                Ok(CTyp::mle(tbase, rem))
                            }
                            CTyp::Vec(box CTyp::Base(tb), m) if &tb == tbase && *n > m => {
                                let rem = n.checked_sub(m).ok_or_else(|| {
                                    TypeError::mle_app(kctx, vctx, id, params, &param_types)
                                })?;
                                Ok(CTyp::mle(tbase, rem))
                            }
                            _ => Err(TypeError::mle_app(kctx, vctx, id, params, &param_types)),
                        }
                    }
                    _ => {
                        // It is a function
                        // Find all matching functions in function context [fctx]
                        let mut matching_sigs: Vec<_> = fctx
                            .iter()
                            .filter_map(|sig| {
                                if &sig.name != id {
                                    return None;
                                }
                                let (vs, _) = sig.clone().unify(&param_types, kctx).ok()?;
                                Some(vs)
                            })
                            .collect();
                        // [CTyp::unify] uses max() on univariate degree so many overloads
                        // Poly<F,1,d> all unify with Poly<F,1,1>. When ambiguous, keep only
                        // signatures whose parameters match argument types exactly (no widening).
                        if matching_sigs.len() > 1 {
                            matching_sigs.retain(|vs| {
                                vs.args
                                    .iter()
                                    .zip(param_types.0.iter())
                                    .all(|(a, t)| a.typ == *t)
                            });
                        }

                        // Only one function shoud match
                        if matching_sigs.len() != 1 {
                            Err(TypeError::next(
                                TypeError::exp(kctx, vctx, self),
                                TypeError::app_multiple(fctx, id, param_types),
                            ))
                        } else {
                            let sig = &matching_sigs[0];
                            Ok(sig.ret.clone())
                        }
                    }
                }
            }

            CExp::Assert(box lhs, box rhs, box cont) | CExp::Verify(box lhs, box rhs, box cont) => {
                let ta = lhs
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = rhs
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Constraint operands must have compatible types
                CTyp::lub_equ(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;

                // The continuation determines the type of the expression
                cont.infer(kctx, fctx, vctx)
            }

            CExp::Let(Some(var), box left, box right) | CExp::Log(var, box left, box right) => {
                let tleft = left.infer(kctx, fctx, vctx)?;
                let mut vctx = vctx.clone();
                vctx.insert(var, &tleft);
                let tright = right.infer(kctx, fctx, &vctx)?;
                Ok(tright)
            }
            CExp::Let(None, box left, box right) => {
                left.infer(kctx, fctx, vctx)?;
                right.infer(kctx, fctx, vctx)
            }

            CExp::Fun(vars, box body) => {
                // Create a new variable context with the parameters
                let mut new_vctx = vctx.clone();

                // Find a field type
                let field_tid = kctx
                    .iter()
                    .find(|(_, k)| k.is_scalar())
                    .map(|(tid, _)| tid.clone())
                    .ok_or(TypeError::exp(kctx, vctx, self))?;

                if vars.len() == 1 {
                    // Univariate polynomial - type the variable as Poly(F, 1, 1) (degree-1 polynomial)
                    // Then type inference will compute the actual degree through lub operations
                    for var in vars {
                        new_vctx.insert(var, &CTyp::Poly(field_tid.clone(), 1, 1));
                    }

                    // Infer the type of the body - should get Poly(F, 1, N) where N is the degree
                    let body_type = body.infer(kctx, fctx, &new_vctx)?;

                    // Extract the degree from the inferred type
                    match body_type {
                        CTyp::Poly(tid, 1, degree) => Ok(CTyp::Poly(tid, 1, degree)),
                        CTyp::Base(tid) => Ok(CTyp::Poly(tid, 1, 0)), // Constant polynomial
                        _ => Err(TypeError::exp(kctx, vctx, self)),
                    }
                } else {
                    // Multilinear polynomial - type variables as scalars and validate structure
                    for var in vars {
                        new_vctx.insert(var, &CTyp::Base(field_tid.clone()));
                    }

                    let body_type = body.infer(kctx, fctx, &new_vctx)?;

                    match body_type {
                        CTyp::Base(tid)
                            if kctx.get(&tid).map(|k| k.is_scalar()).unwrap_or(false) =>
                        {
                            // For multilinear, we just return Mle with the number of variables
                            // Backend validation will catch if it's not actually multilinear
                            Ok(CTyp::mle(&tid, vars.len()))
                        }
                        _ => Err(TypeError::exp(kctx, vctx, self)),
                    }
                }
            }

            CExp::Record(fields) => {
                let mut field_types = Ctx::new();

                // Infer the type of each field
                for (field_name, field_exp) in fields.iter() {
                    let field_typ = field_exp
                        .infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                    field_types.insert(field_name, &field_typ);
                }

                Ok(CTyp::Record(field_types))
            }

            CExp::Proj(box record_exp, field_name) => {
                // Infer the type of the record expression
                let record_typ = record_exp
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match record_typ {
                    CTyp::Record(fields) => {
                        // Look up the field in the record type
                        fields.get(field_name).cloned().ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, vctx, self),
                                TypeError::field_not_found(
                                    kctx, vctx, record_exp, field_name, &fields,
                                ),
                            )
                        })
                    }
                    _ => Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::not_a_record(kctx, vctx, record_exp, &record_typ),
                    )),
                }
            }

            CExp::SetRecord(box record_exp, field_name, box value_exp) => {
                // Infer the type of the record expression (must be a record)
                let record_typ = record_exp
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let CTyp::Record(fields) = &record_typ else {
                    return Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::not_a_record(kctx, vctx, record_exp, &record_typ),
                    ));
                };
                // Check the field exists and the value has a type compatible with the field (e.g. Fin unifies with F)
                let field_typ = fields.get(field_name).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::field_not_found(kctx, vctx, record_exp, field_name, fields),
                    )
                })?;
                let value_typ = value_exp
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let _ = CTyp::lub_equ(&value_typ, field_typ, kctx).map_err(|e| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::lub(TypeError::exp(kctx, vctx, self), e),
                    )
                })?;
                // Result type is the same record type
                Ok(record_typ.clone())
            }
        }
    }
}

/// Type inference for [CBody]
impl Typeable for CBody {
    type Context = Ctx<Vid, CTyp>;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError> {
        // Type inference for each statement in the Body
        match self {
            CBody::Proto { relation, body } => {
                // Infer the relation (Let/Assert chain — infers to Unit)
                relation.infer(kctx, fctx, &vctx.clone())?;

                // Then the body
                let tbody = body.infer(kctx, fctx, &vctx.clone())?;

                if tbody != CTyp::Unit {
                    Err(TypeError::unit(kctx, vctx, body))
                } else {
                    Ok(CTyp::Unit)
                }
            }
            CBody::Func { body } => body.infer(kctx, fctx, &vctx.clone()),
            CBody::TypeAlias => Ok(CTyp::Unit), // Type aliases have no body to check
        }
    }
}
