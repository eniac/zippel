//! Polynomial constructors and evaluation: `interpolate`, `poly`, `coef`, `eval`, `mle`, `fun`.

use super::*;
use crate::ast::range::CRange;

impl CRef<'_> {
    pub(super) fn infer_interpolate(
        self,
        points_opt: Option<CRef<'_>>,
        evals: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let evals_typ = env.typ(evals);

        match points_opt {
            None => match evals_typ {
                CTyp::Vec(b, n) => {
                    let i = b.to_scalar(kctx).ok_or(TypeError::InterpolateUnary)?;
                    if !n.is_power_of_two() {
                        return Err(TypeError::InterpolateUnaryNotPow2(n.node));
                    }
                    // n evaluations on the n-th roots of unity uniquely
                    // determine a polynomial of max degree n-1
                    // (n coefficients under the m+1 convention).
                    // Pow2 check above rules out n == 0, so n >= 1.
                    let deg = n.node - 1;
                    Ok(CTyp::uni(&i, deg))
                }
                _ => Err(TypeError::InterpolateUnary),
            },
            Some(points) => {
                let points_typ = env.typ(points);

                match (points_typ, evals_typ) {
                    (CTyp::Vec(bp, np), CTyp::Vec(be, ne)) if np == ne => {
                        if ne.node == 0 {
                            return Err(TypeError::Interpolate);
                        }
                        // A side typed by a scalar field pins the field; otherwise
                        // integer points/evaluations need a unique scalar in scope.
                        let named = |t: &CTyp| match t {
                            CTyp::Base(b) if kctx.get(b).is_some_and(CKind::is_scalar) => {
                                Some(b.clone())
                            }
                            _ => None,
                        };
                        let ie = named(&be.node)
                            .or_else(|| named(&bp.node))
                            .or_else(|| be.to_scalar(kctx))
                            .ok_or(TypeError::Interpolate)?;
                        let field = CTyp::Base(ie.clone());
                        if !bp.node.fits(&field, kctx) || !be.node.fits(&field, kctx) {
                            return Err(TypeError::Interpolate);
                        }
                        // Lagrange interpolation at ne distinct points
                        // yields a polynomial of max degree ne-1
                        // (ne coefficients under the m+1 convention).
                        // np == ne and ne >= 1 since vector typing
                        // rejects empty literals upstream.
                        let deg = ne.node - 1;
                        Ok(CTyp::uni(&ie, deg))
                    }
                    _ => Err(TypeError::Interpolate),
                }
            }
        }
    }

    pub(super) fn infer_poly(self, v: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let typ = env.typ(v);

        match typ {
            CTyp::Vec(b, k) => {
                if k.node == 0 {
                    return Err(TypeError::Poly);
                }
                let i = b.to_scalar(kctx).ok_or(TypeError::Poly)?;
                let deg = k.node - 1;
                Ok(CTyp::uni(&i, deg))
            }
            _ => Err(TypeError::Poly),
        }
    }

    pub(super) fn infer_coef(self, p: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let typ = env.typ(p);

        match typ {
            CTyp::Poly(tid, m_vars, m) if m_vars.node == 1 => {
                let k = kctx
                    .get(&tid)
                    .ok_or(TypeError::from(LubError::kind_not_found(&tid)))?;
                // Only field elements can be evaluated
                if k.is_scalar() {
                    let len = m.checked_add(1).ok_or_else(|| TypeError::Coef)?;
                    Ok(CTyp::vec(&CTyp::Base(tid), len))
                } else {
                    Err(TypeError::Coef)
                }
            }
            CTyp::Poly(tid, n, d) if n.node > 1 && d.node == 1 => {
                let k = kctx
                    .get(&tid)
                    .ok_or(TypeError::from(LubError::kind_not_found(&tid)))?;
                if k.is_scalar() {
                    if let Some(len) = 1_usize.checked_shl(n.node as u32) {
                        Ok(CTyp::vec(&CTyp::Base(tid), len))
                    } else {
                        Err(TypeError::Coef)
                    }
                } else {
                    Err(TypeError::Coef)
                }
            }
            _ => Err(TypeError::Coef),
        }
    }

    pub(super) fn infer_evaluate(
        self,
        p: CRef<'_>,
        selector: Option<&CRange>,
        opt_points: Option<CRef<'_>>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let p_typ = env.typ(p);

        match (selector, opt_points) {
            // Unary form: eval(p) — evaluation on the FFT grid (n roots of unity).
            (None, None) => {
                let t = p_typ;
                match t.clone() {
                    CTyp::Poly(tid, m_vars, n) if m_vars.node == 1 => {
                        let k = kctx
                            .get(&tid)
                            .ok_or(TypeError::from(LubError::kind_not_found(&tid)))?;
                        if !k.is_scalar() {
                            return Err(TypeError::EvaluateGrid(kctx.clone(), t.clone()));
                        }
                        // Phase 14 m+1 convention: Poly<F, 1, n> has n+1
                        // coefficients. The runtime FFT requires the
                        // coefficient count to be a power of two
                        // (`GeneralEvaluationDomain::new(n+1)` else pads).
                        // Check the coefficient count, not the max-degree.
                        let coef_count = n
                            .checked_add(1)
                            .ok_or_else(|| TypeError::EvaluateGrid(kctx.clone(), t.clone()))?;
                        if !coef_count.is_power_of_two() {
                            return Err(TypeError::EvaluateGridNotPow2(n.node));
                        }
                        Ok(CTyp::vec(&CTyp::Base(tid), coef_count))
                    }
                    _ => Err(TypeError::EvaluateGrid(kctx.clone(), t.clone())),
                }
            }
            // Binary form: eval(p, points) — point or vector evaluation.
            (None, Some(x)) => {
                let x_typ = env.typ(x);

                match (p_typ, x_typ) {
                    // Univariate polynomial evaluated at a single scalar point.
                    // Result is a scalar of the same base type. (The
                    // pre-Phase-B path desugared `p(x)` into
                    // `dot(p, [x^0, ..., x^n])`, which routed through
                    // `lub_dot(Poly, Vec)` — that arm has been
                    // removed, and the App desugaring now produces
                    // `evaluate(p, x)` directly.)
                    (CTyp::Poly(i, m, _n), CTyp::Base(b)) if m.node == 1 && i == b => {
                        let k = kctx.get(&i).ok_or(TypeError::Evaluate)?;
                        if !k.is_scalar() {
                            return Err(TypeError::Evaluate);
                        }
                        Ok(CTyp::Base(i))
                    }
                    // An integer point embeds into the polynomial's own field.
                    (CTyp::Poly(i, m, _n), CTyp::Fin(_) | CTyp::FieldLiteral) if m.node == 1 => {
                        let k = kctx.get(&i).ok_or(TypeError::Evaluate)?;
                        if !k.is_scalar() {
                            return Err(TypeError::Evaluate);
                        }
                        Ok(CTyp::Base(i))
                    }
                    // Univariate polynomial evaluated at a vector of points is a
                    // hard type error: evaluate at a single scalar via `p(x)`, or
                    // write `[p(x) for x in points]` to evaluate at many points.
                    (CTyp::Poly(_i, m, _n), CTyp::Vec(_b, _len)) if m.node == 1 => {
                        Err(TypeError::EvaluateUnivariateVector)
                    }
                    // Multivariate polynomial (MLE, virtual, etc.): n > 1.
                    (CTyp::Poly(i_poly, n, d), CTyp::Vec(b, len_vec)) if n.node > 1 => {
                        // Points must fit the polynomial's field (integers embed).
                        if !b.node.fits(&CTyp::Base(i_poly.clone()), kctx) {
                            return Err(TypeError::Evaluate);
                        }
                        if len_vec == n {
                            return Ok(CTyp::Base(i_poly.clone()));
                        }
                        if len_vec < n {
                            let rem = n.node - len_vec.node;
                            return Ok(CTyp::Poly(i_poly.clone(), Spanned::dummy(rem), d));
                        }
                        Err(TypeError::EvaluateMleTooManyArguments)
                    }
                    _ => Err(TypeError::Evaluate),
                }
            }
            // Selected form: eval<range>(p, fixed).
            (Some(range), Some(fixed)) => {
                let fixed_typ = env.typ(fixed);

                let fail = || TypeError::SelectedEvaluate(range.clone());
                if range.step() != 1 || range.start() >= range.end() {
                    return Err(fail());
                }

                match (p_typ, fixed_typ) {
                    (CTyp::Poly(poly_tid, n, d), CTyp::Vec(fixed_elem, fixed_len)) => {
                        let range_len = range.len();
                        if !fixed_elem.node.fits(&CTyp::Base(poly_tid.clone()), kctx)
                            || range.end() > n.node
                            || fixed_len.node != n.node - range_len
                        {
                            return Err(fail());
                        }
                        Ok(CTyp::Poly(poly_tid, Spanned::dummy(range_len), d))
                    }
                    _ => Err(fail()),
                }
            }
            // Parser conversion rejects this mode for source programs.
            // Keep inference defensive in case an internal caller builds
            // the impossible shape directly.
            (Some(range), None) => Err(TypeError::EvaluateSelectorWithoutPoints(range.clone())),
        }
    }

    pub(super) fn infer_mle(self, v: CRef<'_>, env: &Env<'_>) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        // It must be a vector of fields, or a vector of Fin
        let typ = env.typ(v);

        match typ {
            CTyp::Vec(b, n) => {
                if n.node == 0 || !n.is_power_of_two() {
                    return Err(TypeError::Mle);
                }
                let n_pow = n.ilog2() as usize;
                let i = b.to_scalar(kctx).ok_or(TypeError::Mle)?;
                Ok(CTyp::mle(&i, n_pow))
            }
            _ => Err(TypeError::Mle),
        }
    }

    /// The field a `fun`'s parameters range over: the scalar type variable in scope; checked
    /// before the body is typed.
    pub(super) fn fun_field(self, env: &Env<'_>) -> Result<Tid, TypeError> {
        let Env { kctx, .. } = *env;
        kctx.iter()
            .find(|(_, k)| k.is_scalar())
            .map(|(tid, _)| tid.clone())
            .ok_or(TypeError::IllTyped)
    }

    /// A `fun` over one parameter is a univariate polynomial whose degree is its body's (the
    /// parameter is a degree-1 polynomial); over several, a multilinear one whose parameters
    /// are field elements.
    pub(super) fn infer_fun(
        self,
        vars: &[Spanned<Vid>],
        body: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let not_poly = |t: &CTyp| {
            TypeError::located(
                body.span(),
                TypeError::FunBody(kctx.clone(), vars.len(), t.clone()),
            )
        };
        let body_type = env.typ(body);
        if vars.len() == 1 {
            match body_type {
                CTyp::Poly(tid, m, degree) if m.node == 1 => Ok(CTyp::Poly(tid, m, degree)),
                CTyp::Base(tid) => Ok(CTyp::uni(&tid, 0)), // Constant polynomial
                // An integer constant is a constant polynomial over the unique field.
                t @ (CTyp::Fin(_) | CTyp::FieldLiteral) => match t.to_scalar(kctx) {
                    Some(tid) => Ok(CTyp::uni(&tid, 0)),
                    None => Err(not_poly(&t)),
                },
                t => Err(not_poly(&t)),
            }
        } else {
            match body_type {
                // For multilinear, we just return Mle with the number of variables
                // Backend validation will catch if it's not actually multilinear
                CTyp::Base(tid) if kctx.get(&tid).is_some_and(CKind::is_scalar) => {
                    Ok(CTyp::mle(&tid, vars.len()))
                }
                // An integer constant is a constant over the unique field.
                ref t @ (CTyp::Fin(_) | CTyp::FieldLiteral)
                    if let Some(tid) = t.to_scalar(kctx) =>
                {
                    Ok(CTyp::mle(&tid, vars.len()))
                }
                t => Err(not_poly(&t)),
            }
        }
    }
}
