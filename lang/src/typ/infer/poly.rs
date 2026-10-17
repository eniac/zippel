//! Polynomial constructors and evaluation: `interpolate`, `poly`, `coef`, `eval`, `mle`, `fun`.

use super::*;
use crate::ast::range::CRange;

impl CRef<'_> {
    #[inline(never)]
    pub(super) fn infer_interpolate(
        self,
        points_opt: Option<CRef<'_>>,
        evals: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let evals_typ = evals
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        match points_opt {
            None => match evals_typ {
                CTyp::Vec(b, n) => {
                    let i = b
                        .to_scalar(kctx)
                        .ok_or(TypeError::interpolate_unary(kctx, vctx, self))?;
                    if !n.is_power_of_two() {
                        return Err(TypeError::interpolate_unary_not_pow2(
                            kctx, vctx, self, n.node,
                        ));
                    }
                    // n evaluations on the n-th roots of unity uniquely
                    // determine a polynomial of max degree n-1
                    // (n coefficients under the m+1 convention).
                    // Pow2 check above rules out n == 0, so n >= 1.
                    let deg = n.node - 1;
                    Ok(CTyp::uni(&i, deg))
                }
                _ => Err(TypeError::interpolate_unary(kctx, vctx, self)),
            },
            Some(points) => {
                let points_typ = points
                    .infer_in(kctx, fctx, vctx, cx)
                    .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

                match (points_typ, evals_typ) {
                    (CTyp::Vec(bp, np), CTyp::Vec(be, ne)) if np == ne => {
                        if ne.node == 0 {
                            return Err(TypeError::interpolate(kctx, vctx, self));
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
                            .ok_or(TypeError::interpolate(kctx, vctx, self))?;
                        let field = CTyp::Base(ie.clone());
                        if !bp.node.fits(&field, kctx) || !be.node.fits(&field, kctx) {
                            return Err(TypeError::interpolate(kctx, vctx, self));
                        }
                        // Lagrange interpolation at ne distinct points
                        // yields a polynomial of max degree ne-1
                        // (ne coefficients under the m+1 convention).
                        // np == ne and ne >= 1 since vector typing
                        // rejects empty literals upstream.
                        let deg = ne.node - 1;
                        Ok(CTyp::uni(&ie, deg))
                    }
                    _ => Err(TypeError::interpolate(kctx, vctx, self)),
                }
            }
        }
    }

    #[inline(never)]
    pub(super) fn infer_poly(
        self,
        v: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let typ = v
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        match typ {
            CTyp::Vec(b, k) => {
                if k.node == 0 {
                    return Err(TypeError::poly(kctx, vctx, self));
                }
                let i = b.to_scalar(kctx).ok_or(TypeError::poly(kctx, vctx, self))?;
                let deg = k.node - 1;
                Ok(CTyp::uni(&i, deg))
            }
            _ => Err(TypeError::poly(kctx, vctx, self)),
        }
    }

    #[inline(never)]
    pub(super) fn infer_coef(
        self,
        p: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let typ = p
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        match typ {
            CTyp::Poly(tid, m_vars, m) if m_vars.node == 1 => {
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
            CTyp::Poly(tid, n, d) if n.node > 1 && d.node == 1 => {
                let k = kctx.get(&tid).ok_or(TypeError::lub(
                    TypeError::exp(kctx, vctx, self),
                    LubError::kind_not_found(&tid),
                ))?;
                if k.is_scalar() {
                    if let Some(len) = 1_usize.checked_shl(n.node as u32) {
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

    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    pub(super) fn infer_evaluate(
        self,
        p: CRef<'_>,
        selector: Option<&CRange>,
        opt_points: Option<CRef<'_>>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        let p_typ = p
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        match (selector, opt_points) {
            // Unary form: eval(p) — evaluation on the FFT grid (n roots of unity).
            (None, None) => {
                let t = p_typ;
                match t.clone() {
                    CTyp::Poly(tid, m_vars, n) if m_vars.node == 1 => {
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
                                kctx, vctx, p, n.node, &t,
                            ));
                        }
                        Ok(CTyp::vec(&CTyp::Base(tid), coef_count))
                    }
                    _ => Err(TypeError::evaluate_grid(kctx, vctx, p, &t)),
                }
            }
            // Binary form: eval(p, points) — point or vector evaluation.
            (None, Some(x)) => {
                let x_typ = x
                    .infer_in(kctx, fctx, vctx, cx)
                    .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

                match (p_typ, x_typ) {
                    // Univariate polynomial evaluated at a single scalar point.
                    // Result is a scalar of the same base type. (The
                    // pre-Phase-B path desugared `p(x)` into
                    // `dot(p, [x^0, ..., x^n])`, which routed through
                    // `lub_dot(Poly, Vec)` — that arm has been
                    // removed, and the App desugaring now produces
                    // `evaluate(p, x)` directly.)
                    (CTyp::Poly(i, m, _n), CTyp::Base(b)) if m.node == 1 && i == b => {
                        let k = kctx.get(&i).ok_or(TypeError::evaluate(kctx, vctx, p, x))?;
                        if !k.is_scalar() {
                            return Err(TypeError::evaluate(kctx, vctx, p, x));
                        }
                        Ok(CTyp::Base(i))
                    }
                    // An integer point embeds into the polynomial's own field.
                    (CTyp::Poly(i, m, _n), CTyp::Fin(_) | CTyp::FieldLiteral) if m.node == 1 => {
                        let k = kctx.get(&i).ok_or(TypeError::evaluate(kctx, vctx, p, x))?;
                        if !k.is_scalar() {
                            return Err(TypeError::evaluate(kctx, vctx, p, x));
                        }
                        Ok(CTyp::Base(i))
                    }
                    // Univariate polynomial evaluated at a vector of points is a
                    // hard type error: evaluate at a single scalar via `p(x)`, or
                    // write `[p(x) for x in points]` to evaluate at many points.
                    (CTyp::Poly(_i, m, _n), CTyp::Vec(_b, _len)) if m.node == 1 => {
                        Err(TypeError::evaluate_univariate_vector(kctx, vctx, p, x))
                    }
                    // Multivariate polynomial (MLE, virtual, etc.): n > 1.
                    (CTyp::Poly(i_poly, n, d), CTyp::Vec(b, len_vec)) if n.node > 1 => {
                        // Points must fit the polynomial's field (integers embed).
                        if !b.node.fits(&CTyp::Base(i_poly.clone()), kctx) {
                            return Err(TypeError::evaluate(kctx, vctx, p, x));
                        }
                        if len_vec == n {
                            return Ok(CTyp::Base(i_poly.clone()));
                        }
                        if len_vec < n {
                            let rem = n.node - len_vec.node;
                            return Ok(CTyp::Poly(i_poly.clone(), Spanned::dummy(rem), d));
                        }
                        Err(TypeError::evaluate_mle_too_many_arguments(kctx, vctx, p, x))
                    }
                    _ => Err(TypeError::evaluate(kctx, vctx, p, x)),
                }
            }
            // Selected form: eval<range>(p, fixed).
            (Some(range), Some(fixed)) => {
                let fixed_typ = fixed
                    .infer_in(kctx, fctx, vctx, cx)
                    .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

                let fail = || TypeError::evaluate_selected(kctx, vctx, p, fixed, range.clone());
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
            (Some(range), None) => Err(TypeError::evaluate_selector_without_points(
                kctx,
                vctx,
                p,
                range.clone(),
            )),
        }
    }

    #[inline(never)]
    pub(super) fn infer_mle(
        self,
        v: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
        // It must be a vector of fields, or a vector of Fin
        let typ = v
            .infer_in(kctx, fctx, vctx, cx)
            .map_err(|e| TypeError::within(kctx, vctx, self, e))?;

        match typ {
            CTyp::Vec(b, n) => {
                if n.node == 0 || !n.is_power_of_two() {
                    return Err(TypeError::mle(kctx, vctx, self));
                }
                let n_pow = n.ilog2() as usize;
                let i = b.to_scalar(kctx).ok_or(TypeError::mle(kctx, vctx, self))?;
                Ok(CTyp::mle(&i, n_pow))
            }
            _ => Err(TypeError::mle(kctx, vctx, self)),
        }
    }

    #[inline(never)]
    pub(super) fn infer_fun(
        self,
        vars: &[Spanned<Vid>],
        body: CRef<'_>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        cx: &Cx<'_>,
    ) -> Result<CTyp, TypeError> {
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
                new_vctx.insert(&var.node, &CTyp::uni(&field_tid, 1));
            }

            // Infer the type of the body - should get Poly(F, 1, N) where N is the degree
            let body_type = body.infer_in(kctx, fctx, &new_vctx, cx)?;

            // Extract the degree from the inferred type
            match body_type {
                CTyp::Poly(tid, m, degree) if m.node == 1 => Ok(CTyp::Poly(tid, m, degree)),
                CTyp::Base(tid) => Ok(CTyp::uni(&tid, 0)), // Constant polynomial
                // An integer constant is a constant polynomial over the unique field.
                t @ (CTyp::Fin(_) | CTyp::FieldLiteral) => match t.to_scalar(kctx) {
                    Some(tid) => Ok(CTyp::uni(&tid, 0)),
                    None => Err(TypeError::located(
                        body.span(),
                        TypeError::fun_body(kctx, vctx, self, vars.len(), &t),
                    )),
                },
                t => Err(TypeError::located(
                    body.span(),
                    TypeError::fun_body(kctx, vctx, self, vars.len(), &t),
                )),
            }
        } else {
            // Multilinear polynomial - type variables as scalars and validate structure
            for var in vars {
                new_vctx.insert(&var.node, &CTyp::Base(field_tid.clone()));
            }

            let body_type = body.infer_in(kctx, fctx, &new_vctx, cx)?;

            match body_type {
                CTyp::Base(tid) if kctx.get(&tid).map(|k| k.is_scalar()).unwrap_or(false) => {
                    // For multilinear, we just return Mle with the number of variables
                    // Backend validation will catch if it's not actually multilinear
                    Ok(CTyp::mle(&tid, vars.len()))
                }
                // An integer constant is a constant over the unique field.
                ref t @ (CTyp::Fin(_) | CTyp::FieldLiteral)
                    if let Some(tid) = t.to_scalar(kctx) =>
                {
                    Ok(CTyp::mle(&tid, vars.len()))
                }
                t => Err(TypeError::located(
                    body.span(),
                    TypeError::fun_body(kctx, vctx, self, vars.len(), &t),
                )),
            }
        }
    }
}
