//! `fun` bodies as polynomials.

use super::*;
use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, univariate::DensePolynomial};

impl<C: HasOpFactory> UDag<C> {
    /// Convert a Fun expression body to a PolyVariant
    /// Only polynomial operations (Add, Sub, Mul with scalars, Var, Lit) are allowed
    #[stack_guard]
    pub(super) fn exp_to_poly_variant(
        exp: CRef<'_>,
        vars: &[Vid],
        var_map: &HashMap<Vid, usize>,
    ) -> Result<PolyVariant<C::F>, GraphError> {
        use ark_ff::{One, Zero};

        let non_poly = |msg: String| GraphError::NonPolynomialFun(msg, exp.span().clone());
        // Evaluation-table length of a multilinear fun over `vars`.
        let table_len = || {
            u32::try_from(vars.len())
                .ok()
                .and_then(|n| 1usize.checked_shl(n))
                .ok_or_else(|| non_poly("too many variables in a multilinear fun".to_string()))
        };
        let at = |id: &ExpId| exp.at(*id);
        match exp.node() {
            CExp::Lit(n) => {
                // Field constant, in the shape of the fun's other leaves.
                let scalar = field_from_literal::<C>(n);
                if vars.len() < 2 {
                    Ok(PolyVariant::from_scalar(scalar))
                } else {
                    let evals = vec![scalar; table_len()?];
                    Ok(PolyVariant::DenseMle(
                        DenseMultilinearExtension::from_evaluations_vec(vars.len(), evals),
                    ))
                }
            }
            CExp::Var(vid) => {
                // Check if this is a bound variable
                if let Some(&var_idx) = var_map.get(&vid.node) {
                    // Create a polynomial with variable
                    if vars.len() == 1 {
                        // Univariate: create polynomial [0, 1] representing x
                        let poly =
                            DensePolynomial::from_coefficients_vec(vec![C::F::zero(), C::F::one()]);
                        Ok(PolyVariant::DenseUni(poly))
                    } else {
                        // Multilinear: create a basis polynomial
                        let num_vars = vars.len();
                        let mut evals = vec![C::F::zero(); table_len()?];
                        // Set evaluation at the point corresponding to this variable
                        for (i, e) in evals.iter_mut().enumerate() {
                            if (i >> var_idx) & 1 == 1 {
                                *e = C::F::one();
                            }
                        }
                        let mle = DenseMultilinearExtension::from_evaluations_vec(num_vars, evals);
                        Ok(PolyVariant::DenseMle(mle))
                    }
                } else {
                    Err(non_poly(format!(
                        "variable `{}` is not a parameter of the fun",
                        vid
                    )))
                }
            }
            CExp::Bin(BinOp::Add, a, b) => {
                let pa = Self::exp_to_poly_variant(at(a), vars, var_map)?;
                let pb = Self::exp_to_poly_variant(at(b), vars, var_map)?;
                pa.poly_add(&pb)
                    .map_err(|e| non_poly(format!("Add failed: {}", e)))
            }
            CExp::Bin(BinOp::Sub, a, b) => {
                let pa = Self::exp_to_poly_variant(at(a), vars, var_map)?;
                let pb = Self::exp_to_poly_variant(at(b), vars, var_map)?;
                pa.poly_sub(&pb)
                    .map_err(|e| non_poly(format!("Sub failed: {}", e)))
            }
            CExp::Bin(BinOp::Mul, a, b) => {
                // A constant factor scales the other one, whatever its encoding.
                if let Some(s) = Self::scalar_constant_in_fun(at(a)) {
                    return Ok(Self::exp_to_poly_variant(at(b), vars, var_map)?.poly_mul_scalar(s));
                }
                if let Some(s) = Self::scalar_constant_in_fun(at(b)) {
                    return Ok(Self::exp_to_poly_variant(at(a), vars, var_map)?.poly_mul_scalar(s));
                }
                let pa = Self::exp_to_poly_variant(at(a), vars, var_map)?;
                let pb = Self::exp_to_poly_variant(at(b), vars, var_map)?;
                pa.poly_mul(&pb)
                    .map_err(|e| non_poly(format!("Mul failed: {}", e)))
            }
            CExp::Neg(a) => Ok(Self::exp_to_poly_variant(at(a), vars, var_map)?.poly_neg()),
            _ => Err(non_poly(format!(
                "`{}` is not an addition, subtraction, multiplication, or negation",
                exp
            ))),
        }
    }

    /// The field value of a variable-free fun subexpression built from literals with `-`,
    /// `+`, `-` and `*`; `None` for anything else.
    #[stack_guard]
    pub(super) fn scalar_constant_in_fun(exp: CRef<'_>) -> Option<C::F> {
        let at = |id: &ExpId| exp.at(*id);
        match exp.node() {
            CExp::Lit(n) => Some(field_from_literal::<C>(n)),
            CExp::Neg(a) => Self::scalar_constant_in_fun(at(a)).map(|c| -c),
            CExp::Bin(BinOp::Add, a, b) => {
                Some(Self::scalar_constant_in_fun(at(a))? + Self::scalar_constant_in_fun(at(b))?)
            }
            CExp::Bin(BinOp::Sub, a, b) => {
                Some(Self::scalar_constant_in_fun(at(a))? - Self::scalar_constant_in_fun(at(b))?)
            }
            CExp::Bin(BinOp::Mul, a, b) => {
                Some(Self::scalar_constant_in_fun(at(a))? * Self::scalar_constant_in_fun(at(b))?)
            }
            _ => None,
        }
    }

    #[inline(never)]
    pub(super) fn lower_evaluate(
        &mut self,
        step: Step<'_, C>,
        p: ExpId,
        selector: Option<CRange>,
        opt_points: Option<ExpId>,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let vp = self.add_exp(exprs, p, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        match (selector, opt_points) {
            // Unary form: eval(p) -> materialized merged Op::Evaluate(p, None, None).
            // This preserves the old Node::fft sharing behavior for reusable bindings.
            (None, None) => {
                let neval = self.add_node(Node::evaluate_grid(&vp), span.clone());
                self.add_edges(edge_type, neval, vp);

                Ok(GOp::underscore(
                    neval,
                    ATyp::from_ctyp(typ, kctx)
                        .ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?,
                ))
            }
            // Binary form: eval(p, points) -> Op::Evaluate(p, None, Some(points)).
            (None, Some(x)) => {
                let vx =
                    self.add_exp(exprs, x, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
                let atyp = ATyp::from_ctyp(typ, kctx)
                    .ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
                Ok(self.materialize(GOp::evaluate(vp, vx), edge_type, atyp, span.clone()))
            }
            // Selected form: eval<range>(p, fixed).
            (Some(range), Some(fixed)) => {
                let vfixed = self.add_exp(
                    exprs, fixed, transcr, edge_type, kctx, fctx, vctx, vars, None,
                )?;
                let atyp = ATyp::from_ctyp(typ, kctx)
                    .ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
                Ok(self.materialize(
                    GOp::evaluate_selected(vp, range, vfixed),
                    edge_type,
                    atyp,
                    span.clone(),
                ))
            }
            // Parser conversion rejects this; inference is defensive too.
            (Some(range), None) => {
                Err(
                    TypeError::evaluate_selector_without_points(kctx, vctx, exprs.at(p), range)
                        .into(),
                )
            }
        }
    }

    #[inline(never)]
    pub(super) fn lower_poly(&mut self, step: Step<'_, C>, v: ExpId) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let child = self.add_exp(exprs, v, transcr, edge_type, kctx, fctx, vctx, vars, None)?;

        let npoly = self.add_node(Node::poly(&child), span.clone());

        self.add_edges(edge_type, npoly, child);

        Ok(GOp::underscore(
            npoly,
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?,
        ))
    }

    #[inline(never)]
    pub(super) fn lower_coef(&mut self, step: Step<'_, C>, v: ExpId) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let child = self.add_exp(exprs, v, transcr, edge_type, kctx, fctx, vctx, vars, None)?;

        let npoly = self.add_node(Node::coef(&child), span.clone());

        self.add_edges(edge_type, npoly, child);

        Ok(GOp::underscore(
            npoly,
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?,
        ))
    }

    #[inline(never)]
    pub(super) fn lower_interpolate(
        &mut self,
        step: Step<'_, C>,
        points_opt: Option<ExpId>,
        evals: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let evals_op = self.add_exp(
            exprs, evals, transcr, edge_type, kctx, fctx, vctx, vars, None,
        )?;
        match points_opt {
            // Unary: interpolate(evs) → Op::Ifft(evs)  (FFT-grid interpolation)
            None => {
                let nifft = self.add_node(Node::ifft(&evals_op), span.clone());
                self.add_edges(edge_type, nifft, evals_op);

                Ok(GOp::underscore(
                    nifft,
                    ATyp::from_ctyp(typ, kctx)
                        .ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?,
                ))
            }
            // Binary: interpolate(pts, evs) → Op::Interpolate(pts, evs)
            Some(p) => {
                let points_op =
                    self.add_exp(exprs, p, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
                let ninterp = self.add_node(Node::interpolate(&points_op, &evals_op), span.clone());
                self.add_edges(edge_type, ninterp, points_op);
                self.add_edges(edge_type, ninterp, evals_op);

                Ok(GOp::underscore(
                    ninterp,
                    ATyp::from_ctyp(typ, kctx)
                        .ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?,
                ))
            }
        }
    }

    #[inline(never)]
    pub(super) fn lower_mle(&mut self, step: Step<'_, C>, v: ExpId) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let child = self.add_exp(exprs, v, transcr, edge_type, kctx, fctx, vctx, vars, None)?;

        let nmle = self.add_node(Node::mle(&child), span.clone());

        self.add_edges(edge_type, nmle, child);

        Ok(GOp::underscore(
            nmle,
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?,
        ))
    }

    #[inline(never)]
    pub(super) fn lower_fun(
        exprs: &Exprs<BigUint>,
        fun_vars: Vec<Spanned<Vid>>,
        body: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        // Convert the Fun expression body to a PolyVariant
        let fun_vars_vids: Vec<Vid> = fun_vars.iter().map(|v| v.node.clone()).collect();
        let var_map: HashMap<Vid, usize> = fun_vars_vids
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i))
            .collect();

        let poly = Self::exp_to_poly_variant(exprs.at(body), &fun_vars_vids, &var_map)?;

        // Create a Value::Poly from the PolyVariant wrapped in VirtualPolynomial
        let poly_value = Value::poly(VirtualPolynomial::from_poly(poly));

        Ok(GOp::Value(poly_value))
    }
}
