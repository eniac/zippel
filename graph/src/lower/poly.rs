//! `fun` bodies as polynomials.

use super::*;
use backend::poly::variant::{DenseMle, DenseUni};
use lang::ast::Visit;

impl<C: Backend> UDag<C> {
    /// The polynomial a `fun` body over `vars` denotes. Only `+`, `-`, `*`, negation, the
    /// fun's parameters and literals may occur; a factor built from literals alone scales the
    /// other factor. One post-order pass over the body, each subtree a constant or a
    /// polynomial on a value stack, so long bodies take linear time and bounded stack.
    pub(super) fn exp_to_poly_variant(
        exp: CRef<'_>,
        vars: &[Vid],
        var_map: &HashMap<Vid, usize>,
    ) -> Result<PolyVariant<C::F>, GraphError> {
        /// A subtree's value: a field constant until it meets a parameter.
        enum Value<F: Field> {
            Const(F),
            Poly(PolyVariant<F>),
        }
        let non_poly =
            |e: CRef<'_>, msg: String| GraphError::NonPolynomialFun(msg, e.span().clone());
        // Evaluation-table length of a multilinear fun over `vars`.
        let table_len = |e: CRef<'_>| {
            u32::try_from(vars.len())
                .ok()
                .and_then(|n| 1usize.checked_shl(n))
                .ok_or_else(|| non_poly(e, "too many variables in a multilinear fun".to_string()))
        };
        // A constant in the shape of the fun's other leaves.
        let poly = |e: CRef<'_>, v: Value<C::F>| match v {
            Value::Poly(p) => Ok(p),
            Value::Const(c) if vars.len() < 2 => Ok(PolyVariant::from_scalar(c)),
            Value::Const(c) => Ok(PolyVariant::DenseMle(DenseMle::new(
                vars.len(),
                vec![c; table_len(e)?],
            ))),
        };
        let mut values: Vec<Value<C::F>> = Vec::new();
        for visit in exp.walk() {
            let e = match visit {
                Visit::Enter(e) => {
                    if !matches!(
                        e.node(),
                        CExp::Lit(_)
                            | CExp::Var(_)
                            | CExp::Neg(_)
                            | CExp::Bin(BinOp::Add | BinOp::Sub | BinOp::Mul, ..)
                    ) {
                        return Err(non_poly(
                            e,
                            "not an addition, subtraction, multiplication, or negation".to_string(),
                        ));
                    }
                    continue;
                }
                Visit::Bind(..) | Visit::Unbind(_) | Visit::EnterStmt(_) | Visit::LeaveStmt(_) => {
                    continue;
                }
                Visit::Leave(e) => e,
            };
            let value = match e.node() {
                CExp::Lit(n) => Value::Const(field_from_literal::<C>(n)),
                CExp::Var(vid) => {
                    let Some(&var_idx) = var_map.get(&vid.node) else {
                        return Err(non_poly(
                            e,
                            format!("variable `{vid}` is not a parameter of the fun"),
                        ));
                    };
                    Value::Poly(if vars.len() == 1 {
                        // Univariate: x
                        PolyVariant::DenseUni(DenseUni::new(vec![C::F::zero(), C::F::one()]))
                    } else {
                        // Multilinear: the basis polynomial of this variable
                        let mut evals = vec![C::F::zero(); table_len(e)?];
                        for (i, x) in evals.iter_mut().enumerate() {
                            if (i >> var_idx) & 1 == 1 {
                                *x = C::F::one();
                            }
                        }
                        PolyVariant::DenseMle(DenseMle::new(vars.len(), evals))
                    })
                }
                CExp::Neg(_) => match values.pop().expect("operand") {
                    Value::Const(c) => Value::Const(-c),
                    Value::Poly(p) => Value::Poly(p.poly_neg()),
                },
                CExp::Bin(op, ..) => {
                    let b = values.pop().expect("right operand");
                    let a = values.pop().expect("left operand");
                    match (op, a, b) {
                        (BinOp::Add, Value::Const(a), Value::Const(b)) => Value::Const(a + b),
                        (BinOp::Sub, Value::Const(a), Value::Const(b)) => Value::Const(a - b),
                        (BinOp::Mul, Value::Const(a), Value::Const(b)) => Value::Const(a * b),
                        (BinOp::Mul, Value::Const(s), Value::Poly(p))
                        | (BinOp::Mul, Value::Poly(p), Value::Const(s)) => {
                            Value::Poly(p.poly_mul_scalar(s))
                        }
                        (op, a, b) => {
                            let (a, b) = (poly(e, a)?, poly(e, b)?);
                            let result = match op {
                                BinOp::Add => a.poly_add(&b),
                                BinOp::Sub => a.poly_sub(&b),
                                _ => a.poly_mul(&b),
                            };
                            Value::Poly(
                                result
                                    .map_err(|err| non_poly(e, format!("{op:?} failed: {err}")))?,
                            )
                        }
                    }
                }
                _ => unreachable!("checked on entry"),
            };
            values.push(value);
        }
        poly(exp, values.pop().expect("the body's value"))
    }

    pub(super) fn lower_evaluate(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        p: ExpId,
        selector: Option<CRange>,
        opt_points: Option<ExpId>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let vp = self.add_exp(scope, p, None)?;
        match (selector, opt_points) {
            // Unary form: eval(p) -> materialized merged Op::Evaluate(p, None, None).
            // This preserves the old Node::fft sharing behavior for reusable bindings.
            (None, None) => {
                let neval = self.add_node(Node::evaluate_grid(&vp), span.clone());
                self.add_edges(scope.edge_type, neval, vp);

                Ok(GOp::underscore(
                    neval,
                    ATyp::from_ctyp(&typ, scope.kctx)
                        .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?,
                ))
            }
            // Binary form: eval(p, points) -> Op::Evaluate(p, None, Some(points)).
            (None, Some(x)) => {
                let vx = self.add_exp(scope, x, None)?;
                let atyp = ATyp::from_ctyp(&typ, scope.kctx)
                    .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
                Ok(self.materialize(GOp::evaluate(vp, vx), scope.edge_type, atyp, span.clone()))
            }
            // Selected form: eval<range>(p, fixed).
            (Some(range), Some(fixed)) => {
                let vfixed = self.add_exp(scope, fixed, None)?;
                let atyp = ATyp::from_ctyp(&typ, scope.kctx)
                    .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
                Ok(self.materialize(
                    GOp::evaluate_selected(vp, range, vfixed),
                    scope.edge_type,
                    atyp,
                    span.clone(),
                ))
            }
            // Parser conversion rejects this; inference is defensive too.
            (Some(range), None) => Err(TypeError::EvaluateSelectorWithoutPoints(range).into()),
        }
    }

    pub(super) fn lower_poly(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        v: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let child = self.add_exp(scope, v, None)?;

        let npoly = self.add_node(Node::poly(&child), span.clone());

        self.add_edges(scope.edge_type, npoly, child);

        Ok(GOp::underscore(
            npoly,
            ATyp::from_ctyp(&typ, scope.kctx)
                .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?,
        ))
    }

    pub(super) fn lower_coef(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        v: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let child = self.add_exp(scope, v, None)?;

        let npoly = self.add_node(Node::coef(&child), span.clone());

        self.add_edges(scope.edge_type, npoly, child);

        Ok(GOp::underscore(
            npoly,
            ATyp::from_ctyp(&typ, scope.kctx)
                .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?,
        ))
    }

    pub(super) fn lower_interpolate(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        points_opt: Option<ExpId>,
        evals: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let evals_op = self.add_exp(scope, evals, None)?;
        match points_opt {
            // Unary: interpolate(evs) → Op::Ifft(evs)  (FFT-grid interpolation)
            None => {
                let nifft = self.add_node(Node::ifft(&evals_op), span.clone());
                self.add_edges(scope.edge_type, nifft, evals_op);

                Ok(GOp::underscore(
                    nifft,
                    ATyp::from_ctyp(&typ, scope.kctx)
                        .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?,
                ))
            }
            // Binary: interpolate(pts, evs) → Op::Interpolate(pts, evs)
            Some(p) => {
                let points_op = self.add_exp(scope, p, None)?;
                let ninterp = self.add_node(Node::interpolate(&points_op, &evals_op), span.clone());
                self.add_edges(scope.edge_type, ninterp, points_op);
                self.add_edges(scope.edge_type, ninterp, evals_op);

                Ok(GOp::underscore(
                    ninterp,
                    ATyp::from_ctyp(&typ, scope.kctx)
                        .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?,
                ))
            }
        }
    }

    pub(super) fn lower_mle(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        v: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let child = self.add_exp(scope, v, None)?;

        let nmle = self.add_node(Node::mle(&child), span.clone());

        self.add_edges(scope.edge_type, nmle, child);

        Ok(GOp::underscore(
            nmle,
            ATyp::from_ctyp(&typ, scope.kctx)
                .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?,
        ))
    }

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
