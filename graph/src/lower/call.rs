//! Function and polynomial applications: evaluation by call syntax and call inlining.

use super::*;

impl<C: HasOpFactory> UDag<C> {
    pub(super) fn lower_app(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        fid: Spanned<Vid>,
        params: Exps,
        expected: &mut Option<ATyp>,
    ) -> Result<ExpId, GraphError> {
        let span = scope.exprs.span(id).clone();
        // Is it a polynomial, MLE, or a function?
        match scope.vctx.get(&fid.node).cloned() {
            // Applying a polynomial is `eval`: `p(x)` for a univariate polynomial; for one in
            // several variables, `p(x)` is `eval(p, [x])`, fixing variable 0 (for an MLE, the
            // low bit of an evaluation's index), and `p([x0, ...])` is `eval(p, [x0, ...])`.
            Some(CTyp::Poly(_, vars, _)) => {
                assert_eq!(params.len(), 1, "a polynomial takes one argument");
                let point_is_vec = matches!(scope.infer(params[0])?, CTyp::Vec(..));
                let mut push = |node| scope.exprs.push(node, span.clone());
                let point = if vars.node > 1 && !point_is_vec {
                    push(Exp::Vec(Exps(vec![params[0]])))
                } else {
                    params[0]
                };
                let poly = push(Exp::Var(fid.clone()));
                // Trampoline
                Ok(push(Exp::Evaluate(poly, None, Some(point))))
            }
            _ => {
                let call = scope
                    .exprs
                    .types
                    .call(id)
                    .expect("inference recorded the function call");
                let sig = call.signature.clone();
                let mut body = scope
                    .fctx
                    .get(&call.declaration)
                    .expect("a declaration has a body")
                    .clone();
                call.instantiation
                    .apply(&mut body)
                    .expect("a resolved signature declares every parameter");

                // First add the arguments to the graph, each taking its formal's
                // type (integers passed for field formals become field elements)
                let oparams: Vec<GOp<C>> = params
                    .into_iter()
                    .zip(sig.args.iter())
                    .map(|(p, arg)| {
                        let formal = ATyp::from_ctyp(&arg.typ, scope.kctx);
                        self.add_exp(scope, p, formal)
                    })
                    .collect::<Result<_, _>>()?;
                // The inlined body's value takes the caller's expected type, else
                // the callee's declared return type.
                if expected.is_none() {
                    *expected = sig
                        .ret
                        .as_ref()
                        .and_then(|r| ATyp::from_ctyp(&r.node, scope.kctx));
                }

                // Trampoline: bind the parameters and continue with the body. The enclosing
                // `add_exp` unbinds them when the call's value is lowered.
                for (vid, typ) in sig.args.to_ctx().iter() {
                    scope.vctx.insert(vid, typ);
                }
                for (arg, op) in sig.args.iter().zip(oparams.iter()) {
                    scope.vars.insert(&arg.id.node, op);
                }
                let fn_kctx = sig.typevars.to_ctx();
                for (tid, kind) in fn_kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step() == 1
                        && r.end() == r.start() + 1
                    {
                        let vid = Vid::new(&tid.0);
                        scope.vctx.insert(&vid, &CTyp::Fin(r.clone()));
                        scope
                            .vars
                            .insert(&vid, &GOp::Value(Value::Index(r.start())));
                    }
                }
                Ok(match body.body() {
                    Some(tree) => scope.exprs.append(tree),
                    None => scope.exprs.push(CExp::Unit, span),
                })
            }
        }
    }
}
