//! Function and polynomial applications: evaluation by call syntax and call inlining.

use super::*;

impl<C: HasOpFactory> UDag<C> {
    #[inline(never)]
    pub(super) fn lower_app(
        &mut self,
        step: Step<'_, C>,
        fid: Spanned<Vid>,
        params: Exps,
    ) -> Result<Lowered<C>, GraphError> {
        let Step {
            exprs,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            expected,
            ..
        } = step;
        // type inference for each parameter
        let param_types: CTyps = params
            .iter()
            .map(|p| exprs.infer(p, kctx, vctx).map(Spanned::dummy))
            .collect::<Result<_, _>>()?;

        // Is it a polynomial, MLE, or a function?
        match &vctx.get(&fid.node) {
            Some(CTyp::Poly(tbase, m, _n)) if m.node == 1 => {
                // It is a univariate polynomial
                let k = kctx.get(tbase).unwrap();

                // Only field elements can be evaluated and only 1 argument can be given
                assert!(k.is_scalar());
                assert_eq!(param_types.len(), 1);

                // Phase B: desugar `p(x)` directly to
                // `evaluate(p, x)` using `Op::Evaluate`. The
                // pre-Phase-B route went through
                // `dot(p, [x^0, x^1, ..., x^n])` which required
                // implicitly reinterpreting the polynomial as a
                // coefficient list — that lub_dot(Poly, Vec) arm
                // has been removed.
                let poly = exprs.push(Exp::Var(fid.clone()), span.clone());
                let eval_exp = exprs.push(Exp::Evaluate(poly, None, Some(params[0])), span);
                // Trampoline
                Ok(Lowered::Rewrite(eval_exp))
            }
            Some(CTyp::Poly(tbase, n, d)) if d.node == 1 => {
                // It is a multilinear extension
                let k = kctx.get(tbase).unwrap();

                // Only field elements can be evaluated and only 1 argument can be given
                assert!(k.is_scalar());
                assert_eq!(param_types.len(), 1);

                // https://github.com/microsoft/Nova/blob/ad4d77ac89d6bbe9ef943056806e65ceb4ba3b3e/src/spartan/polys/multilinear.rs#L58
                let mid = 1_usize
                    .checked_shl(
                        n.node
                            .checked_sub(1)
                            .expect("mle_app: n - 1 underflow (n < 1)")
                            .try_into()
                            .expect("mle_app: n - 1 exceeds u32"),
                    )
                    .expect("mle_app: 1 << (n-1) overflow");
                let end = 1_usize
                    .checked_shl(n.node.try_into().expect("mle_app: n exceeds u32"))
                    .expect("mle_app: 1 << n overflow");
                let mut bound_vars = vctx.keys();
                let coef_var = Vid::fresh(&format!("__coef_{}", fid), &mut bound_vars);

                let mut push = |node| exprs.push(node, span.clone());
                let coefs = Exp::Var(Spanned::dummy(coef_var.clone()));
                let (low, high) = (push(coefs.clone()), push(coefs));
                let low_range = push(Exp::Range(CRange::from_raw(0, 1, mid)));
                let high_range = push(Exp::Range(CRange::from_raw(mid, 1, end)));
                let mle_l = push(Exp::Ram(low, low_range));
                let mle_r = push(Exp::Ram(high, high_range));

                // mle_l + (mle_r - mle_l) * params[0]
                let diff = push(Exp::Bin(BinOp::Sub, mle_r, mle_l));
                let scaled = push(Exp::Bin(BinOp::Mul, params[0], diff));
                let fold = push(Exp::Bin(BinOp::Add, mle_l, scaled));

                let poly = push(Exp::Var(fid.clone()));
                let coef = push(Exp::Coef(poly));
                let let_coef = push(Exp::Let(Spanned::dummy(coef_var), coef));
                let bound_exp = push(Exp::Block(Exps(vec![let_coef]), Some(fold)));

                // Trampoline
                Ok(Lowered::Rewrite(bound_exp))
            }
            _ => {
                // Type checking resolved this call already, so it resolves here.
                let decls = fctx
                    .iter()
                    .map(|(sig, _)| sig)
                    .filter(|sig| sig.name.node == fid.node);
                let (decl, sig, inst) = CSig::resolve_call(decls, &param_types, kctx)
                    .expect("type checking resolved this call");
                let body = fctx.get(decl).expect("a declaration has a body");
                let mut body = body.clone();
                inst.apply(&mut body)
                    .expect("a resolved signature declares every parameter");

                // First add the arguments to the graph, each taking its formal's
                // type (integers passed for field formals become field elements)
                let oparams: Vec<GOp<C>> = params
                    .into_iter()
                    .zip(sig.args.iter())
                    .map(|(p, arg)| {
                        let formal = ATyp::from_ctyp(&arg.typ, kctx);
                        self.add_exp(exprs, p, transcr, edge_type, kctx, fctx, vctx, vars, formal)
                    })
                    .collect::<Result<_, _>>()?;
                // The inlined body's value takes the caller's expected type, else
                // the callee's declared return type.
                if expected.is_none() {
                    *expected = sig
                        .ret
                        .as_ref()
                        .and_then(|r| ATyp::from_ctyp(&r.node, kctx));
                }

                // Trampoline: replace context and continue with body
                let mut next_vctx = vctx.clone();
                for (vid, typ) in sig.args.to_ctx().iter() {
                    next_vctx.insert(vid, typ);
                }
                let mut next_vars = vars.clone();
                for (arg, op) in sig.args.iter().zip(oparams.iter()) {
                    next_vars.insert(&arg.id.node, op);
                }
                let fn_kctx = sig.typevars.to_ctx();
                for (tid, kind) in fn_kctx.iter() {
                    if let CKind::Range(r) = kind
                        && r.step() == 1
                        && r.end() == r.start() + 1
                    {
                        let vid = Vid::new(&tid.0);
                        next_vctx.insert(&vid, &CTyp::Fin(r.clone()));
                        next_vars.insert(&vid, &GOp::Value(Value::Index(r.start())));
                    }
                }
                let body = match body.body() {
                    Some(tree) => exprs.append(tree),
                    None => exprs.push(CExp::Unit, span),
                };
                Ok(Lowered::Inline {
                    body,
                    vctx: next_vctx,
                    vars: next_vars,
                })
            }
        }
    }
}
