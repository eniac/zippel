//! Applications: polynomial and MLE evaluation by call syntax, and function calls resolved
//! among overloaded declarations.

use super::*;
use crate::ast::sig::SigError;
use crate::typ::CTyps;
use crate::typ::instantiate::CallError;

impl CRef<'_> {
    pub(super) fn infer_app(
        self,
        id: &Spanned<Vid>,
        params: &Exps,
        env: &Env<'_>,
        call: &mut Option<ResolvedCall>,
    ) -> Result<CTyp, TypeError> {
        let Cx { kctx, fctx } = env.cx;
        let vctx = env.vctx;
        let param_types: CTyps = params
            .iter()
            .map(|p| Spanned::new(env.typ(self.at(p)), self.at(p).span().clone()))
            .collect();

        // Is it a polynomial, another variable, or a function?
        match vctx.get(&id.node) {
            // Applying a polynomial is `eval` at one point; a scalar for a polynomial in
            // several variables is the point `[x]`, fixing its variable 0.
            Some(p_typ @ CTyp::Poly(_, vars, _)) => {
                let [point] = &param_types.0[..] else {
                    return Err(TypeError::PolyApp(
                        kctx.clone(),
                        id.node.clone(),
                        param_types.clone(),
                    ));
                };
                let point = match &point.node {
                    x @ CTyp::Vec(..) => x.clone(),
                    x if vars.node > 1 => CTyp::vec(x, 1),
                    x => x.clone(),
                };
                super::poly::evaluated_typ(p_typ.clone(), point, kctx)
            }
            // Any other variable: it hides the functions of its name, so this calls none.
            Some(t) => Err(TypeError::NotApplicable(
                kctx.clone(),
                id.clone(),
                t.clone(),
            )),
            None => {
                // It is a function: resolve the call among the declarations of this name.
                let decls = fctx.iter().filter(|sig| sig.name.node == id.node);
                let cause = match CSig::resolve_call(decls, &param_types, kctx) {
                    Ok((decl, sig, instantiation)) => {
                        let ret = sig.ret.as_ref().map_or(CTyp::Unit, |r| r.node.clone());
                        *call = Some(ResolvedCall {
                            declaration: decl.clone(),
                            signature: sig,
                            instantiation,
                        });
                        return Ok(ret);
                    }
                    Err(CallError::NoMatch(failures)) => {
                        // Declarations that fit the arguments but whose type parameters
                        // could not all be solved.
                        let mut unresolved: Vec<(CSig, SigError)> = failures
                            .into_iter()
                            .filter(|(_, e)| {
                                matches!(
                                    e,
                                    SigError::Uninferable { .. } | SigError::KindUnsatisfied { .. }
                                )
                            })
                            .collect();
                        if unresolved.len() == 1 {
                            let (_, e) = unresolved.pop().expect("one element");
                            TypeError::Call(id.clone(), Box::new(e))
                        } else {
                            TypeError::FuncNotFound(
                                kctx.clone(),
                                fctx.clone(),
                                id.clone(),
                                param_types,
                                unresolved,
                            )
                        }
                    }
                    Err(CallError::Ambiguous(tied)) => {
                        TypeError::AppMultiple(kctx.clone(), tied, id.clone(), param_types)
                    }
                };
                Err(cause)
            }
        }
    }
}
