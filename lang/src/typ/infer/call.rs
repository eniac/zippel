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
        let Cx { kctx, fctx, vctx } = env.cx;
        let param_types: CTyps = params
            .iter()
            .map(|p| Spanned::new(env.typ(self.at(p)), self.at(p).span().clone()))
            .collect();

        // Is it a polynomial, MLE, or a function?
        match vctx.get(&id.node) {
            Some(CTyp::Poly(tbase, m, _)) if m.node == 1 => {
                // It is a univariate polynomial
                let k = kctx
                    .get(tbase)
                    .ok_or(TypeError::from(LubError::kind_not_found(tbase)))?;

                // Only field elements can be evaluated and only 1 argument can be given
                if !k.is_scalar() || param_types.len() != 1 {
                    return Err(TypeError::Uni(
                        kctx.clone(),
                        id.node.clone(),
                        param_types.clone(),
                    ));
                }

                // The argument must fit the polynomial's field (integers embed)
                if param_types.0[0].node.fits(&CTyp::Base(tbase.clone()), kctx) {
                    Ok(CTyp::base(tbase))
                } else {
                    Err(TypeError::Uni(
                        kctx.clone(),
                        id.node.clone(),
                        param_types.clone(),
                    ))
                }
            }
            Some(CTyp::Poly(tbase, n, d)) if d.node == 1 => {
                // It is a multilinear extension
                let k = kctx
                    .get(tbase)
                    .ok_or(TypeError::from(LubError::kind_not_found(tbase)))?;
                // Only field elements can be evaluated and only 1 argument can be given
                if !k.is_scalar() || param_types.len() != 1 {
                    return Err(TypeError::MleApp(
                        kctx.clone(),
                        id.node.clone(),
                        param_types.clone(),
                    ));
                }

                // The argument must be a field and the same as the MLE
                match &param_types.0[0].node {
                    CTyp::Fin(_) | CTyp::FieldLiteral if n.node > 0 => {
                        let rem = n.node - 1;
                        Ok(CTyp::mle(tbase, rem))
                    }
                    CTyp::Base(tb) if tb == tbase && n.node > 0 => {
                        let rem = n.node - 1;
                        Ok(CTyp::mle(tbase, rem))
                    }
                    CTyp::Vec(CTyp::Base(tb), m) if tb == tbase && n.node == m.node => {
                        Ok(CTyp::base(tbase))
                    }
                    CTyp::Vec(CTyp::Fin(_) | CTyp::FieldLiteral, m) if n.node == m.node => {
                        Ok(CTyp::base(tbase))
                    }
                    CTyp::Vec(CTyp::Fin(_) | CTyp::FieldLiteral, m) if n.node > m.node => {
                        let rem = n.node - m.node;
                        Ok(CTyp::mle(tbase, rem))
                    }
                    CTyp::Vec(CTyp::Base(tb), m) if tb == tbase && n.node > m.node => {
                        let rem = n.node - m.node;
                        Ok(CTyp::mle(tbase, rem))
                    }
                    _ => Err(TypeError::MleApp(
                        kctx.clone(),
                        id.node.clone(),
                        param_types.clone(),
                    )),
                }
            }
            _ => {
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
