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
    ) -> Result<CTyp, TypeError> {
        let Env {
            kctx, fctx, vctx, ..
        } = *env;
        let param_types: CTyps = params
            .iter()
            .map(|p| Spanned::dummy(env.typ(self.at(p))))
            .collect();

        // Is it a polynomial, MLE, or a function?
        match vctx.get(&id.node) {
            Some(CTyp::Poly(tbase, m, _)) if m.node == 1 => {
                // It is a univariate polynomial
                let k = kctx.get(tbase).ok_or(TypeError::lub(
                    TypeError::exp(kctx, vctx, self),
                    LubError::kind_not_found(tbase),
                ))?;

                // Only field elements can be evaluated and only 1 argument can be given
                if !k.is_scalar() || param_types.len() != 1 {
                    return Err(TypeError::uni(
                        kctx,
                        vctx,
                        &id.node,
                        &self.trees(params),
                        &param_types,
                    ));
                }

                // The argument must fit the polynomial's field (integers embed)
                if param_types.0[0].node.fits(&CTyp::Base(tbase.clone()), kctx) {
                    Ok(CTyp::base(tbase))
                } else {
                    Err(TypeError::uni(
                        kctx,
                        vctx,
                        &id.node,
                        &self.trees(params),
                        &param_types,
                    ))
                }
            }
            Some(CTyp::Poly(tbase, n, d)) if d.node == 1 => {
                // It is a multilinear extension
                let k = kctx.get(tbase).ok_or(TypeError::lub(
                    TypeError::exp(kctx, vctx, self),
                    LubError::kind_not_found(tbase),
                ))?;
                // Only field elements can be evaluated and only 1 argument can be given
                if !k.is_scalar() || param_types.len() != 1 {
                    return Err(TypeError::mle_app(
                        kctx,
                        vctx,
                        &id.node,
                        &self.trees(params),
                        &param_types,
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
                    _ => Err(TypeError::mle_app(
                        kctx,
                        vctx,
                        &id.node,
                        &self.trees(params),
                        &param_types,
                    )),
                }
            }
            _ => {
                // It is a function: resolve the call among the declarations of this name.
                let decls = fctx.iter().filter(|sig| sig.name.node == id.node);
                let cause = match CSig::resolve_call(decls, &param_types, kctx) {
                    Ok((decl, sig, _)) => {
                        (env.on_call)(decl);
                        return Ok(sig.ret.map_or(CTyp::Unit, |r| r.node));
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
                            TypeError::Call(kctx.clone(), id.clone(), e)
                        } else {
                            TypeError::func_not_found(
                                kctx,
                                fctx,
                                id,
                                param_types,
                                &self.trees(params),
                                unresolved,
                            )
                        }
                    }
                    Err(CallError::Ambiguous(tied)) => {
                        TypeError::app_multiple(kctx, tied, id, param_types, &self.trees(params))
                    }
                };
                Err(TypeError::within(kctx, vctx, self, cause))
            }
        }
    }
}
