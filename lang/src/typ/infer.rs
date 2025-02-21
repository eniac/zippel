#![allow(refining_impl_trait)]
use share::{Ctx, Set, Opt, Proj2, log2};
use share::traversal::{ToTraversal1, ToTraversal2};
use crate::id::{Fid, Tid, Vid};
use crate::exp::{BinOp, CAExp, AExps, CAExps, TAExp, TAExps, CBExp, TBExp};
use crate::Decl;
use crate::typ::unify::{Unify, UnifyError};
use crate::typ::sig::Sig;
use crate::typ::AliasSubsts;
use crate::range::Range;
use crate::typ::{CTyp, Nothing, Kind};
use thiserror::Error;

use std::fmt;

#[derive(Error, PartialEq, Eq, Debug)]
pub enum TypeError {
    #[error("AddTypeError: In expression {0}, {1} |- {2} + {3}\n\t{4}")]
    Add(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("SubTypeError: In expression {0}, {1} |- {2} - {3}\n\t{4}")]
    Sub(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("MulTypeError: In expression {0}, {1} |- {2} * {3}\n\t{4}")]
    Mul(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("DivTypeError: In expression {0}, {1} |- {2} / {3}\n\t{4}")]
    Div(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("PowTypeError: In expression {0}, {1} |- {2} ^ {3}\n\t{4}")]
    Pow(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("DotTypeError: In expression {0}, {1} |- {2} . {3}\n\t{4}")]
    Dot(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("EquTypeError: In expression {0}, {1} |- {2} == {3}\n\t{4}")]
    Equ(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("ContainsTypeError: Expects a vector and element of the same type: {0}, {1} |- contains {2} [ {3} ]\n\t{4}")]
    Contains(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, Opt<UnifyError>),
    #[error("VecInnerType: Container elements must have a base type {0}, {1} |- [ {2}, .., {3} ]\n\t{4}")]
    VecInner(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, UnifyError),
    #[error("VecEmptyError: Cannot define empty vector {0}, {1} |- []")]
    VecEmpty(Ctx<Tid, Kind>, Ctx<Vid, CTyp>),
    #[error("CoefficientError: Argument to [coef] must be a vector of fields {0}, {1} |- coef {2}")]
    Coef(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),
    #[error("Mle: Arguments to [mle] must be a vector type with size a power of 2: {0}, {1} |- mle {2}")]
    Mle(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),
    #[error("GenError: Type parameter to [gen] must be a Group kind {0}, {1} |- gen {2}\n\t{3}")]
    Gen(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Tid, Opt<UnifyError>),
    #[error("MapError: Arguments to [for] must be a vector type {0}, {1} |- [{2} for {3} in {4}]")]
    Map(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp, Vid, TAExp),
    #[error("VarError: Variable {0} not found in context {1}")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),
    #[error("AssertError: Assertion must be a boolean expression {0}, {1} |- assert {2}\n\t{3}")]
    Assert(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TBExp, Opt<UnifyError>),
    #[error("VerifyError: Verification must be a boolean expression {0}, {1} |- verify {2}\n\t{3}")]
    Verify(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TBExp, Opt<UnifyError>),
    #[error("ConcatenateError: Cannot concatenate {0}, {1} |- {2} ++ {3}\n\t{4}")]
    Concat(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, Opt<UnifyError>),
    #[error("InterpolateError: Cannot interpolate {0} |- interpolate ({1}, {2})\n\t{3}")]
    Interp(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp, Opt<UnifyError>),
    #[error("RamError: Index must be a Fin type within the bounds of the vector {0}, {1} |- {2} [ {3} ]")]
    Ram(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),
    #[error("AppMultipleError: Function has multiple matching definitions in context {0} |- {1} ( {2} )")]
    AppMultiple(Set<(Fid, Sig)>, Fid, TAExps),
    #[error("FuncNotFound: No matching definition found for function {0} |- {1} ( {2} )")]
    FuncNotFound(Set<(Fid, Sig)>, Fid, TAExps),
}

/// Infer a type with a typing context and typing constraints
pub trait Typeable {
    type Output;
    fn infer(self,
        kctx: &Ctx<Tid, Kind>,      // Kind context Tid -> Kind
        fctx: &Set<(Fid, Sig)>,     // Function context Fid -> Sig
        vctx: &mut Ctx<Vid, CTyp>,  // Variable context Vid -> CTyp
        subs: &mut AliasSubsts,     // Substitutions of type variables
        ) -> Result<Self::Output, TypeError>;
}

/// Type inference for [CAExp]
impl Typeable for CAExp {
    type Output = TAExp;
    fn infer(self,kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>,
        vctx: &mut Ctx<Vid, CTyp>, subs: &mut AliasSubsts) -> Result<Self::Output, TypeError> {
        match self {
            // Infer the type of a literal [n] as a Fin<n> type
            CAExp::Lit(n, _) =>
                Ok(TAExp::Lit(n, CTyp::fin(Range::singleton(n)))),

            // Infer the type of a univariate polynomial from its coefficients' vector
            CAExp::Coef(box v, _) => {
                // Infer the type of its argument
                let tv = v.infer(kctx, fctx, vctx, subs)?;
                // It must be a vector of fields, or a vector of Fin
                match tv.proj2() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::Coef(kctx.clone(), vctx.clone(), tv))?;
                        Ok(TAExp::Coef(Box::new(tv), CTyp::uni(i, n)))
                    },
                    _ => Err(TypeError::Coef(kctx.clone(), vctx.clone(), tv))
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CAExp::Mle(box v, _) => {
                // Infer the type of its argument
                let tv = v.infer(kctx, fctx, vctx, subs)?;
                // It must be a vector of fields, or a vector of Fin
                match tv.proj2() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::Mle(kctx.clone(), vctx.clone(), tv))?;
                        let (exp, rem) = log2(n);
                        if rem == 0 {
                            Ok(TAExp::Mle(Box::new(tv), CTyp::mle(i, exp)))
                        } else {
                            Err(TypeError::Mle(kctx.clone(), vctx.clone(), tv))
                        }
                    },
                    _ => Err(TypeError::Mle(kctx.clone(), vctx.clone(), tv))
                }
            },

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CAExp::Vec(mut v, _) => {
                match v.0.pop() {
                    None => Err(TypeError::VecEmpty(kctx.clone(), vctx.clone())),
                    Some(h) => {
                        let th = h.infer(kctx, fctx, vctx, subs)?;
                        let mut t = th.proj2();
                        let mut typeds = Vec::new();
                        // Unify all elements of vector [v] into type [t]
                        for x in v.into_iter() {
                            let tx = x.infer(kctx, fctx, vctx, subs)?;
                            t = CTyp::unify_equ(t.clone(), tx.proj2(), kctx, subs)
                                .map_err(|e| TypeError::VecInner(kctx.clone(), vctx.clone(), th.clone(), tx, e))?;
                            // Use [t] as the type of element [tx] to ensure it is the
                            // representative of the equivalence class
                            typeds.push(tx.traverse2(&mut |_| Ok(t))?);
                        }
                        Ok(TAExp::Vec(AExps(typeds), CTyp::vec(t, typeds.len())))
                    }
                }
            }

            // Handle +
            CAExp::Bin(BinOp::Add, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let t = CTyp::unify_add(ta.proj2(), tb.proj2(), kctx, subs)
                            .map_err(|e| TypeError::Add(kctx.clone(), vctx.clone(), *ta, *tb, e))?;
                Ok(TAExp::Bin(BinOp::Add, ta, tb, t))
            }

            // Handle -
            CAExp::Bin(BinOp::Sub, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let t = CTyp::unify_sub(ta.proj2(), tb.proj2(), kctx, subs)
                            .map_err(|e| TypeError::Sub(kctx.clone(), vctx.clone(), *ta, *tb, e))?;
                Ok(TAExp::Bin(BinOp::Sub, ta, tb, t))
            }

            // Handle *
            CAExp::Bin(BinOp::Mul, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let t = CTyp::unify_mul(ta.proj2(), tb.proj2(), kctx, subs)
                            .map_err(|e| TypeError::Mul(kctx.clone(), vctx.clone(), *ta, *tb, e))?;
                Ok(TAExp::Bin(BinOp::Mul, ta, tb, t))
            }

            // Handle /
            CAExp::Bin(BinOp::Div, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let t = CTyp::unify_div(ta.proj2(), tb.proj2(), kctx, subs)
                            .map_err(|e| TypeError::Div(kctx.clone(), vctx.clone(), *ta, *tb, e))?;
                Ok(TAExp::Bin(BinOp::Div, ta, tb, t))
            }

            // Handle ^
            CAExp::Bin(BinOp::Pow, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let t = CTyp::unify_pow(ta.proj2(), tb.proj2(), kctx, subs)
                            .map_err(|e| TypeError::Pow(kctx.clone(), vctx.clone(), *ta, *tb, e))?;
                Ok(TAExp::Bin(BinOp::Pow, ta, tb, t))
            }

            // Handle .
            CAExp::Bin(BinOp::Dot, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let t = CTyp::unify_dot(ta.proj2(), tb.proj2(), kctx, subs)
                            .map_err(|e| TypeError::Dot(kctx.clone(), vctx.clone(), *ta, *tb, e))?;
                Ok(TAExp::Bin(BinOp::Dot, ta, tb, t))
            }

            // Handle ++
            CAExp::Bin(BinOp::Concat, a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                match (ta.proj2(), tb.proj2()) {
                    (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                        let c = CTyp::unify_equ(a.clone(), b.clone(), kctx, subs)
                            .map_err(|e| TypeError::Concat(kctx.clone(), vctx.clone(), *ta, *tb, Opt::some(e)))?;
                        Ok(TAExp::Bin(BinOp::Concat, ta, tb, CTyp::Vec(Box::new(c), x + y)))
                    },
                    (_, _) => Err(TypeError::Concat(kctx.clone(), vctx.clone(), *ta, *tb, Opt::none()))
                }
            }

            // Range expression
            CAExp::Range(r, _) =>
                // Infer the type of the range expression as a vector of sizes
                Ok(TAExp::Range(r.clone(), CTyp::vec(CTyp::Fin(r.clone()), r.get_size()))),

            // Map comprehension
            CAExp::Map(x, id, r, _) => {
                // Type infer the range expression
                let tr = r.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;

                // Clone the context
                let mut innerctx = vctx.clone();

                match tr.proj2() {
                    CTyp::Vec(box inner, size) => {
                        innerctx.insert(id, inner);
                        let tx =
                            x.traverse1(&mut |x| x.infer(kctx, fctx, &mut innerctx, subs))?;
                        Ok(TAExp::Map(tx, id, tr, CTyp::vec(tx.proj2(), size)))
                    },
                    typ => Err(TypeError::Map(kctx.clone(), innerctx, *x, id, *tr))
                }
            }

            // Variable context lookup
            CAExp::Var(id, _) => {
                let v = vctx.get(&id).ok_or(TypeError::VarNotFound(id, vctx.clone()))?;
                Ok(TAExp::Var(id.clone(), v.clone()))
            },

            // Random oracle challenge
            CAExp::Challenge(t, _) => Ok(TAExp::Challenge(t.clone(), t)),

            // Group generator
            CAExp::Gen(t, _) => {
                let k = kctx.get(&t).ok_or(
                    TypeError::Gen(kctx.clone(), vctx.clone(), t, Opt::some(UnifyError::KindNotFound(t, kctx.clone()))))?;
                if k.is_group() {
                    Ok(TAExp::Gen(t.clone(), CTyp::Base(t)))
                } else {
                    Err(TypeError::Gen(kctx.clone(), vctx.clone(), t, Opt::none()))
                }
            }

            // Interpolation of points into a univariate polynomial
            CAExp::Interpolate(a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                match (ta.proj2(), tb.proj2()) {
                    (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m => {
                        // Unify inner types [a] and [b]
                        let t = CTyp::unify_equ(a.clone(), b.clone(), kctx, subs)
                                .map_err(|e| TypeError::Interp(kctx.clone(), vctx.clone(), *ta, *tb, Opt::some(e)))?;

                        // Only interpolate vectors of fields
                        if let CTyp::Base(a) = t {
                            let k = kctx.get(&a).ok_or(UnifyError::KindNotFound(a, kctx.clone()))
                                .map_err(|e| TypeError::Interp(kctx.clone(), vctx.clone(), *ta, *tb, Opt::some(e)))?;
                            if k.is_field() {
                                Ok(TAExp::Interpolate(ta, tb, CTyp::Uni(a, n)))
                            } else {
                                Err(TypeError::Interp(kctx.clone(), vctx.clone(), *ta, *tb, Opt::none()))
                            }
                        } else {
                            Err(TypeError::Interp(kctx.clone(), vctx.clone(), *ta, *tb, Opt::none()))
                        }
                    },
                    (_, _) => Err(TypeError::Interp(kctx.clone(), vctx.clone(), *ta, *tb, Opt::none()))
                }
            },

            // Random access memory
            CAExp::Ram(v, i, _) => {
                let tv = v.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let ti = i.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                match (tv.proj2(), ti.proj2()) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(m)) if m.end < n =>
                            Ok(TAExp::Ram(tv, ti, typ.clone())),
                    (_, _) => Err(TypeError::Ram(kctx.clone(), vctx.clone(), *tv, *ti))
                }
            }

            // Function application
            CAExp::App(id, params, _) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, vctx, subs))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.into_iter().filter_map(|(fid, sig)|
                    // If the function name matches
                    if id == fid {
                        // Create new alias substitution context, we do not want to polute
                        // [subs] with aliases that fail to unify.
                        let mut nsubs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs =
                            sig.unify_all(
                                typed_params.into_iter().map(|x| x.proj2()).collect(),
                                kctx, &mut nsubs).ok()?;
                        Some((vs, nsubs))
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::AppMultiple(fctx.clone(), id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::FuncNotFound(fctx.clone(), id, typed_params))
                } else {
                    let (sig, nsubs) = matching_sigs[0];
                    subs.union_equ(&mut nsubs);
                    Ok(TAExp::App(id, typed_params, sig.ret().clone()))
                }
            }

            CAExp::Assert(assert, _) => {
                let tassert = assert.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                if tassert.proj2() != CTyp::bool() {
                    Err(TypeError::Assert(kctx.clone(), vctx.clone(), *tassert, Opt::some(UnifyError::NotBoolean(tassert.proj2()))))
                } else {
                    Ok(TAExp::Assert(tassert, CTyp::bool()))
                }
            }

            CAExp::Verify(assert, _) => {
                let tassert = assert.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                if tassert.proj2() != CTyp::bool() {
                    Err(TypeError::Verify(kctx.clone(), vctx.clone(), *tassert, Opt::some(UnifyError::NotBoolean(tassert.proj2()))))
                } else {
                    Ok(TAExp::Verify(tassert, CTyp::bool()))
                }
            }

            CAExp::Let(var, right, _) => {
                let tright = right.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                vctx.insert(var, tright.proj2());
                Ok(TAExp::Let(var, tright, tright.proj2()))
            },

            CAExp::Log(var, right, _) => {
                let tright = right.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                vctx.insert(var, tright.proj2());
                Ok(TAExp::Log(var, tright, tright.proj2()))
            },
        }
    }
}

/// Type inference for [CAExp]
impl Typeable for CAExps {
    type Output = TAExps;
    fn infer(self,  kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>,
        vctx: &mut Ctx<Vid, CTyp>, subs: &mut AliasSubsts) -> Result<Self::Output, TypeError> {
        self.aexps_traverse(&mut |x| x.infer(kctx, fctx, vctx, subs))
    }
}

/// Type inference for [BExp] with type context [ctx]
impl Typeable for CBExp {
    type Output = TBExp;
    fn infer(self, kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>,
        vctx: &mut Ctx<Vid, CTyp>, subs: &mut AliasSubsts) -> Result<TBExp, TypeError> {
        match self {
            CBExp::Equ(a, b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                CTyp::unify_equ(ta.proj2(), tb.proj2(), kctx, subs)
                    .map_err(|e| TypeError::Equ(kctx.clone(), vctx.clone(), ta.clone(), tb.clone(), e))?;
                Ok(TBExp::Equ(ta, tb, CTyp::bool()))
            }
            CBExp::Contains(a, b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                match (ta.proj2(), tb.proj2()) {
                    (x, CTyp::Vec(box a, n)) => {
                        let t = CTyp::unify_equ(x, a, kctx, subs)
                            .map_err(|e| TypeError::Contains(kctx.clone(), vctx.clone(), ta.clone(), tb.clone(), Opt::some(e)))?;
                        Ok(TBExp::Contains(ta, tb, CTyp::bool()))
                    },
                    (_, _) => Err(TypeError::Contains(kctx.clone(), vctx.clone(), ta.clone(), tb.clone(), Opt::none())),
                }
            }
            CBExp::App(id, params, _) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, vctx, subs))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.into_iter().filter_map(|(fid, sig)|
                    // If the function name matches
                    if id == fid {
                        // Create new alias substitution context, we do not want to polute
                        // [subs] with aliases that fail to unify.
                        let mut nsubs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs =
                            sig.unify_all(
                                typed_params.into_iter().map(|x| x.proj2()).collect(),
                                kctx, &mut nsubs).ok()?;
                        Some((vs, nsubs))
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::AppMultiple(fctx.clone(), id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::FuncNotFound(fctx.clone(), id, typed_params))
                } else {
                    let (sig, nsubs) = matching_sigs[0];
                    subs.union_equ(&mut nsubs);
                    Ok(TBExp::App(id, typed_params, sig.ret().clone()))
                }
            }
            CBExp::And(a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                Ok(TBExp::And(ta, tb, CTyp::bool()))
            },
            CBExp::Or(a, b, _) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                Ok(TBExp::Or(ta, tb, CTyp::bool()))
            }
        }
    }
}

/// Type inference for Decl (annotate each AST node with the type)
impl<A: fmt::Display> Typeable<A> for Decl<A> {
    type Output<Z> = Decl<Z>;
    type MutContext = Constraints;
    type ImContext = ();
    fn infer(self, _: &(), constr: &mut Constraints) -> Result<TDecl<A>, TypeError<A>> {
        match self {
            Decl::Proto {
                name,
                generics,
                args,
                principal,
                relation,
                body,
                assert
            } => {
                // Create a new context with generics and their kinds
                let mut ctx = TypCtx::from(generics.clone());

                // Append the argument types to typecontext (a: T)
                for Arg { id, typ, .. } in args.iter() {
                    ctx.add_var(id, typ);
                }

                // Type annotate the body
                let typed_body = body.infer(&ctx, constr)?;

                // Type annotate the relation
                let typed_relation = relation.infer(&ctx, constr)?;

                // Type annotate the assert
                let typed_assert = assert.infer(&ctx, constr)?;

                Ok(Decl::Proto {
                    name,
                    generics,
                    args,
                    principal,
                    relation: typed_relation,
                    body: typed_body,
                    assert: typed_assert,
                })
            }
            Decl::Func {
                name,
                generics,
                args,
                typ,
                body,
            } => {
                // Create a new context with generics and their kinds
                let mut ctx = TypCtx::from(generics.clone());

                // Append the argument types to typecontext (a: T)
                for Arg { id, typ, .. } in args.iter() {
                    ctx.add_var(id, typ);
                }

                // Type annotate the body
                let typed_body = body.infer(&ctx, constr)?;

                // Type check the return type
                let ft = Typ::unify_equ(typed_body.get_type().clone(), typ.clone(), &ctx, constr)?;

                Ok(Decl::Func {
                    name,
                    generics,
                    args,
                    typ: ft,
                    body: typed_body
                })
            }
        }
    }
}

/// Type inference for Modules.
/// Annotate each AST node with the type and each decl with the
/// constraints.
impl<A: fmt::Display, B> Typeable<A> for Module<A, B> {
    type Output<Z> = Module<Z, (B, Constraints)>;
    type ImContext = ();
    type MutContext = ();
    fn infer(self, _: &(), _: &mut ()) -> Result<TModule<A, B>, TypeError<A>> {
        let mut decls = Vec::new();
        for (decl, ann) in self.0.into_iter() {
            // Fresh constraints for each declaration (template polymorphism)
            let mut constr = Constraints::new();
            // Type annotate the declaration
            decls.push((decl.infer(&(), &mut constr)?, (ann, constr)));
        }
        Ok(Module(decls))
    }
}

