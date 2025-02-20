#![allow(refining_impl_trait)]
use share::{Ctx, Set, Proj2, log2};
use crate::id::{Fid, Tid, Vid};
use crate::exp::{BinOp, CAExp, CAExps, TAExp, TAExps, CBExp, TBExp};
use crate::Decl;
use crate::typ::lub::{Lub, ArithmeticTypeError};
use crate::typ::sig::Sig;
use crate::typ::AliasSubsts;
use crate::range::Range;
use crate::typ::{CTyp, TypeVar, Kind};
use thiserror::Error;

use std::fmt;

#[derive(Error, PartialEq, Eq, Debug)]
pub enum TypeError {
    #[error(transparent)]
    Arithmetic(#[from] ArithmeticTypeError),
    #[error("VecInnerType: Container elements must have a base type {0}, {1} |- [ {2} ]")]
    VecInner(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),
    #[error("VecEmptyError: Cannot define empty vector {0}, {1} |- []")]
    VecEmpty(Ctx<Tid, Kind>, Ctx<Vid, CTyp>),
    #[error("CoefficientError: Argument to [coef] must be a vector of fields {0}, {1} |- coef {2}")]
    CoefError(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),
    #[error("MleError: Arguments to [mle] must be a vector type with size a power of 2: {0}, {1} |- mle {2}")]
    MleError(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),
    #[error("GenError: Type parameter to [gen] must be a Group kind {0}, {1} |- gen {2}")]
    GenError(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Tid),
    #[error("MapError: Arguments to [for] must be a vector type {0}, {1} |- [{2} for {3} in {4}]")]
    MapError(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp, Vid, TAExp),
    #[error("VarError: Variable {0} not found in context {1}")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),
    #[error("ConcatenateError: Cannot concatenate {0}, {1} |- {2} ++ {3}")]
    ConcatError(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),
    #[error("InterpolateError: Cannot interpolate {0} |- interpolate ({1}, {2})")]
    InterpError(Ctx<Tid, Kind>, Ctx<Tid, CTyp>, TAExp, TAExp),
    #[error("RamError: Index must be a Fin type within the bounds of the vector {0}, {1} |- {2} [ {3} ]")]
    RamError(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),
    #[error("AppMultipleError: Function has multiple matching definitions in context {0} |- {1} ( {2} )")]
    AppMultipleError(Set<(Fid, Sig)>, Fid, TAExps),
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
            // Infer the type of a literal as a Fin type
            CAExp::Lit(n, _) =>
                Ok(TAExp::Lit(n, CTyp::fin(Range::singleton(n)))),

            // Infer the type of a univariate polynomial from its coefficients' vector
            CAExp::Coef(box v, _) => {
                // Infer the type of its argument
                let tv = v.infer(kctx, fctx, vctx, subs)?;
                // It must be a vector of fields, or a vector of Fin
                match tv.proj2() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::CoefError(kctx.clone(), vctx.clone(), tv))?;
                        Ok(TAExp::Coef(Box::new(tv), CTyp::uni(i, n)))
                    },
                    _ => Err(TypeError::CoefError(kctx.clone(), vctx.clone(), tv))
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CAExp::Mle(box v, _) => {
                // Infer the type of its argument
                let tv = v.infer(kctx, fctx, vctx, subs)?;
                // It must be a vector of fields, or a vector of Fin
                match tv.proj2() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::MleError(kctx.clone(), vctx.clone(), tv))?;
                        let (exp, rem) = log2(n);
                        if rem == 0 {
                            Ok(CAExp::Mle(Box::new(tv), CTyp::mle(i, exp)))
                        } else {
                            Err(TypeError::MleErrorLog(kctx.clone(), vctx.clone(), tv))
                        }
                    },
                    _ => Err(TypeError::CoefError(kctx.clone(), vctx.clone(), tv))
                }
            },

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CAExp::Vec(mut v, _) => {
                match v.pop() {
                    None => Err(TypeError::VecEmpty(kctx.clone(), vctx.clone())),
                    Some(h) => {
                        let th = h.infer(kctx, fctx, vctx, subs)?;
                        let mut t = th.proj2();
                        let mut typeds = Vec::new();
                        // Unify all elements of vector [v] into type [t]
                        for x in v.into_iter() {
                            let typedx = x.infer(kctx, fctx, vctx, subs)?;
                            t = CTyp::unify_equ(t.clone(), typedx.proj2(), kctx)?;
                            typeds.push(typedx);
                        }
                        Ok(CAExp::Vec(typeds, CTyp::vec(Box::new(t), typeds.len())))
                    }
                }
            }

            // Handle +
            CAExp::Bin(BinOp::Add, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::add(ta, tb, CTyp::lub_add(ta.proj2(), tb.proj2(), kctx)?))
            }

            // Handle -
            CAExp::Bin(BinOp::Sub, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::sub(ta, tb, CTyp::lub_sub(ta.proj2(), tb.proj2(), kctx)?))
            }

            // Handle *
            CAExp::Bin(BinOp::Mul, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::mul(ta, tb, CTyp::lub_mul(ta.proj2(), tb.proj2(), kctx)?))
            }

            // Handle /
            CAExp::Bin(BinOp::Div, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::div(ta, tb, CTyp::lub_div(ta.proj2(), tb.proj2(), kctx)?))
            }

            // Handle ^
            CAExp::Bin(BinOp::Pow, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::pow(ta, tb, CTyp::lub_pow(ta.proj2(), tb.proj2(), kctx)?))
            }

            // Handle .
            CAExp::Bin(BinOp::Dot, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::dot(ta, tb, CTyp::lub_dot(ta.proj2(), tb.proj2(), kctx)?))
            }

            // Handle ++
            CAExp::Bin(BinOp::Concat, box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                match (ta.proj2(), tb.proj2()) {
                    (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                        let c = CTyp::unify_equ(a.clone(), b.clone(), kctx)?;
                        Ok(CAExp::concat(ta, tb, CTyp::Vec(c, x + y)))
                    },
                    (_, _) => Err(TypeError::ConcatError(kctx.clone(), vctx.clone(), ta, tb))
                }
            }

            // Range expression
            CAExp::Range(r, _) =>
                // Infer the type of the range expression as a vector of sizes
                Ok(CAExp::range(r.clone(), CTyp::vec(&CTyp::Index(r.clone()), &r.get_size()))),

            // Map comprehension
            CAExp::Map(box x, id, box r, _) => {
                // Type infer the range expression
                let tr = r.infer(kctx, fctx, vctx, subs)?;

                // Clone the context
                let mut innerctx = vctx.clone();

                match tr.proj2() {
                    CTyp::Vec(box inner, size) => {
                        innerctx.insert(id, inner);
                        let tx = x.infer(kctx, fctx, &mut innerctx, subs)?;
                        Ok(TAExp::map(tx, id, tr, CTyp::Vec(tx.proj2(), size)))
                    },
                    typ => Err(TypeError::MapError(kctx.clone(), innerctx, x, id, tr))
                }
            }

            // Variable; context lookup
            CAExp::Var(id, _) =>
                Ok(CAExp::Var(id.clone(), vctx.get(&id).ok_or(Err(TypeError::VarNotFound(id,vctx.clone())))?)),

            // Random oracle challenge
            CAExp::Challenge(t, _) => Ok(TAExp::challenge(t.clone(), t)),

            // Group generator
            CAExp::Gen(t, _) => {
                let k = kctx.get(&t).ok_or(Err(ArithmeticTypeError::KindNotFound(t, kctx.clone())))?;
                if k.is_group() {
                    Ok(TAExp::Gen(t.clone(), CTyp::base(&t)))
                } else {
                    Err(TypeError::GenError(kctx.clone(), vctx.clone(), t))
                }
            }

            // Interpolation of points into a univariate polynomial
            CAExp::Interpolate(box a, box b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                match (ta.proj2(), tb.proj2()) {
                    (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                        match CTyp::lub_equ(a.clone(), b.clone(), kctx)? {
                            CTyp::Base(a) => {
                                let k = kctx.get(a?).ok_or(Err(ArithmeticTypeError::KindNotFound(a, kctx.clone())))?;
                                if k.is_field() && x == y {
                                    Ok(CAExp::interpolate(ta, tb, CTyp::Uni(a, x)))
                                } else {
                                    Err(TypeError::InterpError(kctx.clone(), vctx.clone(), ta, tb))
                                }
                            }
                            _ => Err(TypeError::InterpError(kctx.clone(), vctx.clone(), ta, tb))
                        }
                    },
                    (_, _) => Err(TypeError::InterpError(kctx.clone(), vctx.clone(), ta, tb))
                }
            },

            CAExp::Ram(box v, box i, _) => {
                let tv = v.infer(kctx, fctx, vctx, subs)?;
                let ti = i.infer(kctx, fctx, vctx, subs)?;
                match (tv.proj2(), ti.proj2()) {
                    (CTyp::Vec(box typ, n), CTyp::Index(m)) if m < n =>
                            Ok(CAExp::ram(tv, ti, typ.clone())),
                    (_, _) => Err(TypeError::RamError(kctx.clone(), vctx.clone(), tv, ti))
                }
            }

            // Function application
            CAExp::App(id, params, _) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, vctx, subs))?;

                let matching_sigs = fctx.into_iter().filter_map(|(fid, sig)| {
                    match sig {
                        Sig::Func { args, ret } if fid == id => {
                            let vs = sig.lub_all(typed_params, kctx).ok()?;
                            Some(Sig::Func { args: vs, ret })
                        },
                        _ => None
                    }
                }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::AppMultipleError(fctx.clone(), id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::FuncNotFound(fctx.clone(), id, typed_params))
                } else {
                    let sig = matching_sigs[0];
                    Ok(CAExp::app(id, typed_params, sig.ret.clone()))
                }
            }

            CAExp::Assert(box assert, _) => {
                let tassert = assert.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::Assert(Box::new(tassert), CTyp::bool()))
            }

            CAExp::Verify(box assert, _) => {
                let tassert = assert.infer(kctx, fctx, vctx, subs)?;
                Ok(CAExp::Verify(Box::new(tassert), CTyp::bool()))
            }

            // TODO: Context extension on the Decl!
            CAExp::Let(var, box right, _) => {
                let tright = right.infer(kctx, fctx, vctx, subs)?;
                vctx.insert(var, tright.proj2());
                CAExp::letx(var, tright, tright.proj2())
            },

            CAExp::Log(var, box right, _) => {
                let tright = right.infer(kctx, fctx, vctx, subs)?;
                vctx.insert(var, tright.proj2());
                CAExp::logx(var, tright, tright.proj2())
            },

        }
    }
}

/// Type inference for [CAExp]
impl Typeable for CAExps {
    type Output = TAExps;
    fn infer(self,  kctx: &Ctx<Tid, Kind>, fctx: &Ctx<Fid, Sig>,
        vctx: &mut Ctx<Vid, CTyp>, subs: &mut AliasSubsts) -> Result<Self::Output, TypeError> {
        self.aexps_traverse(&mut |x| x.infer(kctx, fctx, vctx, subs))
    }
}

/// Type inference for [BExp] with type context [ctx]
impl Typeable for CBExp {
    type Output = TBExp;
    fn infer(self, kctx: &Ctx<Tid, Kind>, fctx: &Ctx<Fid, Sig>,
        vctx: &mut Ctx<Vid, CTyp>, subs: &mut AliasSubsts) -> Result<TBExp, TypeError> {
        match self {
            CBExp::Eq(a, b, _) => {
                let ta = a.infer(kctx, fctx, vctx, subs)?;
                let tb = b.infer(kctx, fctx, vctx, subs)?;
                CTyp::lub_equ(ta.proj2(), tb.proj2(), kctx)?;
                Ok(TBExp::eq(ta, tb))
            }
            CBExp::App(id, params, _) => {
                // Function signature
                let (args, principal) = ctx.get_proto(&id)?;

                // type inference for each parameter
                let typed_params = params.traverse1(&mut |p| p.infer(kctx, fctx, vctx, subs))?;

                // Clone the context to go inside the function
                let mut inner = ctx.clone();

                // The arity of the function must be the same as the number of arguments
                if args.len() != typed_params.len() {
                    return Err(TypeError::SigError(ctx.clone(), typed_params, id, Sig::Proto { args, principal }));
                }
                // Bind the arguments to the function's parameters
                for (arg, param) in args.iter().zip(typed_params.iter()) {
                    Typ::unify_equ(arg.clone(), param.get_type().clone(), &inner, constr)?;
                }
                Ok(BExp::app(id, typed_params))
            }
            BExp::And(box a, box b) =>
                Ok(TBExp::and(a.infer(kctx, fctx, vctx, subs)?, b.infer(kctx, fctx, vctx, subs)?)),
            BExp::Or(box a, box b) =>
                Ok(TBExp::or(a.infer(kctx, fctx, vctx, subs)?, b.infer(kctx, fctx, vctx, subs)?)),
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

