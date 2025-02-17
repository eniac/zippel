#![allow(refining_impl_trait)]

use share::{Ctx, Pretty, Traversable1};

use crate::lang::context::Ctx;
use crate::lang::id::{Fid, Tid, Vid};
use crate::lang::syntax::{TAExp, AExp, Assert, TAssert, Arg, TBExp, BExp, BinOp, Decl, TDecl, Module, TModule};
use crate::lang::traits::{Traversable1, Proj1, Pretty};
use crate::lang::types::sizes::{Constraints, Constr, ConstrError, Eval, EvalError, LogError};
use crate::lang::types::unify::Unify;
use crate::lang::types::{Typ, TypeVar, Nothing, Size, Bin, Kind, ArithmeticTypeError};
use crate::lang::types::context::{Sig, TypCtx, CtxError};
use thiserror::Error;

use pretty::{BoxAllocator, DocAllocator, DocBuilder};
use std::fmt;

#[derive(Error, PartialEq, Eq, Debug)]
pub enum TypeError<A: fmt::Display> {
    #[error(transparent)]
    Arithmetic(#[from] ArithmeticTypeError),
    #[error(transparent)]
    ConstrError(#[from] ConstrError),
    #[error(transparent)]
    CtxError(#[from] CtxError),
    #[error("VecInnerType: Container elements must have a base type {0} |- {1}")]
    VecInner(TypCtx, TAExp<A>),
    #[error("VecEmptyError: Cannot define empty vector or matrix {0} |- {1}")]
    VecEmpty(TypCtx, AExp<A>),
    #[error("CoefficientError: Argument to [coef] must be a vector type {0} |- {1}")]
    CoefError(TypCtx, TAExp<A>),
    #[error("MleError: Arguments to [mle] must be 2^n evaluations in bool hypercube")]
    MleErrorLog(#[from] LogError),
    #[error("MleError: Arguments to [mle] must be a vector type {0} |- {1}")]
    MleError(TypCtx, TAExp<A>),
    #[error("GenError: Type parameter to [gen] must be a Group kind {0} |- {1}")]
    GenError(TypCtx, TypeVar),
    #[error("MapError: Arguments to [map] must be a vector type {0} |- {1}")]
    MapError(TypCtx, TAExp<A>),
    #[error("SignatureTypeError: Unexpected arguments {1} to signature {0} |- {2} : {3}")]
    SigError(TypCtx, Vec<TAExp<A>>, Fid, Sig),
    #[error("ConcatenateError: Cannot concatenate {0} |- {1} ++ {2}")]
    ConcatError(TypCtx, TAExp<A>, TAExp<A>),
    #[error("InterpolateError: Cannot interpolate {0} |- interpolate ({1}, {2})")]
    InterpError(TypCtx, TAExp<A>, TAExp<A>),
    #[error("ReduceTypeError: Reduce expects a vector argument {0} |- {1}")]
    ReduceError(TypCtx, TAExp<A>),
    #[error("IndexOutOfBounds: Vector index out of bounds {0} |- {1}[{2}]")]
    IndexOutOfBounds(TypCtx, TAExp<A>, TAExp<A>),
}

impl<A> TAExp<A> {
    fn get_type(&self) -> &Typ {
        &self.proj1().1
    }
}

/// Infer a type with a typing context and typing constraints
pub trait Typeable<A: fmt::Display> {
    type Output<Z>;
    type MutContext;
    type ImContext;
    fn infer(self, ctx: &Self::ImContext, constr: &mut Self::MutContext) -> Result<Self::Output<(A, Typ)>, TypeError<A>>;
}

/// Type inference for [AExp] with type context [ctx]
impl<A: fmt::Display> Typeable<A> for AExp<A> {
    type Output<Z> = AExp<Z>;
    type MutContext = Constraints;
    type ImContext = TypCtx;
    fn infer(self, ctx: &Self::ImContext, constr: &mut Constraints) -> Result<Self::Output<(A, Typ)>, TypeError<A>> {
        match self {
            // Infer the type of a literal as a fin-type, coercions should make it into field/group
            AExp::Lit(n, a) => {
                let typ = Typ::fin(&Size::lit(n as i32));
                Ok(AExp::Lit(n, (a, typ)))
            }

            // Infer the type of a univariate polynomial
            AExp::Coef(box v, a) => {
                let typed = v.infer(ctx, constr)?;
                match typed.get_type().clone() {
                    Typ::Vec(box inner, size) => {
                        if let Some(base) = inner.get_base() {
                            if ctx.is_field(&base) {
                                return Ok(AExp::coef(typed, (a, Typ::uni(base, &size))));
                            }
                        }
                        return Err(TypeError::CoefError(ctx.clone(), typed));
                    }
                    typ => Err(TypeError::CoefError(ctx.clone(), typed))
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube
            // TODO: Implement matrix MLE inference
            AExp::Mle(box v, a) => {
                let typed = v.infer(ctx, constr)?;
                match typed.get_type().clone() {
                    Typ::Vec(box inner, size) => {
                        if let Some(base) = inner.get_base() {
                            if ctx.is_field(&base) {
                                // Size of vector has to be 2^b
                                let b = size.clone().hard_log2(constr)?;
                                return Ok(AExp::mle(typed, (a, Typ::mle(base, &Size::bin(b)))));
                            }
                        }
                        return Err(TypeError::MleError(ctx.clone(), typed));
                    }
                    typ => Err(TypeError::MleError(ctx.clone(), typed))
                }
            }

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            AExp::Vec(mut v, a) => {
                match v.pop() {
                    None => Err(TypeError::VecEmpty(ctx.clone(), AExp::Vec(v, a))),
                    Some(h) => {
                        let th = h.infer(ctx, constr)?;
                        let mut t = th.get_type().clone();
                        let mut typeds = Vec::new();
                        // Unify all elements of vector [v] into type [t]
                        for x in v.into_iter() {
                            let typedx = x.infer(ctx, constr)?;
                            t = Typ::unify_equ(t.clone(), typedx.get_type().clone(), ctx, constr)?;
                            typeds.push(typedx);
                        }
                        let len = typeds.len() as i32;
                        Ok(AExp::vec(typeds, (a, Typ::vec(&t, &Size::lit(len)))))
                    }
                }
            }
            // Handle +
            AExp::Bin(BinOp::Add, box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                Ok(AExp::add(ta, tb, (z, Typ::unify_add(typa, typb, ctx, constr)?)))
            }

            // Handle -
            AExp::Bin(BinOp::Sub, box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                Ok(AExp::sub(ta, tb, (z, Typ::unify_sub(typa, typb, ctx, constr)?)))
            }

            // Handle *
            AExp::Bin(BinOp::Mul, box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                Ok(AExp::mul(ta, tb,(z, Typ::unify_mul(typa, typb, ctx, constr)?)))
            }

            // Handle /
            AExp::Bin(BinOp::Div, box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                Ok(AExp::div(ta, tb,(z, Typ::unify_div(typa, typb, ctx, constr)?)))
            }

            // Handle ^
            AExp::Bin(BinOp::Pow, box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                Ok(AExp::pow(ta, tb, (z, Typ::unify_pow(typa, typb, ctx, constr)?)))
            }

            // Handle .
            AExp::Bin(BinOp::Dot, box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                Ok(AExp::dot(ta, tb,(z, Typ::unify_dot(typa, typb, ctx, constr)?)))
            }

            // Range expression
            AExp::Range(r, a) => {
                // Make sure range constraints hold
                constr.add_range(r.clone());

                // Infer the type of the range expression as a vector of sizes
                Ok(AExp::range(r.clone(), (a, Typ::vec(&Typ::Index(r.clone()), &r.get_size()))))
            }

            // Map comprehension
            AExp::Map(box x, id, box r, a) => {
                // Typeinfer the range expression
                let tr = r.infer(ctx, constr)?;

                // Clone the context
                let mut innerctx = ctx.clone();

                match tr.get_type().clone() {
                    Typ::Vec(box inner, size) => {
                        innerctx.add_var(&id, &inner);
                        let tx = x.infer(&innerctx, constr)?;
                        let typx = tx.get_type().clone();
                        Ok(AExp::map(tx, id, tr, (a, Typ::vec(&typx, &size))))
                    },
                    typ => Err(TypeError::MapError(ctx.clone(), tr))
                }
            }

            // Variable; context lookup
            AExp::Var(id, a) => Ok(AExp::Var(id.clone(), (a, ctx.get_var(&id)?))),

            // Random oracle challenge
            AExp::Challenge(t, a) => Ok(AExp::challenge(t.clone(), (a, t))),

            // Group generator
            AExp::Gen(t, a) => {
                let kind = ctx.get_kind(&t)?;
                if kind.is_group() {
                    Ok(AExp::Gen(t.clone(), (a, Typ::base(&t))))
                } else {
                    Err(TypeError::GenError(ctx.clone(), TypeVar::new(t, kind)))
                }
            }

            // Vector and matrix concatenation
            AExp::Concat(box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                match (typa, typb) {
                    // Vec<A> + Vec<B> = Vec<A + B>
                    (Typ::Vec(box a, x), Typ::Vec(box b, y)) => {
                        let c = Typ::unify_equ(a.clone(), b.clone(), ctx, constr)?;
                        Ok(AExp::concat(ta, tb, (z, Typ::vec(&c, &(x + y)))))
                    }
                    (_, _) => Err(TypeError::ConcatError(ctx.clone(), ta, tb))
                }
            },

            // Interpolation of points into a univariate polynomial
            AExp::Interpolate(box a, box b, z) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                let typa = ta.get_type().clone();
                let typb = tb.get_type().clone();
                match (typa, typb) {
                    (Typ::Vec(box a, x), Typ::Vec(box b, y)) => {
                        match (a, b) {
                            (Typ::Base(a), Typ::Base(b)) if a == b && ctx.is_field(&a) =>
                                Ok(AExp::interpolate(ta, tb, (z, Typ::uni(&a, &constr.add_eq(&x, &y)?)))),
                            (_, _) => Err(TypeError::InterpError(ctx.clone(), ta, tb))
                        }
                    },
                    (_, _) => Err(TypeError::InterpError(ctx.clone(), ta, tb))
                }
            },

            AExp::Index(box v, box i, ann) => {
                let tv = v.infer(ctx, constr)?;
                let ti = i.infer(ctx, constr)?;
                let typv = tv.get_type().clone();
                let typi = ti.get_type().clone();
                match (typv, typi) {
                    (Typ::Vec(box typ, n), Typ::Index(m)) => {
                        // Index within the bounds of the vector
                        constr.add_ge(&n, &m.end)?;
                        Ok(AExp::index(tv, ti, (ann, typ.clone())))
                    },
                    (_, _) => Err(TypeError::IndexOutOfBounds(ctx.clone(), tv, ti))
                }
            }

            // Function application
            AExp::App(id, params, ann) => {
                // Function signature
                let (args, ret) = ctx.get_func(&id)?;

                // type inference for each parameter
                let typed_params = params.traverse1(&mut |p| p.infer(ctx, constr))?;

                // The arity of the function must be the same as the number of arguments
                if args.len() != typed_params.len() {
                    return Err(TypeError::SigError(ctx.clone(), typed_params, id, Sig::Func { args, ret }));
                }

                // Clone the context to go inside the function
                let mut inner = ctx.clone();

                // Bind the arguments to the function's parameters
                for (arg, param) in args.iter().zip(typed_params.iter()) {
                    Typ::unify_equ(arg.clone(), param.get_type().clone(), &inner, constr)?;
                }
                Ok(AExp::app(id, typed_params, (ann, ret)))
            }

            // Reduce operation
            AExp::Reduce(op, box v, ann) => {
                let tv = v.infer(ctx, constr)?;
                if let Typ::Vec(box a, n) = tv.get_type() {
                    let c = match op {
                        BinOp::Add => Typ::unify_add(a.clone(), a.clone(), ctx, constr),
                        BinOp::Sub => Typ::unify_sub(a.clone(), a.clone(), ctx, constr),
                        BinOp::Mul => Typ::unify_mul(a.clone(), a.clone(), ctx, constr),
                        BinOp::Div => Typ::unify_div(a.clone(), a.clone(), ctx, constr),
                        BinOp::Pow => Typ::unify_pow(a.clone(), a.clone(), ctx, constr),
                        BinOp::Dot => Typ::unify_dot(a.clone(), a.clone(), ctx, constr),
                    }?;
                    Ok(AExp::reduce(op, tv, (ann, c)))
                } else {
                    Err(TypeError::ReduceError(ctx.clone(), tv))
                }
            }

            AExp::Assert(assert, box next, ann) => {
                let tassert = assert.infer(ctx, constr)?;
                let tnext = next.infer(ctx, constr)?;
                let typ = tnext.get_type().clone();
                Ok(AExp::assert(tassert, tnext, (ann, typ)))
            },

            AExp::Let(var, box val, box body, ann) => {
                let tval = val.infer(ctx, constr)?;
                let mut inner = ctx.clone();
                inner.add_var(&var.id, &tval.get_type());
                let tbody = body.infer(&inner, constr)?;
                let typ = tbody.get_type().clone();
                Ok(AExp::letx(var, tval, tbody, (ann, typ)))
            },

            AExp::Log(var, box val, box body, ann) => {
                let tval = val.infer(ctx, constr)?;
                let mut inner = ctx.clone();
                inner.add_var(&var.id, &tval.get_type());
                let tbody = body.infer(&inner, constr)?;
                let typ = tbody.get_type().clone();
                Ok(AExp::log(var, tval, tbody, (ann, typ)))
            },

        }
    }
}

/// Type inference for [BExp] with type context [ctx]
impl<A: fmt::Display> Typeable<A> for Assert<A> {
    type Output<Z> = Assert<Z>;
    type MutContext = Constraints;
    type ImContext = TypCtx;
    fn infer(self, ctx: &TypCtx, constr: &mut Constraints) -> Result<TAssert<A>, TypeError<A>> {
        let tcond = self.condition.infer(ctx, constr)?;
        Ok(Assert::new(self.principal, tcond))
    }
}

/// Type inference for [BExp] with type context [ctx]
impl<A: fmt::Display> Typeable<A> for BExp<A> {
    type Output<Z> = BExp<Z>;
    type MutContext = Constraints;
    type ImContext = TypCtx;
    fn infer(self, ctx: &TypCtx, constr: &mut Constraints) -> Result<TBExp<A>, TypeError<A>> {
        match self {
            BExp::Eq(a, b) => {
                let ta = a.infer(ctx, constr)?;
                let tb = b.infer(ctx, constr)?;
                Typ::unify_equ(ta.get_type().clone(), tb.get_type().clone(), ctx, constr)?;
                Ok(TBExp::eq(ta, tb))
            }
            BExp::App(id, params) => {
                // Function signature
                let (args, principal) = ctx.get_proto(&id)?;

                // type inference for each parameter
                let typed_params = params.traverse1(&mut |p| p.infer(ctx, constr))?;

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
                Ok(TBExp::and(a.infer(ctx, constr)?, b.infer(ctx, constr)?)),
            BExp::Or(box a, box b) =>
                Ok(TBExp::or(a.infer(ctx, constr)?, b.infer(ctx, constr)?)),
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

