#![allow(refining_impl_trait)]
use share::{Ctx, Set, log2};
use share::traversal::ToTraversal1;
use crate::id::{Fid, Tid, Vid};
use crate::exp::{BinOp, CAExp, CExp, CAExps, TAExp, TAExps, CBExp, TBExp};
use crate::decl::{CDecl, TDecl, CDecls, TDecls, DeclTraversal};
use crate::module::{UModule, TModule};
use crate::typ::unify::{Unify, UnifyError};
use crate::typ::sig::Sig;
use crate::typ::AliasSubsts;
use crate::range::{Range, RangeError};
use crate::typ::{CTyp, Nothing, Kind};
use thiserror::Error;

use std::fmt;

#[derive(Error, PartialEq, Debug)]
pub enum TypeError {
    #[error("TypeError: In declaration {0}:\n\n{1}")]
    Decl(Fid, Box<TypeError>),

    #[error("TypeError: In expression {0}, {1} |- {2} \n\n{3}")]
    Next(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp, Box<TypeError>),

    #[error("VecEmptyError: Cannot define empty vector {0}, {1} |- []")]
    VecEmpty(Ctx<Tid, Kind>, Ctx<Vid, CTyp>),

    #[error("VecTypeError: Vector elements must have the same type: {0}, {1} |- [ {2} not a {3} ]\n\n{4}")]
    Vec(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, CTyp, Box<TypeError>),

    #[error("CoefficientError: Argument to [coef] must be a vector of fields {0}, {1} |- coef {2}")]
    Coef(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),

    #[error("MleError: Arguments to [mle] must be a vector type with size a power of 2: {0}, {1} |- mle {2}")]
    Mle(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp),

    #[error("MapError: Arguments to [for] must be a vector type {0}, {1} |- [{2} for {3} in {4}]")]
    Map(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp, Vid, TAExp),

    #[error("GenError: Only group generators are allowed: {0}, {1} |- gen< {2} : {3} >")]
    Gen(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Tid, Kind),

    #[error("VarError: Variable {0} not found in context {1}")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),

    #[error("RangeError: Not a valid range expression {0}, {1} |- {2}\n\n{3}")]
    Range(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Range<usize>, RangeError),

    #[error("ConcatenateError: Expects two vectors with the same element types {0}, {1} |- {2} ++ {3}")]
    Concat(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),

    #[error("InterpolateError: Expects two field vectors with the same size {0} |- interpolate ( {1}, {2} )")]
    Interp(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),

    #[error("RamError: Index must be a Fin type within the bounds of the vector {0}, {1} |- {2} [ {3} ]")]
    Ram(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),

    #[error("AppMultipleError: Function has multiple matching definitions in context {0} |- {1} ( {2} )")]
    AppMultiple(Set<(Fid, Sig)>, Fid, TAExps),

    #[error("FuncNotFound: No matching definition found for function {0} |- {1} ( {2} )")]
    FuncNotFound(Set<(Fid, Sig)>, Fid, TAExps),

    #[error("ContainsError: Expects an element and a vector: {0}, {1} |- contains( {2} , {3} )")]
    Contains(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, TAExp, TAExp),

    #[error(transparent)]
    Unify(#[from] UnifyError),
}

impl<'a> TypeError {
    pub fn decl(id: &Fid, e: TypeError) -> Self {
        TypeError::Decl(id.clone(), Box::new(e))
    }
    pub fn next(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: CExp, t: Self) -> Self {
        TypeError::Next(kctx.clone(), vctx.clone(), e, Box::new(t))
    }
    pub fn unify(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: CExp, u: UnifyError) -> Self {
        TypeError::next(kctx, vctx, e, TypeError::from(u))
    }
    pub fn vec_empty(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VecEmpty(kctx.clone(), vctx.clone())
    }
    pub fn vec(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &TAExp, t: CTyp, r: TypeError) -> Self {
        TypeError::Vec(kctx.clone(), vctx.clone(), e.clone(), t.clone(), Box::new(r))
    }
    pub fn coef(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &TAExp) -> Self {
        TypeError::Coef(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn mle(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &TAExp) -> Self {
        TypeError::Mle(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn map(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: CAExp, id: Vid, r: TAExp) -> Self {
        TypeError::Map(kctx.clone(), vctx.clone(), e, id, r)
    }
    pub fn gen(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, t: Tid, k: &Kind) -> Self {
        TypeError::Gen(kctx.clone(), vctx.clone(), t, k.clone())
    }
    pub fn var_not_found(id: &Vid, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VarNotFound(id.clone(), vctx.clone())
    }
    pub fn range(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, r: Range<usize>, e: RangeError) -> Self {
        TypeError::Range(kctx.clone(), vctx.clone(), r, e)
    }
    pub fn concat(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: TAExp, b: TAExp) -> Self {
        TypeError::Concat(kctx.clone(), vctx.clone(), a, b)
    }
    pub fn interp(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: TAExp, b: TAExp) -> Self {
        TypeError::Interp(kctx.clone(), vctx.clone(), a, b)
    }
    pub fn ram(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: TAExp, b: TAExp) -> Self {
        TypeError::Ram(kctx.clone(), vctx.clone(), a, b)
    }
    pub fn app_multiple(fctx: &Set<(Fid, Sig)>, id: Fid, params: TAExps) -> Self {
        TypeError::AppMultiple(fctx.clone(), id, params)
    }
    pub fn func_not_found(fctx: &Set<(Fid, Sig)>, id: Fid, params: TAExps) -> Self {
        TypeError::FuncNotFound(fctx.clone(), id, params)
    }
    pub fn contains(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: TAExp, b: TAExp) -> Self {
        TypeError::Contains(kctx.clone(), vctx.clone(), a, b)
    }
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
    fn infer<'a>(self, kctx: &'a Ctx<Tid, Kind>, fctx: &'a Set<(Fid, Sig)>,
        vctx: &'a mut Ctx<Vid, CTyp>, subs: &'a mut AliasSubsts) -> Result<Self::Output, TypeError> {
        match self.clone() {
            // Infer the type of a literal [n] as a Fin<n> type
            CAExp::Lit(n, _) =>
                Ok(TAExp::Lit(n, CTyp::fin(Range::singleton(n)))),

            // Infer the type of a univariate polynomial from its coefficients' vector
            CAExp::Coef(v, _) => {
                // Infer the type of its argument
                let tv : Box<TAExp> =
                    v.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(&kctx, &vctx, (&self).into(), e))?;

                // It must be a vector of fields, or a vector of Fin
                match tv.typ() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::coef(kctx, vctx, &tv))?;
                        Ok(TAExp::Coef(tv, CTyp::uni(i, n)))
                    },
                    _ => Err(TypeError::coef(kctx, vctx, &tv))
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CAExp::Mle(v, _) => {
                // Infer the type of its argument
                let tv =
                    v.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                // It must be a vector of fields, or a vector of Fin
                match tv.typ() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx)
                            .ok_or(TypeError::mle(kctx, vctx, &tv))?;

                        // MLEs come in sizes 2^n
                        let (exp, rem) = log2(n);
                        if rem == 0 {
                            Ok(TAExp::Mle(tv, CTyp::mle(i, exp)))
                        } else {
                            Err(TypeError::mle(kctx, vctx, &tv))
                        }
                    },
                    _ => Err(TypeError::mle(kctx, vctx, &tv))
                }
            },

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CAExp::Vec(v, _) => {
                let ts =
                    v.aexps_traverse(&mut |x| x.infer(kctx, fctx, vctx, subs))
                    .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                // Vectors cannot be empty for type inference to work
                if ts.is_empty() {
                    return Err(TypeError::vec_empty(kctx, vctx));
                }

                // For reference, the type of the first element
                let mut t = ts.0[0].typ();

                // Unify types of all elements in the vector to [t]
                for tx in ts.iter() {
                    t = CTyp::unify_equ(t.clone(), tx.typ(), kctx, subs)
                        .map_err(|e| TypeError::vec(kctx, vctx, tx, t, e.into()))?;
                }

                let n = ts.len();
                Ok(TAExp::Vec(ts, CTyp::vec(t, n)))
            }

            // Handle +
            CAExp::Bin(BinOp::Add, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let t = CTyp::unify_add(ta.typ(), tb.typ(), kctx, subs)
                        .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Bin(BinOp::Add, ta, tb, t))
            }

            // Handle -
            CAExp::Bin(BinOp::Sub, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let t = CTyp::unify_sub(ta.typ(), tb.typ(), kctx, subs)
                        .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Bin(BinOp::Sub, ta, tb, t))
            }

            // Handle *
            CAExp::Bin(BinOp::Mul, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let t = CTyp::unify_mul(ta.typ(), tb.typ(), kctx, subs)
                        .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Bin(BinOp::Mul, ta, tb, t))
            }

            // Handle /
            CAExp::Bin(BinOp::Div, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let t = CTyp::unify_div(ta.typ(), tb.typ(), kctx, subs)
                        .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Bin(BinOp::Div, ta, tb, t))
            }

            // Handle ^
            CAExp::Bin(BinOp::Pow, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let t = CTyp::unify_pow(ta.typ(), tb.typ(), kctx, subs)
                        .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Bin(BinOp::Pow, ta, tb, t))
            }

            // Handle .
            CAExp::Bin(BinOp::Dot, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let t = CTyp::unify_dot(ta.typ(), tb.typ(), kctx, subs)
                        .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Bin(BinOp::Dot, ta, tb, t))
            }

            // Handle ++
            CAExp::Bin(BinOp::Concat, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                match (ta.typ(), tb.typ()) {
                    (CTyp::Vec(a, x), CTyp::Vec(b, y)) => {
                        // Type [a] and [b] should be the same ([c])
                        let c = CTyp::unify_equ(*a, *b, kctx, subs)
                            .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;

                        // Add the sizes of the vectors
                        Ok(TAExp::Bin(BinOp::Concat, ta, tb, CTyp::vec(c, x + y)))
                    },
                    (_, _) => Err(TypeError::concat(kctx, vctx, *ta, *tb))
                }
            }

            // Range expression
            CAExp::Range(r, _) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start, r.step, r.end)
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(TAExp::Range(rr.clone(), CTyp::vec(CTyp::Fin(rr), rr.get_size())))
            }

            // Map comprehension
            CAExp::Map(x, id, r, _) => {
                // Type infer the range expression
                let tr =
                    r.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                match tr.typ() {
                    CTyp::Vec(box inner, n) => {
                        // Clone the context
                        let mut innerctx = vctx.clone();

                        // Add variable [id] to the context with type [inner]
                        innerctx.insert(&id, &inner);

                        // Type infer the expression [x] with the new context
                        let tx =
                            x.traverse1(&mut |x| x.infer(kctx, fctx, &mut innerctx, subs))
                                .map_err(|e| TypeError::next(kctx, &innerctx, self.into(), e))?;

                        let typ = tx.typ();
                        Ok(TAExp::Map(tx, id, tr, CTyp::vec(typ, n)))
                    },
                    _ => Err(TypeError::map(kctx, vctx, *x, id, *tr))
                }
            }

            // Variable context lookup
            CAExp::Var(id, _) => {
                let v = vctx.get(&id).ok_or(TypeError::var_not_found(&id, &vctx))?;
                Ok(TAExp::Var(id.clone(), v.clone()))
            },

            // Random oracle challenge
            CAExp::Challenge(t, _) => Ok(TAExp::Challenge(t.clone(), t)),

            // Random number generator
            CAExp::Random(t, _) => Ok(TAExp::Random(t.clone(), t)),

            // Group generator
            CAExp::Gen(t, _) => {
                // What kind if [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::unify(kctx, vctx, (&self).into(), UnifyError::kind_not_found(&t)))?;

                // Only generate elements of groups
                if k.is_group() {
                    Ok(TAExp::Gen(t.clone(), CTyp::Base(t)))
                } else {
                    Err(TypeError::gen(kctx, vctx, t, k))
                }
            }

            // Interpolation of points into a univariate polynomial
            CAExp::Interpolate(a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                // Only field vectors can be interpolated
                match (ta.typ(), tb.typ()) {
                    (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m => {
                        // Unify inner types [a] and [b]
                        let t = CTyp::unify_equ(a.clone(), b.clone(), kctx, subs)
                                .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;

                        // Only interpolate vectors of fields
                        if let CTyp::Base(a) = t {
                            // What kind if [t]?
                            let k = kctx.get(&a)
                                .ok_or(TypeError::unify(kctx, vctx, (&self).into(), UnifyError::kind_not_found(&a)))?;

                            // Only interpolate elements of fields
                            if k.is_field() {
                                Ok(TAExp::Interpolate(ta, tb, CTyp::Uni(a, n)))
                            } else {
                                Err(TypeError::interp(kctx, vctx, *ta, *tb))
                            }
                        } else {
                            Err(TypeError::interp(kctx, vctx, *ta, *tb))
                        }
                    },
                    (_, _) => Err(TypeError::interp(kctx, vctx, *ta, *tb))
                }
            },

            // Random access into vectors
            CAExp::Ram(v, i, _) => {
                let tv =
                    v.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let ti =
                    i.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                // Must be a vector and a Fin type
                match (tv.typ(), ti.typ()) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(m)) if m.end < n =>
                            Ok(TAExp::Ram(tv, ti, typ.clone())),
                    (_, _) => Err(TypeError::ram(kctx, vctx, *tv, *ti))
                }
            }

            // Function application
            CAExp::App(id, params, _) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|(fid, sig)|
                    // If the function name matches
                    if &id == fid {
                        // Create new alias substitution context, we do not want to polute
                        // [subs] with aliases that fail to unify.
                        let mut nsubs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs =
                            sig.clone().unify_all(
                                typed_params.iter().map(|x| x.typ()).collect(),
                                kctx, &mut nsubs).ok()?;
                        Some((vs, nsubs))
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::app_multiple(fctx, id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::func_not_found(fctx, id, typed_params))
                } else {
                    let (sig, mut nsubs) = matching_sigs[0].clone();
                    subs.union_equ(&mut nsubs);
                    Ok(TAExp::App(id, typed_params, sig.ret().clone()))
                }
            }

            CAExp::Assert(assert, _) => {
                let tassert =
                    assert.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Assert(tassert, CTyp::bool()))
            }

            CAExp::Verify(assert, _) => {
                let tassert =
                    assert.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                Ok(TAExp::Verify(tassert, CTyp::bool()))
            }

            CAExp::Let(var, right, _) => {
                let tright = right.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))?;
                let typ = tright.typ();
                vctx.insert(&var, &typ);
                Ok(TAExp::Let(var, tright, typ))
            },

            CAExp::Log(var, box right, _) => {
                let tright = right.infer(kctx, fctx, vctx, subs)?;
                let typ = tright.typ();
                vctx.insert(&var, &typ);
                Ok(TAExp::Log(var, Box::new(tright), typ))
            },
        }
    }
}

/// Type inference for [CAExps]
impl Typeable for CAExps {
    type Output = TAExps;
    fn infer<'a>(self,  kctx: &'a Ctx<Tid, Kind>, fctx: &'a Set<(Fid, Sig)>,
        vctx: &'a mut Ctx<Vid, CTyp>, subs: &'a mut AliasSubsts) -> Result<Self::Output, TypeError> {
        self.aexps_traverse(&mut |x| x.infer(kctx, fctx, vctx, subs))
    }
}

/// Type inference for [BExp]
impl Typeable for CBExp {
    type Output = TBExp;
    fn infer<'a>(self, kctx: &'a Ctx<Tid, Kind>, fctx: &'a Set<(Fid, Sig)>,
        vctx: &'a mut Ctx<Vid, CTyp>, subs: &'a mut AliasSubsts) -> Result<TBExp, TypeError> {
        match self.clone() {
            CBExp::Equ(a, b) => {
                let ta =
                    a.infer(kctx, fctx, vctx, subs)
                    .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.infer(kctx, fctx, vctx, subs)
                    .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                // Values are equal when their types are equal (with unification)
                CTyp::unify_equ(ta.typ(), tb.typ(), kctx, subs)
                    .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                Ok(TBExp::Equ(ta, tb))
            }
            CBExp::Contains(a, b) => {
                let ta =
                    a.infer(kctx, fctx, vctx, subs).map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.infer(kctx, fctx, vctx, subs).map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                match (ta.typ(), tb.typ()) {
                    (x, CTyp::Vec(box a, _)) => {
                        CTyp::unify_equ(x, a, kctx, subs)
                            .map_err(|e| TypeError::unify(kctx, vctx, (&self).into(), e))?;
                        Ok(TBExp::Contains(ta, tb))
                    },
                    (_, _) => Err(TypeError::contains(kctx, vctx, ta, tb))
                }
            }
            CBExp::App(id, params) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|(fid, sig)|
                    // If the function name matches
                    if &id == fid {
                        // Create new alias substitution context, we do not want to polute
                        // [subs] with aliases that fail to unify.
                        let mut nsubs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs =
                            sig.clone().unify_all(
                                typed_params.iter().map(|x| x.typ()).collect(),
                                kctx, &mut nsubs).ok()?;
                        Some((vs, nsubs))
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::app_multiple(fctx, id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::func_not_found(fctx, id, typed_params))
                } else {
                    let (_, mut nsubs) = matching_sigs[0].clone();
                    subs.union_equ(&mut nsubs);
                    Ok(TBExp::App(id, typed_params))
                }
            }
            CBExp::And(a, b) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                Ok(TBExp::And(ta, tb))
            },
            CBExp::Or(a, b) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, vctx, subs))
                        .map_err(|e| TypeError::next(kctx, vctx, (&self).into(), e))?;
                Ok(TBExp::Or(ta, tb))
            }
        }
    }
}

/// Type inference for [Decl]
impl Typeable for CDecl {
    type Output = TDecl;
    fn infer<'a>(self, _: &'a Ctx<Tid, Kind>, fctx: &'a Set<(Fid, Sig)>,
        _: &'a mut Ctx<Vid, CTyp>, _: &'a mut AliasSubsts) -> Result<TDecl, TypeError> {
        match self.clone() {
            CDecl::Proto { name, typevars, args, relation, body } => {
                // Create a new context from type vars
                let kctx = typevars.to_ctx();

                // Create a new variable context from args
                let mut vctx = args.to_ctx();

                // Substitutions for type aliases are empty
                let mut subs = AliasSubsts::new();

                // Type inference on the body
                let typed_body = body.infer(&kctx, fctx, &mut vctx, &mut subs)
                    .map_err(|e| TypeError::decl(&name, e))?;

                // Type inference on the precondition relation
                let typed_relation = relation.infer(&kctx, fctx, &mut vctx, &mut subs)
                    .map_err(|e| TypeError::decl(&name, e))?;

                Ok(TDecl::Proto {
                    name,
                    typevars,
                    args,
                    relation: typed_relation,
                    body: typed_body
                })
            }
            CDecl::Func { name, typevars, args, body, typ } => {
                // Create a new context from type vars
                let kctx = typevars.to_ctx();

                // Create a new variable context from args
                let mut vctx = args.to_ctx();

                // Substitutions for type aliases are empty
                let mut subs = AliasSubsts::new();

                // Type inference on the body
                let typed_body = body.infer(&kctx, fctx, &mut vctx, &mut subs)?;

                // Last expression gives us the type
                let last = typed_body.0.last().unwrap();

                // Type check the return type
                let ft = CTyp::unify_equ(typ, last.typ(), &kctx, &mut subs)
                        .map_err(|e| TypeError::decl(&name, TypeError::from(e)))?;

                Ok(TDecl::Func {
                    name,
                    typevars,
                    args,
                    typ: ft,
                    body: typed_body
                })
            }
        }
    }
}

impl Typeable for CDecls {
    type Output = TDecls;
    fn infer<'a>(self, _: &'a Ctx<Tid, Kind>, fctx: &'a Set<(Fid, Sig)>,
        _: &'a mut Ctx<Vid, CTyp>, _: &'a mut AliasSubsts) -> Result<TDecls, TypeError> {
        self.decl_traverse(&mut |x| x.infer(&Ctx::new(), fctx, &mut Ctx::new(), &mut AliasSubsts::new()))
    }
}

/// Type inference for [Module]
impl Typeable for UModule {
    type Output = TModule;
    fn infer<'a>(self, _: &'a Ctx<Tid, Kind>, _: &'a Set<(Fid, Sig)>,
        _: &'a mut Ctx<Vid, CTyp>, _: &'a mut AliasSubsts) -> Result<TModule, TypeError> {

        // Create a function context from the declarations
        let fctx: Set<(Fid, Sig)> = self.0.values()
            .map(| decl| (decl.name().clone(), decl.sig()))
            .collect();

        // Type inference on the declarations
        Ok(self.decl_traverse(&mut |x| x.infer(&Ctx::new(), &fctx, &mut Ctx::new(), &mut AliasSubsts::new()))?)
    }
}
