#![allow(refining_impl_trait)]
use share::{Ctx, Set, log2};
use share::traversal::ToTraversal1;
use crate::id::{Fid, Tid, Gen, TidTraversal, Vid};
use crate::exp::{BinOp, CAExp, CExp, CAExps, TAExp, TAExps, CBExp, TBExp};
use crate::decl::{CDecl, TDecl, DeclTraversal};
use crate::module::{UModule, TModule};
use crate::typ::unify::UnifyError;
use crate::typ::lub::{Lub, LubError};
use crate::typ::sig::Sig;
use crate::typ::AliasSubsts;
use crate::range::{Range, RangeError};
use crate::typ::{CTyp, Nothing, Kind};
use thiserror::Error;

pub trait Typeable {
    type Output;
    type Context;
    fn infer(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>, inf: &mut Self::Context) -> Result<Self::Output, TypeError>;
}

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

    #[error("ChallengeError: Only challenges returning field elements are allowed: {0}, {1} |- challenge< {2} : {3} >")]
    Challenge(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Tid, Kind),

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

    #[error(transparent)]
    Lub(#[from] LubError),
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
    pub fn lub(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: CExp, l: LubError) -> Self {
        TypeError::next(kctx, vctx, e, TypeError::from(l))
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
    pub fn challenge(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, t: Tid, k: &Kind) -> Self {
        TypeError::Challenge(kctx.clone(), vctx.clone(), t, k.clone())
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

/// Type inference for expressions, helper object
#[derive(Clone)]
pub struct InferenceContext {
    pub vctx: Ctx<Vid, CTyp>,        // Variable context Vid -> CTyp
    pub subs: Ctx<Fid, AliasSubsts>  // Substitutions of type variables
}

/// Type inference for [CAExp]
impl InferenceContext {
    pub fn new() -> Self {
        InferenceContext {
            vctx: Ctx::new(),
            subs: Ctx::new()
        }
    }
}

/// Type inference for [CAExp]
impl Typeable for CAExp {
    type Output = TAExp;
    type Context = InferenceContext;
    fn infer(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>, inf: &mut Self::Context) -> Result<Self::Output, TypeError> {
        match self.clone() {
            // Infer the type of a literal [n] as a Fin<n> type
            CAExp::Lit(n, _) =>
                Ok(TAExp::Lit(n, CTyp::fin(Range::singleton(n)))),

            // Infer the type of a univariate polynomial from its coefficients' vector
            CAExp::Coef(v, _) => {
                // Infer the type of its argument
                let tv : Box<TAExp> =
                    v.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(&kctx, &inf.vctx, self.into(), e))?;

                // It must be a vector of fields, or a vector of Fin
                match tv.typ() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::coef(kctx, &inf.vctx, &tv))?;
                        Ok(TAExp::Coef(tv, CTyp::uni(i, n)))
                    },
                    _ => Err(TypeError::coef(kctx, &inf.vctx, &tv))
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CAExp::Mle(v, _) => {
                // Infer the type of its argument
                let tv =
                    v.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                // It must be a vector of fields, or a vector of Fin
                match tv.typ() {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx)
                            .ok_or(TypeError::mle(kctx, &inf.vctx, &tv))?;

                        // MLEs come in sizes 2^n
                        let (exp, rem) = log2(n);
                        if rem == 0 {
                            Ok(TAExp::Mle(tv, CTyp::mle(i, exp)))
                        } else {
                            Err(TypeError::mle(kctx, &inf.vctx, &tv))
                        }
                    },
                    _ => Err(TypeError::mle(kctx, &inf.vctx, &tv))
                }
            },

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CAExp::Vec(v, _) => {
                let ts =
                    v.aexps_traverse(&mut |x| x.infer(kctx, fctx, inf))
                    .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                // Vectors cannot be empty for type inference to work
                if ts.is_empty() {
                    return Err(TypeError::vec_empty(kctx, &inf.vctx));
                }

                // For reference, the type of the first element
                let mut t = ts.0[0].typ();

                // Unify types of all elements in the vector to [t]
                for tx in ts.0[1..].iter() {
                    t = CTyp::lub_equ(t.clone(), tx.typ(), kctx)
                        .map_err(|e| TypeError::vec(kctx, &inf.vctx, tx, t, e.into()))?;
                }

                let n = ts.len();
                Ok(TAExp::Vec(ts, CTyp::vec(t, n)))
            }

            // Handle +
            CAExp::Bin(BinOp::Add, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let t = CTyp::lub_add(ta.typ(), tb.typ(), kctx)
                        .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Bin(BinOp::Add, ta, tb, t))
            }

            // Handle -
            CAExp::Bin(BinOp::Sub, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let t = CTyp::lub_sub(ta.typ(), tb.typ(), kctx)
                        .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Bin(BinOp::Sub, ta, tb, t))
            }

            // Handle *
            CAExp::Bin(BinOp::Mul, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let t = CTyp::lub_mul(ta.typ(), tb.typ(), kctx)
                        .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Bin(BinOp::Mul, ta, tb, t))
            }

            // Handle /
            CAExp::Bin(BinOp::Div, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let t = CTyp::lub_div(ta.typ(), tb.typ(), kctx)
                        .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Bin(BinOp::Div, ta, tb, t))
            }

            // Handle ^
            CAExp::Bin(BinOp::Pow, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let t = CTyp::lub_pow(ta.typ(), tb.typ(), kctx)
                        .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Bin(BinOp::Pow, ta, tb, t))
            }

            // Handle .
            CAExp::Bin(BinOp::Dot, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let t = CTyp::lub_dot(ta.typ(), tb.typ(), kctx)
                        .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Bin(BinOp::Dot, ta, tb, t))
            }

            // Handle ++
            CAExp::Bin(BinOp::Concat, a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                match (ta.typ(), tb.typ()) {
                    (CTyp::Vec(a, x), CTyp::Vec(b, y)) => {
                        // Type [a] and [b] should be the same ([c])
                        let c = CTyp::lub_equ(*a, *b, kctx)
                            .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;

                        // Add the sizes of the vectors
                        Ok(TAExp::Bin(BinOp::Concat, ta, tb, CTyp::vec(c, x + y)))
                    },
                    (_, _) => Err(TypeError::concat(kctx, &inf.vctx, *ta, *tb))
                }
            }

            // Range expression
            CAExp::Range(r, _) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start, r.step, r.end)
                    .map_err(|e| TypeError::range(kctx, &inf.vctx, r, e))?;

                Ok(TAExp::Range(rr.clone(), CTyp::vec(CTyp::Fin(rr), rr.get_size())))
            }

            // Map comprehension
            CAExp::Map(x, id, r, _) => {
                // Type infer the range expression
                let tr =
                    r.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                match tr.typ() {
                    CTyp::Vec(box inner, n) => {
                        // Clone the context
                        let mut innerctx = inf.clone();

                        // Add variable [id] to the context with type [inner]
                        innerctx.vctx.insert(&id, &inner);

                        // Type infer the expression [x] with the new context
                        let tx =
                            x.traverse1(&mut |x| x.infer(kctx, fctx, &mut innerctx))
                                .map_err(|e| TypeError::next(kctx, &innerctx.vctx, self.into(), e))?;

                        let typ = tx.typ();
                        Ok(TAExp::Map(tx, id, tr, CTyp::vec(typ, n)))
                    },
                    _ => Err(TypeError::map(kctx, &inf.vctx, *x, id, *tr))
                }
            }

            // Variable context lookup
            CAExp::Var(id, _) => {
                let v = inf.vctx.get(&id).ok_or(TypeError::var_not_found(&id, &&inf.vctx))?;
                Ok(TAExp::Var(id.clone(), v.clone()))
            },

            // Random oracle challenge
            CAExp::Challenge(t, _) => {
                // What kind of [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::lub(kctx, &inf.vctx, self.into(), LubError::kind_not_found(&t)))?;

                // Only allow challenges for field elements
                if k.is_field() {
                    Ok(TAExp::Challenge(t.clone(), CTyp::Base(t)))
                } else {
                    Err(TypeError::challenge(kctx, &inf.vctx, t, k))
                }
            }

            // Random number generator
            CAExp::Random(t, _) => {
                kctx.get(&t).ok_or(
                    TypeError::lub(kctx, &inf.vctx, self.into(), LubError::kind_not_found(&t)))?;

                Ok(TAExp::Random(t.clone(), CTyp::Base(t)))
            }

            // Group generator
            CAExp::Gen(t, _) => {
                // What kind of [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::lub(kctx, &inf.vctx, self.into(), LubError::kind_not_found(&t)))?;

                // Only generate elements of groups
                if k.is_group() {
                    Ok(TAExp::Gen(t.clone(), CTyp::Base(t)))
                } else {
                    Err(TypeError::gen(kctx, &inf.vctx, t, k))
                }
            }

            // Interpolation of points into a univariate polynomial
            CAExp::Interpolate(a, b, _) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                // Only field vectors can be interpolated
                match (ta.typ(), tb.typ()) {
                    (CTyp::Vec(box a, n), CTyp::Vec(box b, m)) if n == m => {
                        // Unify inner types [a] and [b]
                        let t = CTyp::lub_equ(a.clone(), b.clone(), kctx)
                                .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;

                        // Only interpolate vectors of fields
                        if let CTyp::Base(a) = t {
                            // What kind if [t]?
                            let k = kctx.get(&a)
                                .ok_or(TypeError::lub(kctx, &inf.vctx, self.into(), LubError::kind_not_found(&a)))?;

                            // Only interpolate elements of fields
                            if k.is_field() {
                                Ok(TAExp::Interpolate(ta, tb, CTyp::Uni(a, n)))
                            } else {
                                Err(TypeError::interp(kctx, &inf.vctx, *ta, *tb))
                            }
                        } else {
                            Err(TypeError::interp(kctx, &inf.vctx, *ta, *tb))
                        }
                    },
                    (_, _) => Err(TypeError::interp(kctx, &inf.vctx, *ta, *tb))
                }
            },

            // Random access into vectors
            CAExp::Ram(v, i, _) => {
                let tv =
                    v.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let ti =
                    i.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                // Must be a vector and a Fin type
                match (tv.typ(), ti.typ()) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(m)) if m.end < n =>
                            Ok(TAExp::Ram(tv, ti, typ.clone())),
                    (_, _) => Err(TypeError::ram(kctx, &inf.vctx, *tv, *ti))
                }
            }

            // Function application
            CAExp::App(id, params, _) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;


                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|(fid, sig)|
                    // If the function name matches
                    if &id == fid {
                        // Create new alias substitution context for this function [fid]
                        let mut subs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs = sig.clone().unify_typs(
                            typed_params.iter().map(|x| x.typ()).collect(), kctx, &mut subs).ok()?;

                        // Return substitutions
                        Some((vs, subs))
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::app_multiple(fctx, id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::func_not_found(fctx, id, typed_params))
                } else {
                    let (sig, subs) = &matching_sigs[0];
                    // Add substitutions to the global context indexed by the function name [id]
                    inf.subs.insert(&id, &subs);
                    Ok(TAExp::App(id, typed_params, sig.ret.clone()))
                }
            }

            CAExp::Assert(assert, _) => {
                let tassert =
                    assert.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Assert(tassert, CTyp::bool()))
            }

            CAExp::Verify(assert, _) => {
                let tassert =
                    assert.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                Ok(TAExp::Verify(tassert, CTyp::bool()))
            }

            CAExp::Let(var, right, _) => {
                let tright = right.traverse1(&mut |x| x.infer(kctx, fctx, inf))?;
                let typ = tright.typ();
                inf.vctx.insert(&var, &typ);
                Ok(TAExp::Let(var, tright, typ))
            },

            CAExp::Log(var, box right, _) => {
                let tright = right.infer(kctx, fctx, inf)?;
                let typ = tright.typ();
                inf.vctx.insert(&var, &typ);
                Ok(TAExp::Log(var, Box::new(tright), typ))
            },
        }
    }
}

/// Type inference for [CAExps]
impl Typeable for CAExps {
    type Output = TAExps;
    type Context = InferenceContext;
    fn infer(&self,  kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)> , inf: &mut Self::Context) -> Result<Self::Output, TypeError> {
        self.clone().aexps_traverse(&mut |x| x.infer(kctx, fctx, inf))
    }
}

/// Type inference for [CBExp]
impl Typeable for CBExp {
    type Output = TBExp;
    type Context = InferenceContext;
    fn infer(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>, inf: &mut Self::Context) -> Result<Self::Output, TypeError> {
        match self.clone() {
            CBExp::Equ(a, b) => {
                let ta =
                    a.infer(kctx, fctx, inf)
                    .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.infer(kctx, fctx, inf)
                    .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                // Values are equal when their types are equal (with unification)
                CTyp::lub_equ(ta.typ(), tb.typ(), kctx)
                    .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                Ok(TBExp::Equ(ta, tb))
            }
            CBExp::Contains(a, b) => {
                let ta =
                    a.infer(kctx, fctx, inf).map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.infer(kctx, fctx, inf).map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                match (ta.typ(), tb.typ()) {
                    (x, CTyp::Vec(box a, _)) => {
                        CTyp::lub_equ(x, a, kctx)
                            .map_err(|e| TypeError::lub(kctx, &inf.vctx, self.into(), e))?;
                        Ok(TBExp::Contains(ta, tb))
                    },
                    (_, _) => Err(TypeError::contains(kctx, &inf.vctx, ta, tb))
                }
            }
            CBExp::App(id, params) => {
                // type inference for each parameter
                let typed_params =
                    params.aexps_traverse(&mut |p| p.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|(fid, sig)|
                    // If the function name matches
                    if &id == fid {
                        // Create new alias substitution context for this function [fid]
                        let mut subs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs = sig.clone().unify_typs(
                            typed_params.iter().map(|x| x.typ()).collect(), kctx, &mut subs).ok()?;

                        // Return substitutions
                        Some((vs, subs))
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::app_multiple(fctx, id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::func_not_found(fctx, id, typed_params))
                } else {
                    let subs = &matching_sigs[0].1;
                    // Add substitutions to the global context indexed by the function name [id]
                    inf.subs.insert(&id, &subs);
                    Ok(TBExp::App(id, typed_params))
                }
            }
            CBExp::And(a, b) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                Ok(TBExp::And(ta, tb))
            },
            CBExp::Or(a, b) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                Ok(TBExp::Or(ta, tb))
            },
            CBExp::Not(a) => {
                let ta =
                    a.traverse1(&mut |x| x.infer(kctx, fctx, inf))
                        .map_err(|e| TypeError::next(kctx, &inf.vctx, self.into(), e))?;
                Ok(TBExp::Not(ta))
            },

        }
    }
}

/// Type inference for [Decl]
impl Typeable for CDecl {
    type Output = TDecl;
    type Context = InferenceContext;
    fn infer(&self, _: &Ctx<Tid, Kind>, fctx: &Set<(Fid, Sig)>, inf: &mut Self::Context) -> Result<Self::Output, TypeError> {
        // Clear variable context, every declaration has fresh variables
        inf.vctx.clear();

        // Create a new context from type vars
        let kctx = self.typevars().iter().map(|tvar| (tvar.id.clone(), tvar.kind.clone())).collect();

        // Create a new variable context from typed arguments
        inf.vctx =
            self.args().iter().map(|arg| (arg.id.clone(), arg.typ.clone())).collect();

        // Type inference on the body
        let typed_body =
            self.body().infer(&kctx, fctx, inf)
            .map_err(|e| TypeError::decl(&self.name(), e))?;

        match self.clone() {
            CDecl::Proto { name, typevars, args, relation, .. } => {
                // Type inference on the precondition relation
                let typed_relation =
                    relation.infer(&kctx, fctx, inf)
                    .map_err(|e| TypeError::decl(&name, e))?;

                Ok(TDecl::Proto {
                    name,
                    typevars,
                    args,
                    relation: typed_relation,
                    body: typed_body
                })
            }
            CDecl::Func { name, typevars, args, typ, .. } => {
                // Last expression gives us the type. Parser guarantees non-empty bodies, otherwise
                // there is a parser bug.
                let last = typed_body.0.last().unwrap();

                // Type check the return type
                let ft = CTyp::lub_equ(typ, last.typ(), &kctx)
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

/// Type inference for [Module]
impl Typeable for UModule {
    type Output = TModule;
    type Context = Nothing;
    fn infer(&self, _: &Ctx<Tid, Kind>, _: &Set<(Fid, Sig)>, _: &mut Nothing) -> Result<Self::Output, TypeError> {

        // Create a function context from the declarations
        let fctx: Set<(Fid, Sig)> = self.0.values()
            .map(| decl| (decl.name().clone(), decl.sig()))
            .collect();

        // Create an empty type inference context
        let mut inf = InferenceContext::new();

        // Type inference on the declarations makes a copy of the module
        let m =
            self.clone().decl_traverse(&mut |decl| decl.infer(&Ctx::new(), &fctx, &mut inf))?;

        // Replace all tid's with the alias representative, then we don't need to maintain the subs
        // context anymore
        Ok(m.into_iter().map(|((fid, arguments), declaration)|
            // If there are substitutions for this function
            if let Some(subs) = inf.subs.get(&fid).clone() {
                let mut decl = declaration.clone();
                let mut args = arguments.clone();

                // Capturing can happen...
                let tvs = declaration.typevars();
                for id in tvs.ids() {
                    if let Some(rid) = subs.get_repr(&id) {
                        if rid != id {
                            // Capturing could happen, shift [rid] to the next available id
                            if tvs.contains(&rid) {
                                let used_ids = Set::from(tvs.ids()).union(subs.keys());
                                let next = Tid::gen(&used_ids);
                                decl = decl.tid_traverse::<()>(&mut |x| Ok(if x == rid { next.clone() } else { x.clone() })).unwrap();
                                args = args.tid_traverse::<()>(&mut |x| Ok(if x == rid { next.clone() } else { x.clone() })).unwrap();
                            }
                            decl = decl.tid_traverse::<()>(&mut |x| Ok(if x == id { rid.clone() } else { x.clone() })).unwrap();
                            args = args.tid_traverse::<()>(&mut |x| Ok(if x == id { rid.clone() } else { x.clone() })).unwrap();
                        }
                    }
                }

                ((fid, args), decl)
            } else {
                ((fid, arguments), declaration)
            }).collect())
    }
}
