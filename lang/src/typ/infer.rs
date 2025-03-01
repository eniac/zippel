#![allow(refining_impl_trait)]
use share::{Ctx, Set, log2};
use share::traversal::{ToTraversal1, ToTraversal2};
use crate::id::{Fid, Tid, Vid};
use crate::exp::{BinOp, CAExp, CExp, CAExps, TAExp, TAExps, CBExp, TBExp, AExpTraversal};
use crate::decl::{CBody, TBody};
use crate::module::{TPolymod, CPolymod};
use crate::typ::unify::UnifyError;
use crate::typ::lub::{Lub, LubError};
use crate::sig::{Sig, CSig};
use crate::typ::AliasSubsts;
use crate::range::{Range, RangeError};
use crate::typ::{CTyp, CTyps, Nothing, Kind};
use thiserror::Error;

pub trait Typeable {
    type Output;
    type Context;
    fn infer_fwd(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<CTyp, TypeError>;
    fn infer_bwd(&self, typ: CTyp, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<Self::Output, TypeError>;
}

#[derive(Error, PartialEq, Debug)]
pub enum TypeError {
    #[error("TypeError: In declaration {0}:\n\n{1}")]
    Decl(Fid, Box<TypeError>),

    #[error("{0}\n\n{1}")]
    Next(Box<TypeError>, Box<TypeError>),

    #[error("TypeError: In expression {0}, {1} |- {2}")]
    CExp(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp),

    #[error("VecEmptyError: Cannot infer the type of the empty vector {0}, {1} |- []")]
    VecEmpty(Ctx<Tid, Kind>, Ctx<Vid, CTyp>),

    #[error("VecTypeError: Vector elements must have the same type: {0}, {1} |- {2} != {3} \n\n{4}")]
    Vec(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CTyp, CTyp, Box<TypeError>),

    #[error("CoefficientError: Argument to [coef] must be a vector of fields:\n{0}, {1} |- coef {2}")]
    Coef(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp),

    #[error("MleError: Arguments to [mle] must be a vector type with size a power of 2:\n{0}, {1} |- mle {2}")]
    Mle(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp),

    #[error("MapError: Arguments to [for] must be a vector type:\n{0}, {1} |- [{2} for {3} in {4}]")]
    Map(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp, Vid, CAExp),

    #[error("GenError: Only group generators are allowed:\n{0}, {1} |- gen< {2} : {3} >")]
    Gen(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Tid, Kind),

    #[error("ChallengeError: Only challenges returning field elements are allowed:\n {0}, {1} |- challenge< {2} : {3} >")]
    Challenge(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Tid, Kind),

    #[error("VarError: Variable {0} not found in context {1}")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),

    #[error("RangeError: Not a valid range expression:\n{0}, {1} |- {2}\n\n{3}")]
    Range(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, Range<usize>, RangeError),

    #[error("ConcatenateError: Expects two vectors with the same element types:\n {0}, {1} |- {2} ++ {3}")]
    Concat(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CTyp, CTyp),

    #[error("InterpolateError: Expects two field vectors with the same size:\n{0}, {1} |- interpolate ( {2}: {3}, {4}: {5} )")]
    Interp(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp, CTyp, CAExp, CTyp),

    #[error("RamError: Index must be a Fin type within the bounds of the vector:\n{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    Ram(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CAExp, CTyp, CAExp, CTyp),

    #[error("AppMultipleError: Function has multiple matching definitions in context\n{0} |- {1} ( {2} )")]
    AppMultiple(Set<CSig>, Fid, CTyps),

    #[error("FuncNotFound: No matching definition found for function:\n{0} |- {1} ( {2} )")]
    FuncNotFound(Set<CSig>, Fid, CTyps),

    #[error("ContainsError: Expects an element and a vector:\n{0}, {1} |- contains( {2} , {3} )")]
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
    pub fn next(a: Self, b: Self) -> Self {
        TypeError::Next(Box::new(a), Box::new(b))
    }
    pub fn unify(a: Self, u: UnifyError) -> Self {
        TypeError::next(a, TypeError::from(u))
    }
    pub fn lub(a: Self, l: LubError) -> Self {
        TypeError::next(a, TypeError::from(l))
    }
    pub fn caexp(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CAExp) -> Self {
        TypeError::CExp(kctx.clone(), vctx.clone(), e.into())
    }
    pub fn vec_empty(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VecEmpty(kctx.clone(), vctx.clone())
    }
    pub fn vec(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CTyp, t: &CTyp, r: TypeError) -> Self {
        TypeError::Vec(kctx.clone(), vctx.clone(), e.clone(), t.clone(), Box::new(r))
    }
    pub fn coef(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CAExp) -> Self {
        TypeError::Coef(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn mle(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CAExp) -> Self {
        TypeError::Mle(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn map(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: CAExp, id: Vid, r: CAExp) -> Self {
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
    pub fn concat(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: &CTyp, b: &CTyp) -> Self {
        TypeError::Concat(kctx.clone(), vctx.clone(), a.clone(), b.clone())
    }
    pub fn interp(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: &CAExp, ta: CTyp, b: &CAExp, tb: CTyp) -> Self {
        TypeError::Interp(kctx.clone(), vctx.clone(), a.clone(), ta, b.clone(), tb)
    }
    pub fn ram(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: &CAExp, ta: CTyp, b: &CAExp, tb: CTyp) -> Self {
        TypeError::Ram(kctx.clone(), vctx.clone(), a.clone(), ta, b.clone(), tb)
    }
    pub fn app_multiple(fctx: &Set<CSig>, id: Fid, params: CTyps) -> Self {
        TypeError::AppMultiple(fctx.clone(), id, params)
    }
    pub fn func_not_found(fctx: &Set<CSig>, id: Fid, params: CTyps) -> Self {
        TypeError::FuncNotFound(fctx.clone(), id, params)
    }
    pub fn contains(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: TAExp, b: TAExp) -> Self {
        TypeError::Contains(kctx.clone(), vctx.clone(), a, b)
    }
}

/// Type inference for [CAExp]
impl Typeable for CAExp {
    type Output = TAExp;
    type Context = Ctx<Vid, CTyp>;
    fn infer_fwd(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<CTyp, TypeError> {
        match self.clone() {
            // Infer the type of a literal [n] as a Fin<n> type
            CAExp::Lit(n, _) => Ok(CTyp::fin(Range::singleton(n))),

            // Infer the type of a univariate polynomial from its coefficients' vector
            CAExp::Coef(box v, _) => {
                // Infer the type of its argument
                let typ = v.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;

                // It must be a vector of fields, or a vector of Fin
                match typ {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::coef(kctx, &vctx, self))?;
                        Ok(CTyp::uni(i, n))
                    },
                    _ => Err(TypeError::coef(kctx, &vctx, self))
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CAExp::Mle(box v, _) => {
                // Infer the type of its argument
                let typ = v.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;

                // It must be a vector of fields, or a vector of Fin
                match typ {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or(TypeError::mle(kctx, &vctx, self))?;

                        // MLEs come in sizes 2^n
                        let (exp, rem) = log2(n);
                        if rem == 0 {
                            Ok(CTyp::mle(i, exp))
                        } else {
                            Err(TypeError::mle(kctx, &vctx, self))
                        }
                    },
                    _ => Err(TypeError::mle(kctx, &vctx, self))
                }
            },

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CAExp::Vec(v, _) => {
                let ts: CTyps =
                    v.into_iter().map(|aexp| aexp.infer_fwd(kctx, fctx, vctx)).collect::<Result<_, _>>()
                    .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;

                // Vectors cannot be empty for type inference to work
                if ts.is_empty() {
                    return Err(TypeError::vec_empty(kctx, &vctx));
                }

                // For reference, the type of the first element
                let mut t = ts.0[0];

                // Unify types of all elements in the vector to [t]
                for tx in ts.0[1..].iter() {
                    t = CTyp::lub_equ(t.clone(), tx.clone(), kctx)
                        .map_err(|e| TypeError::vec(kctx, &vctx, tx, &t, e.into()))?;
                }

                // Vector length
                let n = ts.len();

                // Generalize the type of the parameters
                Ok(CTyp::vec(t, n))
            }

            // Handle +
            CAExp::Bin(BinOp::Add, box a, box b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                CTyp::lub_add(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))
            }

            // Handle -
            CAExp::Bin(BinOp::Sub, a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                CTyp::lub_sub(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))
            }

            // Handle *
            CAExp::Bin(BinOp::Mul, a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                CTyp::lub_mul(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))
            }

            // Handle /
            CAExp::Bin(BinOp::Div, a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                CTyp::lub_div(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))
            }

            // Handle ^
            CAExp::Bin(BinOp::Pow, a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                CTyp::lub_pow(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))
            }

            // Handle .
            CAExp::Bin(BinOp::Dot, a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                CTyp::lub_dot(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))
            }

            // Handle ++
            CAExp::Bin(BinOp::Concat, a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                match (ta, tb) {
                    (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                        // Type [a] and [b] should be the same ([c])
                        let t = CTyp::lub_equ(a, b, kctx)
                            .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self), e))?;

                        // Add the sizes of the vectors
                        Ok(CTyp::vec(t, x + y))
                    },
                    (_, _) => Err(TypeError::concat(kctx, vctx, &ta, &tb))
                }
            }

            // Range expression
            CAExp::Range(r, _) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start, r.step, r.end)
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(CTyp::Fin(rr), rr.get_size()))
            }

            // Map comprehension
            CAExp::Map(box x, id, box r, _) => {
                // Type infer_fwd the range expression
                let tr = r.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;

                match tr {
                    CTyp::Vec(box inner, n) => {
                        // Clone the context
                        let mut innerctx = vctx.clone();

                        // Add variable [id] to the context with type [inner]
                        innerctx.insert(&id, &inner);

                        // Type infer_fwd the expression [x] with the new context
                        let tx = x.infer_fwd(kctx, fctx, &mut innerctx)
                                .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;

                        Ok(CTyp::vec(tx, n))
                    },
                    _ => Err(TypeError::map(kctx, vctx, x, id, x))
                }
            }

            // Variable context lookup
            CAExp::Var(id, _) =>
                vctx.get(&id).map(|x| x.clone()).ok_or(TypeError::var_not_found(&id, vctx)),

            // Random oracle challenge
            CAExp::Challenge(t, _) | CAExp::Random(t, _) => {
                // What kind of [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::lub(TypeError::caexp(kctx, vctx, self), LubError::kind_not_found(&t)))?;

                // Only allow challenges/random for field elements
                if k.is_field() {
                    Ok(CTyp::Base(t))
                } else {
                    Err(TypeError::challenge(kctx, vctx, t, k))
                }
            }

            // Group generator
            CAExp::Gen(t, _) => {
                // What kind of [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::lub(TypeError::caexp(kctx, vctx, self), LubError::kind_not_found(&t)))?;

                // Only generate elements of groups
                if k.is_group() {
                    Ok(CTyp::Base(t))
                } else {
                    Err(TypeError::gen(kctx, vctx, t, k))
                }
            }

            // Interpolation of points into a univariate polynomial
            CAExp::Interpolate(box a, box b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                // Must have a LUB; a vector of fields
                let t = CTyp::lub_equ(ta, tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::caexp(kctx, vctx, self),  e))?;

                // Only field vectors can be interpolated
                match t {
                    CTyp::Vec(box t, n) => {
                        // Must be a field
                        let t = t.to_field(kctx).ok_or(TypeError::interp(kctx, vctx, &a, ta, &b, tb))?;
                        Ok(CTyp::Uni(t, n))
                    },
                    _ => Err(TypeError::interp(kctx, vctx, &a, ta, &b, tb))
                }
            },

            // Random access into vectors
            CAExp::Ram(a, b, _) => {
                let ta = a.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;
                let tb = b.infer_fwd(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self),  e))?;

                // Must be a vector and a Fin type
                match (ta, tb) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(r)) if r.end < n => Ok(typ),
                    (_, _) => Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                }
            }

            // Function application
            CAExp::App(id, params, _) => {
                // type inference for each parameter
                let types: CTyps = params.into_iter()
                        .map(|p| p.infer_fwd(kctx, fctx, vctx)).collect::<Result<_, _>>()
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;


                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|sig|
                    // If the function name matches
                    if sig.name == id {
                        // Create new alias substitution context for this function [fid]
                        let mut subs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs = sig.clone()
                            .unify(&types, kctx, &mut subs)
                            .ok()?;
                        // Return new signature
                        Some(vs)
                    } else {
                        None
                    }).collect::<Vec<_>>();

                // Only one function shoud match
                if matching_sigs.len() > 1 {
                    Err(TypeError::next(TypeError::caexp(kctx, vctx, self), TypeError::app_multiple(fctx, id, types)))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::next(TypeError::caexp(kctx, vctx, self), TypeError::func_not_found(fctx, id, types)))
                } else {
                    let sig = &matching_sigs[0];
                    Ok(sig.ret.clone())
                }
            }

            CAExp::Assert(_, _) | CAExp::Verify(_, _) => Ok(CTyp::bool()),

            CAExp::Let(var, box right, _) | CAExp::Log(var, box right, _) => {
                let tright = right.infer_fwd(kctx, fctx, vctx)?;
                vctx.insert(&var, &tright);
                Ok(tright)
            },
        }
    }

    fn infer_bwd(&self, typ: CTyp, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<Self::Output, TypeError> {
        match (self.clone(), typ) {
            // Match the type of a literal [n]
            (CAExp::Lit(n, _), typ) => CAExp::Lit(n, typ),

            // Match the type of a univariate polynomial with the inner vector
            (CAExp::Coef(box v, _), CTyp::Uni(b, n)) => {
                let tv = v.infer_bwd(CTyp::vec(CTyp::base(b), n), kctx, fctx, vctx)?;
                Ok(TAExp::Coef(Box::new(tv), typ))
            },

            // Match the type of an MLE from 2^n evaluations in a bool hypercube to a vector
            (CAExp::Mle(box v, _), CTyp::Mle(b, n)) => {
                let tv = v.infer_bwd(CTyp::vec(CTyp::base(b), std::math::pow(2, n)), kctx, fctx, vctx)?;
                Ok(TAExp::Mle(Box::new(tv), typ))
            },

            // Match the type of a (nonempty) vector by unifying the types of its elements
            (CAExp::Vec(vs, _), CTyp::Vec(box b, n)) => {
                let tvs = vs.into_iter().map(|v| v.infer_bwd(b.clone(), kctx, fctx, vctx)).collect::<Result<_, _>>()?;
                Ok(TAExp::Vec(tvs, typ))
            },

            // Handle +
            (CAExp::Bin(BinOp::Add, box a, box b, _), typ) => {
                let ta = a.infer_bwd(typ.clone(), kctx, fctx, vctx)?;
                let tb = b.infer_bwd(typ.clone(), kctx, fctx, vctx)?;
                Ok(TAExp::Bin(BinOp::Add, Box::new(ta), Box::new(tb), typ))
            },
            // Handle -
            (CAExp::Bin(BinOp::Sub, box a, box b, _), typ) => {
                let ta = a.infer_bwd(typ.clone(), kctx, fctx, vctx)?;
                let tb = b.infer_bwd(typ.clone(), kctx, fctx, vctx)?;
                Ok(TAExp::Bin(BinOp::Sub, Box::new(ta), Box::new(tb), typ))
            },
            // WTF?????
            // Handle *
            (CAExp::Bin(BinOp::Mul, box a, box b, _), typ) => {
                let ta = a.infer_bwd(typ.clone(), kctx, fctx, vctx)?;
                let tb = b.infer_bwd(typ.clone(), kctx, fctx, vctx)?;
                Ok(TAExp::Bin(BinOp::Mul, Box::new(ta), Box::new(tb), typ))
            },
            _ => Err(TypeError::mle(kctx, vctx, self))
                },
                // Infer the type of its argument
                let typ = v.infer_bwd(typ, kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::caexp(kctx, vctx, self), e))?;

                // It must be a vector of fields, or a vector of Fin
                match typ {
                    CTyp::Vec(box b, n) => {
                        let i = b.to_field(kctx).ok_or
}

/// Type inference for [CAExps]
impl Typeable for CAExps {
    type Output = TAExps;
    type Context = Ctx<Vid, CTyp>;
    fn infer_fwd(&self,  kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<Self::Output, TypeError> {
        self.clone().aexp_traverse(&mut |x| x.infer_fwd(kctx, fctx, vctx))
    }
}

/// Type infer_fwdence for [CBExp]
impl Typeable for CBExp {
    type Output = TBExp;
    type Context = Ctx<Vid, CTyp>;
    fn infer_fwd(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<Self::Output, TypeError> {
        match self.clone() {
            CBExp::Equ(a, b) => {
                let ta =
                    a.infer_fwd(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                let tb =
                    b.infer_fwd(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;

                // Values are equal when their types are equal (with unification)
                CTyp::lub_equ(ta.typ(), tb.typ(), kctx)
                    .map_err(|e| TypeError::lub(kctx, &vctx, self.into(), e))?;
                Ok(TBExp::Equ(ta, tb))
            }
            CBExp::Contains(a, b) => {
                let ta =
                    a.infer_fwd(kctx, fctx, vctx).map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                let tb =
                    b.infer_fwd(kctx, fctx, vctx).map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;

                match (ta.typ(), tb.typ()) {
                    (x, CTyp::Vec(box a, _)) => {
                        CTyp::lub_equ(x, a, kctx)
                            .map_err(|e| TypeError::lub(kctx, &vctx, self.into(), e))?;
                        Ok(TBExp::Contains(ta, tb))
                    },
                    (_, _) => Err(TypeError::contains(kctx, &vctx, ta, tb))
                }
            }
            CBExp::App(id, params) => {
                // type infer_fwdence for each parameter
                let typed_params =
                    params.aexp_traverse(&mut |p| p.infer_fwd(kctx, fctx, vctx))
                        .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|sig|
                    // If the function name matches
                    if sig.name == id {
                        // Create new alias substitution context for this function [fid]
                        let mut subs = AliasSubsts::new();
                        // The argument types must match the parameter types
                        let vs = sig.clone()
                            .unify(typed_params.iter().map(|x| x.typ()).collect(), kctx, &mut subs)
                            .ok()?;

                        // Return new signature
                        Some(vs)
                    } else {
                        None
                    }).collect::<Vec<_>>();

                if matching_sigs.len() > 1 {
                    Err(TypeError::app_multiple(fctx, id, typed_params))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::func_not_found(fctx, id, typed_params))
                } else {
                    Ok(TBExp::App(id, typed_params))
                }
            }
            CBExp::And(a, b) => {
                let ta =
                    a.traverse1(&mut |x| x.infer_fwd(kctx, fctx, vctx))
                        .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer_fwd(kctx, fctx, vctx))
                        .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                Ok(TBExp::And(ta, tb))
            },
            CBExp::Or(a, b) => {
                let ta =
                    a.traverse1(&mut |x| x.infer_fwd(kctx, fctx, vctx))
                        .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                let tb =
                    b.traverse1(&mut |x| x.infer_fwd(kctx, fctx, vctx))
                        .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                Ok(TBExp::Or(ta, tb))
            },
            CBExp::Not(a) => {
                let ta =
                    a.traverse1(&mut |x| x.infer_fwd(kctx, fctx, vctx))
                        .map_err(|e| TypeError::next(kctx, &vctx, self.into(), e))?;
                Ok(TBExp::Not(ta))
            },

        }
    }
}

/// Type infer_fwdence for [Body]
impl Typeable for CBody {
    type Output = TBody;
    type Context = Ctx<Vid, CTyp>;
    fn infer_fwd(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<Self::Output, TypeError> {
        // Type infer_fwdence for each statement in the Body
        match self {
            CBody::Proto { relation, body } => {
                // First the relation
                let r = relation.infer_fwd(kctx, fctx, &mut vctx.clone())?;

                // Then the body
                let b = body.infer_fwd(kctx, fctx, &mut vctx.clone())?;
                Ok(TBody::Proto { relation: r, body: b })
            },
            CBody::Func { body } =>
                Ok(TBody::Func { body: body.infer_fwd(kctx, fctx, vctx)? })
        }
    }
}

/// Type infer_fwdence for a polymorphic module [CPolymod]
impl Typeable for CPolymod {
    type Output = TPolymod;
    type Context = Nothing;
    fn infer_fwd(&self, _: &Ctx<Tid, Kind>, _: &Set<CSig>, _: &mut Nothing) -> Result<Self::Output, TypeError> {

        // Create a function context from the declarations
        let fctx: Set<CSig> = self.0
            .iter()
            .map(| ((_, sig), _)| sig.clone())
            .collect();

        self.clone().into_iter().map(|((typevars, sig), body)| {
            // Make a kind context from typevars
            let kctx : Ctx<Tid, Kind> =
                typevars.iter().map(|tvar| (tvar.id.clone(), tvar.kind.clone())).collect();

            // Create a typed variable context from arguments
            let mut vctx : Ctx<Vid, CTyp> =
                sig.args.iter().map(|arg| (arg.id.clone(), arg.typ.clone())).collect();

            // Type infer_fwdence on the body
            let b = body.infer_fwd(&kctx, &fctx, &mut vctx)?;

            // Check last argument is the same as the return type

            let last = b.last().unwrap();
            let ft = CTyp::lub_equ(sig.ret.clone(), last.typ(), &kctx)
                .map_err(|e| TypeError::decl(&sig.name, TypeError::from(e)))?;

            let s = Sig { name: sig.name, args: sig.args, ret: ft };
            Ok(((typevars, s), b))

        }).collect::<Result<_, _>>()
    }
}

/// Unit tests for type infer_fwdence
#[cfg(test)]
mod tests {
    use super::*;
    use share::{Ctx, Set};
    use crate::id::{Fid, Tid, Vid};
    use crate::exp::{BinOp, UAExp, CAExp, CBExp, CAExps};
    use crate::typ::{CTyp, Kind};
    use crate::sig::CSig;
    use crate::arg::{Args, CArg};
    use crate::range::Range;
    use lazy_static::lazy_static;

    lazy_static! {
        static ref KIND_CTX: Ctx<Tid, Kind> = {
            let mut kctx = Ctx::new();
            // Add field type "F"
            kctx.insert(&Tid::from("F"), &Kind::Field);
            // Add group type "G"
            kctx.insert(&Tid::from("G"), &Kind::Group);
            kctx
        };

        static ref VAR_CTX: Ctx<Vid, CTyp> = {
            let mut vctx = Ctx::new();
            // Add variable "x" of type "F"
            vctx.insert(&Vid::from("x"), &CTyp::Base(Tid::from("F")));
            // Add variable "y" of type "F"
            vctx.insert(&Vid::from("y"), &CTyp::Base(Tid::from("F")));
            // Add vector variable "v" with element type "F" and length 5
            vctx.insert(&Vid::from("v"), &CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5));
            vctx
        };
    }

    // Tests for literals
    #[test]
    fn test_literal_infer_fwdence() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a literal expression "5"
        let lit = CAExp::lit(5);

        // Run type infer_fwdence
        let result = lit.infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        // Verify result
        assert!(result.is_ok());
        let typed_expr = result.unwrap();
        match typed_expr {
            TAExp::Lit(n, typ) => {
                assert_eq!(n, 5);
                assert_eq!(typ, CTyp::Fin(Range::singleton(5)));
            },
            _ => panic!("Expected a literal expression")
        }
    }

    // Tests for binary operations
    #[test]
    fn test_binary_add_infer_fwdence() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x + y
        let tadd = CAExp::bin(
            BinOp::Add,
            CAExp::varstr("x"),
            CAExp::varstr("y"),
        ).infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        if let TAExp::Bin(op, box a, box b, typ) = tadd.unwrap() {
            assert_eq!(op, BinOp::Add);
            // Check both operands are field types
            assert_eq!(a.typ(), CTyp::varstr("F"));
            assert_eq!(b.typ(), CTyp::varstr("F"));
            assert_eq!(typ, CTyp::varstr("F"));
        } else {
            panic!("Expected a binary addition expression")
        }
    }

    // Test for vector creation
    #[test]
    fn test_vector_infer_fwdence() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a vector expression [1, 2, 3]
        let tvec = CAExp::vec(
            vec![
                CAExp::lit(1),
                CAExp::lit(2),
                CAExp::lit(3),
            ]).infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        // Verify result
        if let TAExp::Vec(ts, typ) = tvec.unwrap() {
            assert_eq!(typ, CTyp::vec(CTyp::Fin(Range::new(1, 4)), 3));
            for t in ts.0.iter() {
                assert_eq!(t.typ(), CTyp::Fin(Range::new(1, 4)));
            }
        } else {
            panic!("Expected a vector expression")
        }
    }

    // Test for error: empty vector
    #[test]
    fn test_empty_vector_error() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an empty vector expression []
        let tresult =
            CAExp::vec(vec![]).infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        match tresult.unwrap_err() {
            TypeError::VecEmpty(_, _) => {}, // This is correct
            err => panic!("Expected VecEmpty error, got: \n\n\t{}", err)
        }
    }

    // Test for error: vector with different types
    #[test]
    fn test_vector_type_error() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a vector expression [1, 2, x]
        let tresult =
            CAExp::vec(vec![
                CAExp::lit(1),
                CAExp::lit(2),
                CAExp::varstr("x"),
            ]).infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        match tresult.unwrap_err() {
            TypeError::Vec(_, _, _, _, _) => {}, // This is correct
            err => panic!("Expected Vec error, got: \n\n\t{}", err)
        }
    }

    // Test interpolate
    #[test]
    fn test_interpolate_good() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an interpolation expression interpolate([1, 2, 3], [1, 2, 3])
        let tinterp = CAExp::interpolate(
            CAExp::vec(vec![
                CAExp::lit(1),
                CAExp::lit(2),
                CAExp::lit(3),
            ]),
            CAExp::vec(vec![
                CAExp::lit(4),
                CAExp::lit(5),
                CAExp::lit(6),
            ])).infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        // Verify result
        match tinterp {
            Ok(TAExp::Interpolate(box a, box b, typ)) => {
                assert_eq!(typ, CTyp::Uni(Tid::from("F"), 3));
                assert_eq!(a.typ(), CTyp::vec(CTyp::Fin(Range::new(1, 4)), 3));
                assert_eq!(b.typ(), CTyp::vec(CTyp::Fin(Range::new(4, 7)), 3));
            },
            Ok(e) => panic!("Expected an interpolation expression, got: \n\n{}", e),
            Err(err) => panic!("Expected an interpolation expression, got error: \n\n{}", err),
        }
    }

    // Test for error: interpolate with different types
    #[test]
    fn test_interpolate_type_error() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an interpolation expression interpolate([1, 2, 3], [1, 2, x])
        let tresult =
            CAExp::interpolate(
                CAExp::vec(vec![
                    CAExp::lit(1),
                    CAExp::lit(2),
                    CAExp::lit(3),
                ]),
                CAExp::vec(vec![
                    CAExp::lit(4),
                    CAExp::lit(5),
                    CAExp::varstr("x"),
                ])).infer_fwd(&KIND_CTX, &fctx, &mut vctx);

        match tresult.unwrap_err() {
            TypeError::Interp(_, _, _, _) => {}, // This is correct
            err => panic!("Expected Interp error, got: \n\n\t{}", err)
        }
    }
}
