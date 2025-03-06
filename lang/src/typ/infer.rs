#![allow(refining_impl_trait)]
use share::{Ctx, Set, log2};
use share::traversal::ToTraversal1;
use crate::id::{Fid, Tid, Vid};
use crate::ast::{BinOp, CExp, CBody};
use crate::typ::unify::UnifyError;
use crate::typ::lub::{Lub, LubError};
use crate::ast::sig::CSig;
use crate::typ::AliasSubsts;
use crate::typ::range::{Range, RangeError};
use crate::typ::{CTyp, CTyps, Kind};
use thiserror::Error;

pub trait Typeable {
    type Context;
    fn infer(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<CTyp, TypeError>;
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
    Coef(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp),

    #[error("MleError: Arguments to [mle] must be a vector type with size a power of 2:\n{0}, {1} |- mle {2}")]
    Mle(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp),

    #[error("MapError: Arguments to [for] must be a vector type:\n{0}, {1} |- [{2} for {3} in {4}]")]
    Map(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp, Vid, CExp),

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
    Interp(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("RamError: Index must be a Fin type within the bounds of the vector:\n{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    Ram(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("AppMultipleError: Function has multiple matching definitions in context\n{0} |- {1} ( {2} )")]
    AppMultiple(Set<CSig>, Fid, CTyps),

    #[error("FuncNotFound: No matching definition found for function:\n{0} |- {1} ( {2} )")]
    FuncNotFound(Set<CSig>, Fid, CTyps),

    #[error("ContainsError: Expects an element and a vector:\n{0}, {1} |- contains( {2}: {3} , {4}: {5} )")]
    Contains(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("BoolError: Expected boolean expression:\n{0}, {1} |- {2}")]
    Bool(Ctx<Tid, Kind>, Ctx<Vid, CTyp>, CExp),

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
    pub fn exp(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::CExp(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn vec_empty(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VecEmpty(kctx.clone(), vctx.clone())
    }
    pub fn vec(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CTyp, t: &CTyp, r: TypeError) -> Self {
        TypeError::Vec(kctx.clone(), vctx.clone(), e.clone(), t.clone(), Box::new(r))
    }
    pub fn coef(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Coef(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn mle(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Mle(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn map(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: CExp, id: Vid, r: CExp) -> Self {
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
    pub fn interp(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: &CExp, ta: CTyp, b: &CExp, tb: CTyp) -> Self {
        TypeError::Interp(kctx.clone(), vctx.clone(), a.clone(), ta, b.clone(), tb)
    }
    pub fn ram(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: &CExp, ta: CTyp, b: &CExp, tb: CTyp) -> Self {
        TypeError::Ram(kctx.clone(), vctx.clone(), a.clone(), ta, b.clone(), tb)
    }
    pub fn bool(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Bool(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn app_multiple(fctx: &Set<CSig>, id: Fid, params: CTyps) -> Self {
        TypeError::AppMultiple(fctx.clone(), id, params)
    }
    pub fn func_not_found(fctx: &Set<CSig>, id: Fid, params: CTyps) -> Self {
        TypeError::FuncNotFound(fctx.clone(), id, params)
    }
    pub fn contains(kctx: &Ctx<Tid, Kind>, vctx: &Ctx<Vid, CTyp>, a: CExp, ta: CTyp, b: CExp, tb: CTyp) -> Self {
        TypeError::Contains(kctx.clone(), vctx.clone(), a, ta, b, tb)
    }
}

/// Type inference for [CExp]
impl Typeable for CExp {
    type Context = Ctx<Vid, CTyp>;
    fn infer(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<CTyp, TypeError> {
        match self.clone() {
            // Infer the type of a literal [n] as a Fin<n> type
            CExp::Lit(n) => Ok(CTyp::fin(Range::singleton(n))),

            // Infer the type of a univariate polynomial from its coefficients' vector
            CExp::Coef(box v) => {
                // Infer the type of its argument
                let typ = v.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

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
            CExp::Mle(box v) => {
                // Infer the type of its argument
                let typ = v.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

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
            CExp::Vec(v) => {
                let ts: CTyps =
                    v.into_iter().map(|aexp| aexp.infer(kctx, fctx, vctx)).collect::<Result<_, _>>()
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Vectors cannot be empty for type inference to work
                if ts.is_empty() {
                    return Err(TypeError::vec_empty(kctx, &vctx));
                }

                // For reference, the type of the first element
                let mut t = ts.0[0].clone();

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
            CExp::Bin(BinOp::Add, box a, box b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                CTyp::lub_add(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle -
            CExp::Bin(BinOp::Sub, a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                CTyp::lub_sub(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle *
            CExp::Bin(BinOp::Mul, a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                CTyp::lub_mul(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle /
            CExp::Bin(BinOp::Div, a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                CTyp::lub_div(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle ^
            CExp::Bin(BinOp::Pow, a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                CTyp::lub_pow(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle .
            CExp::Bin(BinOp::Dot, a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                CTyp::lub_dot(ta, tb, kctx)
                        .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle ++
            CExp::Bin(BinOp::Concat, a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                match (ta.clone(), tb.clone()) {
                    (CTyp::Vec(box a, x), CTyp::Vec(box b, y)) => {
                        // Type [a] and [b] should be the same ([c])
                        let t = CTyp::lub_equ(a, b, kctx)
                            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;

                        // Add the sizes of the vectors
                        Ok(CTyp::vec(t, x + y))
                    },
                    (_, _) => Err(TypeError::concat(kctx, vctx, &ta, &tb))
                }
            }

            // Range expression
            CExp::Range(r) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start, r.step, r.end)
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(CTyp::Fin(rr), rr.get_size()))
            }

            // Map comprehension
            CExp::Map(box x, id, box r) => {
                // Type infer the range expression
                let tr = r.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match tr {
                    CTyp::Vec(box inner, n) => {
                        // Clone the context
                        let mut innerctx = vctx.clone();

                        // Add variable [id] to the context with type [inner]
                        innerctx.insert(&id, &inner);

                        // Type infer the expression [x] with the new context
                        let tx = x.infer(kctx, fctx, &mut innerctx)
                                .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        Ok(CTyp::vec(tx, n))
                    },
                    _ => Err(TypeError::exp(kctx, vctx, self))
                }
            }

            // Variable context lookup
            CExp::Var(id) =>
                vctx.get(&id).map(|x| x.clone()).ok_or(TypeError::var_not_found(&id, vctx)),

            // Random oracle challenge
            CExp::Challenge(t) | CExp::Random(t) => {
                // What kind of [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::lub(TypeError::exp(kctx, vctx, self), LubError::kind_not_found(&t)))?;

                // Only allow challenges/random for field elements
                if k.is_multiplicative() {
                    Ok(CTyp::Base(t))
                } else {
                    Err(TypeError::challenge(kctx, vctx, t, k))
                }
            }

            // Group generator
            CExp::Gen(t) => {
                // What kind of [t]?
                let k = kctx.get(&t).ok_or(
                    TypeError::lub(TypeError::exp(kctx, vctx, self), LubError::kind_not_found(&t)))?;

                // Only generate elements of groups
                if k.is_group() {
                    Ok(CTyp::Base(t))
                } else {
                    Err(TypeError::gen(kctx, vctx, t, k))
                }
            }

            // Interpolation of points into a univariate polynomial
            CExp::Interpolate(box a, box b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                // Must have a LUB; a vector of fields
                let t = CTyp::lub_equ(ta.clone(), tb.clone(), kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self),  e))?;

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
            CExp::Ram(a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;
                let tb = b.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                // Must be a vector and a Fin type
                match (ta.clone(), tb.clone()) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(r)) if r.end < n => Ok(typ),
                    (_,_) => Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                }
            }

            // Function application
            CExp::App(id, params) => {
                // type inference for each parameter
                let param_types: CTyps = params.into_iter()
                        .map(|p| p.infer(kctx, fctx, vctx)).collect::<Result<_, _>>()
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Find all matching functions in function context [fctx]
                let matching_sigs = fctx.iter().filter_map(|sig| {
                    // If the function name matches
                    if sig.name == id {
                        // The argument types must match the parameter types
                        let vs = sig.clone()
                            .unify(&param_types, &kctx)
                            .ok()?;
                        // Return new signature
                        Some(vs)
                    } else {
                        None
                    }
                }).collect::<Vec<_>>();

                // Only one function shoud match
                if matching_sigs.len() > 1 {
                    Err(TypeError::next(TypeError::exp(kctx, vctx, self), TypeError::app_multiple(fctx, id, param_types)))
                } else if matching_sigs.len() == 0 {
                    Err(TypeError::next(TypeError::exp(kctx, vctx, self), TypeError::func_not_found(fctx, id, param_types)))
                } else {
                    let sig = &matching_sigs[0];
                    Ok(sig.ret.clone())
                }
            }

            CExp::Equ(a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b.infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Values are equal when their types are equal (with unification)
                CTyp::lub_equ(ta, tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                Ok(CTyp::bool())
            }
            CExp::Contains(a, b) => {
                let ta = a.infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b.infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match (ta, tb) {
                    (x, CTyp::Vec(box a, _)) => {
                        CTyp::lub_equ(x, a, kctx)
                            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                        Ok(CTyp::bool())
                    },
                    (ta, tb) => Err(TypeError::contains(kctx, &vctx, *a, ta, *b, tb))
                }
            }
            CExp::And(a, b) | CExp::Or(a, b) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx))
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b.traverse1(&mut |x| x.infer(kctx, fctx, vctx))
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                // Types [ta] and [tb] must be equal and boolean
                let t = CTyp::lub_equ(*ta, *tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                if t == CTyp::Bool {
                    Ok(CTyp::bool())
                } else {
                    Err(TypeError::bool(kctx, vctx, &self))
                }
            },
            CExp::Not(a) => {
                let ta = a.traverse1(&mut |x| x.infer(kctx, fctx, vctx))
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                if *ta == CTyp::Bool {
                    Ok(CTyp::Bool)
                } else {
                    Err(TypeError::bool(kctx, vctx, &self))
                }
            },
            CExp::Assert(box a) | CExp::Verify(box a)=> {
                let t = a.infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self),  e))?;

                if t == CTyp::Bool {
                    Ok(CTyp::bool())
                } else {
                    Err(TypeError::bool(kctx, vctx, &self))
                }
            },

            CExp::Let(Some(var), box left, box right) | CExp::Log(var, box left, box right) => {
                let tleft = left.infer(kctx, fctx, vctx)?;
                vctx.insert(&var, &tleft);
                let tright = right.infer(kctx, fctx, vctx)?;
                Ok(tright)
            },
            CExp::Let(None, box left, box right) => {
                left.infer(kctx, fctx, vctx)?;
                right.infer(kctx, fctx, vctx)
            }
        }
    }
}

/// Type inference for [Body]
impl Typeable for CBody {
    type Context = Ctx<Vid, CTyp>;
    fn infer(&self, kctx: &Ctx<Tid, Kind>, fctx: &Set<CSig>, vctx: &mut Self::Context) -> Result<CTyp, TypeError> {
        // Type inference for each statement in the Body
        match self {
            CBody::Proto { relation, body } => {
                // First the relation
                let tr = relation.infer(kctx, fctx, &mut vctx.clone())?;
                if tr != CTyp::Bool {
                    return Err(TypeError::bool(kctx, vctx, &relation));
                }

                // Then the body
                let tbody = body.infer(kctx, fctx, &mut vctx.clone())?;

                if tbody != CTyp::Bool {
                    return Err(TypeError::bool(kctx, vctx, &body));
                } else {
                    Ok(CTyp::Bool)
                }
            },
            CBody::Func { body } =>
                body.infer(kctx, fctx, &mut vctx.clone())
        }
    }
}

/// Unit tests for type inference
#[cfg(test)]
mod tests {
    use super::*;
    use share::{Ctx, Set};
    use crate::id::{Fid, Tid, Vid};
    use crate::ast::{BinOp, Exp, Exps, UExp, CExp, CExps, CSig, Sig, Args, CArg};
    use crate::typ::{TypeVar, TypeVars, CTyp, Kind};
    use crate::typ::lub::{Lub, LubError, BinopError};
    use crate::typ::range::Range;
    use lazy_static::lazy_static;

    lazy_static! {
        static ref KIND_CTX: Ctx<Tid, Kind> = {
            let mut kctx = Ctx::new();
            // Add field type "F"
            kctx.insert(&Tid::from("F"), &Kind::Field);
            // Add group type "G"
            kctx.insert(&Tid::from("G"), &Kind::Group);
            // Add multiplicative group type "M"
            kctx.insert(&Tid::from("M"), &Kind::Multiplicative("F".into()));
            kctx
        };

        static ref VAR_CTX: Ctx<Vid, CTyp> = {
            let mut vctx = Ctx::new();
            // Add variable "x" of type "F"
            vctx.insert(&Vid::from("f1"), &CTyp::Base(Tid::from("F")));
            // Add variable "y" of type "F"
            vctx.insert(&Vid::from("f2"), &CTyp::Base(Tid::from("F")));
            // Add vector variable "v1" with element type "F" and length 5
            vctx.insert(&Vid::from("v1"), &CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5));
            // Add vector variable "v2" with element type "F" and length 4
            vctx.insert(&Vid::from("v2"), &CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 4));
            // Add variable "g" of type "G"
            vctx.insert(&Vid::from("g1"), &CTyp::Base(Tid::from("G")));
            // Add variable "g2" of type "G"
            vctx.insert(&Vid::from("g2"), &CTyp::Base(Tid::from("G")));
            // Add variable "m1" of type "M"
            vctx.insert(&Vid::from("m1"), &CTyp::Base(Tid::from("M")));
            // Add variable "m2" of type "M"
            vctx.insert(&Vid::from("m2"), &CTyp::Base(Tid::from("M")));
            vctx
        };
    }

    // Tests for literals
    #[test]
    fn test_literal_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a literal expression "5"
        let lit = CExp::lit(5);

        // Run type inference
        assert_eq!(lit.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Fin(Range::singleton(5))));
    }

    // Tests for binary operations
    #[test]
    fn test_binary_add_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x + y
        let field_add =
            CExp::add(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(field_add.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression g1 + g2
        let group_add =
            CExp::add(CExp::varstr("g1"), CExp::varstr("g2"));
        assert_eq!(group_add.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("G"))));

        // Create expression m1 + m2
        let mult_group_add =
            CExp::add(CExp::varstr("m1"), CExp::varstr("m2"));
        assert!(mult_group_add.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression v1 + v1
        let vec_add1 =
            CExp::add(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_add1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5)));

        // Create expression v1 + v2
        let vec_add2 =
            CExp::add(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_add2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for subtraction
    #[test]
    fn test_binary_sub_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x - y
        let field_sub =
            CExp::sub(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(field_sub.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression g1 - g2
        let group_sub =
            CExp::sub(CExp::varstr("g1"), CExp::varstr("g2"));
        assert_eq!(group_sub.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("G"))));

        // Create expression m1 - m2
        let mult_group_sub =
            CExp::sub(CExp::varstr("m1"), CExp::varstr("m2"));
        assert!(mult_group_sub.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression v1 - v1
        let vec_sub1 =
            CExp::sub(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_sub1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5)));

        // Create expression v1 - v2
        let vec_sub2 =
            CExp::sub(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_sub2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for multiplication
    #[test]
    fn test_binary_mul_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x * y
        let field_mul =
            CExp::mul(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(field_mul.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression g1 * g2
        let group_mul =
            CExp::mul(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_mul.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression m1 * m2
        let mult_group_mul =
            CExp::mul(CExp::varstr("m1"), CExp::varstr("m2"));
        assert_eq!(mult_group_mul.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("M"))));

        // Create expression v1 * v1
        let vec_mul1 =
            CExp::mul(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_mul1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5)));

        // Create expression v1 * v2
        let vec_mul2 =
            CExp::mul(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_mul2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for division
    #[test]
    fn test_binary_div_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x / y
        let field_div =
            CExp::div(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(field_div.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression g1 / g2
        let group_div =
            CExp::div(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_div.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression m1 / m2
        let mult_group_div =
            CExp::div(CExp::varstr("m1"), CExp::varstr("m2"));
        assert_eq!(mult_group_div.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("M"))));

        // Create expression v1 / v1
        let vec_div1 =
            CExp::div(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_div1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5)));

        // Create expression v1 / v2
        let vec_div2 =
            CExp::div(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_div2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for power
    #[test]
    fn test_binary_pow_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x ^ y
        let field_pow =
            CExp::pow(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(field_pow.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression g1 ^ g2
        let group_pow =
            CExp::pow(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_pow.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression m1 ^ m2
        let mult_group_pow1 =
            CExp::pow(CExp::varstr("m1"), CExp::varstr("m2"));
        assert!(mult_group_pow1.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression m1 ^ f1
        let mult_group_pow1 =
            CExp::pow(CExp::varstr("m1"), CExp::varstr("f1"));
        assert_eq!(mult_group_pow1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("M"))));

        // Create expression v1 ^ v1
        let vec_pow1 =
            CExp::pow(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_pow1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::vec(CTyp::varstr("F"), 5)));

        // Create expression v1 ^ v2
        let vec_pow2 =
            CExp::pow(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_pow2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for dot product
    #[test]
    fn test_binary_dot_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x . y
        let field_dot =
            CExp::dot(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(field_dot.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression g1 . g2
        let group_dot =
            CExp::dot(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_dot.infer(&KIND_CTX, &fctx, &mut vctx).is_err());

        // Create expression m1 . m2
        let mult_group_dot =
            CExp::dot(CExp::varstr("m1"), CExp::varstr("m2"));
        assert_eq!(mult_group_dot.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("M"))));

        // Create expression v1 . v1
        let vec_dot1 =
            CExp::dot(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_dot1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("F"))));

        // Create expression v1 . v2
        let vec_dot2 =
            CExp::dot(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_dot2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for equality
    #[test]
    fn test_binary_equ_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x == y
        let field_equ =
            CExp::equ(CExp::varstr("f1"), CExp::varstr("f2"));
        assert_eq!(field_equ.infer(&KIND_CTX, &fctx, &mut vctx), Ok(CTyp::Bool));

        // Create expression g1 == g2
        let group_equ =
            CExp::equ(CExp::varstr("g1"), CExp::varstr("g2"));
        assert_eq!(group_equ.infer(&KIND_CTX, &fctx, &mut vctx), Ok(CTyp::Bool));

        // Create expression m1 == m2
        let mult_group_equ =
            CExp::equ(CExp::varstr("m1"), CExp::varstr("m2"));
        assert_eq!(mult_group_equ.infer(&KIND_CTX, &fctx, &mut vctx), Ok(CTyp::Bool));

        let mult_group_equ2 =
            CExp::equ(CExp::varstr("m1"), CExp::varstr("f1"));
        assert_eq!(mult_group_equ2.infer(&KIND_CTX, &fctx, &mut vctx), Ok(CTyp::Bool));

        // Create expression v1 == v1
        let vec_equ1 =
            CExp::equ(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_equ1.infer(&KIND_CTX, &fctx, &mut vctx), Ok(CTyp::Bool));

        // Create expression v1 == v2
        let vec_equ2 =
            CExp::equ(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_equ2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for vector creation
    #[test]
    fn test_vector_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a vector expression [1, 2, 3]
        let lit_vec = CExp::vec(vec![
            CExp::lit(1),
            CExp::lit(2),
            CExp::lit(3),
        ]);
        assert_eq!(lit_vec.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::vec(CTyp::Fin(Range::new(1, 4)), 3)));

        // Create a vector expression [1, f1, 3]
        let lit_vec2 = CExp::vec(vec![
            CExp::lit(1),
            CExp::varstr("f1"),
            CExp::lit(3),
        ]);
        assert_eq!(lit_vec2.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::vec(CTyp::varstr("F"), 3)));

        // Create a vector expression [1, f1, g1]
        let lit_vec_bad = CExp::vec(vec![
            CExp::lit(1),
            CExp::varstr("f1"),
            CExp::varstr("g1"),
        ]);
        assert!(lit_vec_bad.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test for error: empty vector
    #[test]
    fn test_empty_vector_error() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an empty vector expression []
        let empty = CExp::vec(vec![]);

        assert!(empty.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    // Test interpolate
    #[test]
    fn test_interpolate() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an interpolation expression interpolate([1, 2, 3], [1, 2, 3])
        let interp1 = CExp::interpolate(
            CExp::vec(vec![
                CExp::lit(1),
                CExp::lit(2),
                CExp::lit(3),
            ]),
            CExp::vec(vec![
                CExp::lit(4),
                CExp::lit(5),
                CExp::lit(6),
            ]));

        assert_eq!(interp1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Uni(Tid::from("F"), 3)));

        // create an interpolation expression interpolate([1, 2, f1], [f2, 3, f1])
        let interp2 = CExp::interpolate(
            CExp::vec(vec![
                CExp::lit(1),
                CExp::lit(2),
                CExp::varstr("f1"),
            ]),
            CExp::vec(vec![
                CExp::varstr("f2"),
                CExp::lit(3),
                CExp::varstr("f1"),
            ]));

        assert_eq!(interp2.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Uni(Tid::from("F"), 3)));

        let interp_bad = CExp::interpolate(
            CExp::vec(vec![
                CExp::varstr("f1"),
                CExp::varstr("f2"),
            ]),
            CExp::vec(vec![
                CExp::varstr("g1"),
                CExp::varstr("g2"),
            ]));

        assert!(interp_bad.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }

    #[test]
    fn test_app() {
        let fctx = Set::singleton(
            Sig {
                name: "fun".into(),
                typevars: TypeVars::from([ TypeVar::new("F", Kind::Field), TypeVar::new("G", Kind::Group) ]),
                args: Args::from([
                    CArg::public("a".into(), CTyp::Base(Tid::from("F"))),
                    CArg::public("b".into(), CTyp::Base(Tid::from("F"))),
                    CArg::public("c".into(), CTyp::Base(Tid::from("G"))),
                ]),
                ret: CTyp::Base(Tid::from("G")),
            });

        let mut vctx = VAR_CTX.clone();

        // Create a function application fun(2, f1, g1)
        let app1 = CExp::app("fun".into(), Exps::from([
            CExp::lit(2),
            CExp::varstr("f1"),
            CExp::varstr("g1")
        ]));

        assert!(app1.infer(&KIND_CTX, &Set::new(), &mut vctx).is_err());

        assert_eq!(app1.infer(&KIND_CTX, &fctx, &mut vctx),
            Ok(CTyp::Base(Tid::from("G"))));

        // Create a function application fun(1, 2)
        let app2 = CExp::app("fun".into(), Exps::from([
            CExp::lit(1),
            CExp::lit(2)
        ]));
        assert!(app2.infer(&KIND_CTX, &fctx, &mut vctx).is_err());
    }
}
