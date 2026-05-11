#![allow(refining_impl_trait)]
use crate::ast::sig::CSig;
use crate::ast::{BinOp, CBody, CExp, CExps};
use crate::id::{Tid, Vid};
use crate::typ::lub::{Lub, LubError};
use crate::typ::range::{Range, RangeError};
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, CTyps};
use share::{Ctx, Set};
use thiserror::Error;

pub trait Typeable {
    type Context;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError>;
}

#[derive(Error, PartialEq, Debug)]
pub enum TypeError {
    #[error("TypeError: In declaration {0}:\n\n{1}")]
    Decl(Vid, Box<TypeError>),

    #[error("{0}\n\n{1}")]
    Next(Box<TypeError>, Box<TypeError>),

    #[error(
        "TypeError: Specification relation must be pure (no transcript and randomness):\n\t{0}"
    )]
    NotPureRel(CExp),

    #[error("TypeError: Cannot find an Arkworks type for {0}, {1} |- {2} : {3}")]
    Ark(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    #[error("TypeError: In expression {0}, {1} |- {2}")]
    CExp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("VecEmptyError: Cannot infer the type of the empty vector {0}, {1} |- []")]
    VecEmpty(Ctx<Tid, CKind>, Ctx<Vid, CTyp>),

    #[error(
        "VecTypeError: Vector elements must have the same type: {0}, {1} |- {2} != {3} \n\n\t{4}"
    )]
    Vec(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CTyp, CTyp, Box<TypeError>),

    #[error("InterpolateError: Arguments to [interpolate] must be vectors of fields:\n\t{0}, {1} |- interpolate {2}")]
    Interpolate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("InterpolateError: Unary [interpolate] expects a vector of fields:\n\t{0}, {1} |- interpolate {2}")]
    InterpolateUnary(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error(
        "InterpolateError: Unary [interpolate] requires a vector whose length is a power of two; got n={3}:\n\t{0}, {1} |- interpolate {2}"
    )]
    InterpolateUnaryNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize),

    #[error("PolyError: Argument to [poly] must be a vector of fields:\n\t{0}, {1} |- poly {2}")]
    Poly(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("EvaluateError: Arguments to [eval] must be a polynomial and a vector of scalars:\n\t{0}, {1} |- eval {2} {3}")]
    Evaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    #[error("EvaluateMleTooManyArgumentsError: Arguments to [eval] for a multilinear extension had too many arguments:\n\t{0}, {1} |- evalMle {2} {3}")]
    EvaluateMleTooManyArguments(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    #[error("CoefError: Arguments to [coef] must be a polynomial:\n\t{0}, {1} |- coef {2}")]
    Coef(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("MleError: Arguments to [mle] must be a vector type with size a power of 2:\n\t{0}, {1} |- mle {2}")]
    Mle(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("MleError: Must apply MLE to a scalar or vector of scalars:\n\t{0}, {1} |- {2} ( {3} : {4} )")]
    MleApp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Vid, CExps, CTyps),

    #[error(
        "MapError: Arguments to [for] must be a vector type:\n\t{0}, {1} |- [{2} for {3} in {4}]"
    )]
    Map(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Vid, CExp),

    #[error("ReduceError: Arguments to [reduce] must be a vector type:\n\t{0}, {1} |- reduce ({2}, {3} : {4})")]
    Reduce(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, BinOp, CExp, CTyp),

    #[error("UniError: Univariate polynomials over a field must be evaluated over a single scalar, or vector of scalars:\n\t{0}, {1} |- {2}( {3} : {4} )")]
    Uni(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Vid, CExps, CTyps),

    #[error("ChallengeError: Only challenges returning field elements are allowed:\n\t {0}, {1} |- challenge< {2} : {3} >")]
    Challenge(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Tid, CKind),

    #[error("VarError: Variable {0} not found in context {1}")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),

    #[error("RangeError: Not a valid range expression:\n\t{0}, {1} |- {2}\n\n{3}")]
    Range(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Range<usize>, RangeError),

    #[error("InterpolateError: Expects a field vector:\n\t{0}, {1} |- interpolate ( {2}: {3})")]
    Interp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    #[error("EvaluateGridError: Expects a polynomial (univariate or MLE):\n\t{0}, {1} |- eval ( {2}: {3})")]
    EvaluateGrid(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    #[error(
        "EvaluateGridError: Unary [eval] requires the polynomial's max-degree to be a power of two; got n={3}:\n\t{0}, {1} |- eval ( {2}: {4})"
    )]
    EvaluateGridNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize, CTyp),

    #[error("RamError: Index {4} must be a Fin type within the bounds of the vector {2}:\n\t{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    Ram(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("AppMultipleError: Function has multiple matching definitions in context\n\t{0} |- {1} ( {2} )")]
    AppMultiple(Set<CSig>, Vid, CTyps),

    #[error("FuncNotFound: No matching definition found for function:\n\t{0} |- {1} ( {2} )")]
    FuncNotFound(Set<CSig>, Vid, CTyps),

    #[error("BoolError: Expected boolean expression:\n\t{0}, {1} |- {2}")]
    Bool(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("FuncRetError: The return type of function {3} must be {4} but is found:\n\t{0}, {1} |- {2} : {5}")]
    FuncRet(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Vid, CTyp, CTyp),

    #[error("PairError: Expected group pairing between two pairing-friendly curves:\n\t{0}, {1} |- pair({2}: {3}, {4} : {5})")]
    Pair(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("RecordError: Field {3} not found in record:\n\t{0}, {1} |- {2}.{3}")]
    FieldNotFound(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, String),

    #[error("RecordError: Expression is not a record type:\n\t{0}, {1} |- {2} : {3}")]
    NotARecord(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    #[error(transparent)]
    Unify(#[from] UnifyError),

    #[error(transparent)]
    Lub(#[from] LubError),
}

impl<'a> TypeError {
    pub fn decl(id: &Vid, e: TypeError) -> Self {
        TypeError::Decl(id.clone(), Box::new(e))
    }
    pub fn next(a: Self, b: Self) -> Self {
        TypeError::Next(Box::new(a), Box::new(b))
    }
    pub fn unify(a: Self, u: UnifyError) -> Self {
        TypeError::next(a, TypeError::from(u))
    }
    pub fn not_pure_rel(e: &CExp) -> Self {
        TypeError::NotPureRel(e.clone())
    }
    pub fn lub(a: Self, l: LubError) -> Self {
        TypeError::next(a, TypeError::from(l))
    }
    pub fn ark(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::Ark(kctx.clone(), vctx.clone(), e.clone(), t.clone())
    }
    pub fn exp(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::CExp(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn vec_empty(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VecEmpty(kctx.clone(), vctx.clone())
    }
    pub fn vec(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CTyp,
        t: &CTyp,
        r: TypeError,
    ) -> Self {
        TypeError::Vec(
            kctx.clone(),
            vctx.clone(),
            e.clone(),
            t.clone(),
            Box::new(r),
        )
    }
    pub fn interpolate(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Interpolate(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn interpolate_unary(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::InterpolateUnary(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn interpolate_unary_not_pow2(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        n: usize,
    ) -> Self {
        TypeError::InterpolateUnaryNotPow2(kctx.clone(), vctx.clone(), e.clone(), n)
    }
    pub fn evaluate_grid_not_pow2(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        n: usize,
        t: &CTyp,
    ) -> Self {
        TypeError::EvaluateGridNotPow2(kctx.clone(), vctx.clone(), e.clone(), n, t.clone())
    }
    pub fn poly(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Poly(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn coef(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Coef(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn evaluate(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, p: &CExp, x: &CExp) -> Self {
        TypeError::Evaluate(kctx.clone(), vctx.clone(), p.clone(), x.clone())
    }
    pub fn evaluate_mle_too_many_arguments(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        x: &CExp,
    ) -> Self {
        TypeError::EvaluateMleTooManyArguments(kctx.clone(), vctx.clone(), p.clone(), x.clone())
    }
    pub fn mle(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Mle(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn mle_app(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        id: &Vid,
        e: &CExps,
        t: &CTyps,
    ) -> Self {
        TypeError::MleApp(kctx.clone(), vctx.clone(), id.clone(), e.clone(), t.clone())
    }
    pub fn map(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: CExp, id: Vid, r: CExp) -> Self {
        TypeError::Map(kctx.clone(), vctx.clone(), e, id, r)
    }
    pub fn reduce(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        op: BinOp,
        e: &CExp,
        t: &CTyp,
    ) -> Self {
        TypeError::Reduce(kctx.clone(), vctx.clone(), op, e.clone(), t.clone())
    }
    pub fn uni(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        id: &Vid,
        e: &CExps,
        ts: &CTyps,
    ) -> Self {
        TypeError::Uni(
            kctx.clone(),
            vctx.clone(),
            id.clone(),
            e.clone(),
            ts.clone(),
        )
    }
    pub fn challenge(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, t: &Tid, k: &CKind) -> Self {
        TypeError::Challenge(kctx.clone(), vctx.clone(), t.clone(), k.clone())
    }
    pub fn var_not_found(id: &Vid, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VarNotFound(id.clone(), vctx.clone())
    }
    pub fn range(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        r: &Range<usize>,
        e: RangeError,
    ) -> Self {
        TypeError::Range(kctx.clone(), vctx.clone(), r.clone(), e)
    }
    pub fn interp(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, a: &CExp, ta: &CTyp) -> Self {
        TypeError::Interp(kctx.clone(), vctx.clone(), a.clone(), ta.clone())
    }
    pub fn evaluate_grid(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        a: &CExp,
        ta: &CTyp,
    ) -> Self {
        TypeError::EvaluateGrid(kctx.clone(), vctx.clone(), a.clone(), ta.clone())
    }
    pub fn ram(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        a: &CExp,
        ta: CTyp,
        b: &CExp,
        tb: CTyp,
    ) -> Self {
        TypeError::Ram(kctx.clone(), vctx.clone(), a.clone(), ta, b.clone(), tb)
    }
    pub fn bool(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Bool(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn app_multiple(fctx: &Set<CSig>, id: &Vid, params: CTyps) -> Self {
        TypeError::AppMultiple(fctx.clone(), id.clone(), params)
    }
    pub fn func_not_found(fctx: &Set<CSig>, id: &Vid, params: CTyps) -> Self {
        TypeError::FuncNotFound(fctx.clone(), id.clone(), params)
    }
    pub fn func_ret(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        id: &Vid,
        t: &CTyp,
        r: &CTyp,
    ) -> Self {
        TypeError::FuncRet(
            kctx.clone(),
            vctx.clone(),
            e.clone(),
            id.clone(),
            t.clone(),
            r.clone(),
        )
    }
    pub fn pair(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        t: &CExp,
        ta: &CTyp,
        e: &CExp,
        te: &CTyp,
    ) -> Self {
        TypeError::Pair(
            kctx.clone(),
            vctx.clone(),
            t.clone(),
            ta.clone(),
            e.clone(),
            te.clone(),
        )
    }
    pub fn field_not_found(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        field: &str,
        _fields: &Ctx<String, CTyp>,
    ) -> Self {
        TypeError::FieldNotFound(kctx.clone(), vctx.clone(), e.clone(), field.to_string())
    }
    pub fn not_a_record(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::NotARecord(kctx.clone(), vctx.clone(), e.clone(), t.clone())
    }
}

/// Type inference for [CExp]
impl Typeable for CExp {
    type Context = Ctx<Vid, CTyp>;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError> {
        match self {
            // Infer the type of a literal [n] as a Fin<n> type
            CExp::Lit(n) => Ok(CTyp::fin(Range::singleton(*n))),

            // Booleans
            CExp::Bool(_) => Ok(CTyp::Bool),

            // Unary: FFT-grid interpolation; binary: explicit points + evaluations
            CExp::Interpolate(points_opt, box evals) => {
                let evals_typ = evals
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match points_opt {
                    None => match evals_typ {
                        CTyp::Vec(box b, n) => {
                            let i = b
                                .to_scalar(kctx)
                                .ok_or(TypeError::interpolate_unary(kctx, &vctx, self))?;
                            if !n.is_power_of_two() {
                                return Err(TypeError::interpolate_unary_not_pow2(
                                    kctx, vctx, self, n,
                                ));
                            }
                            Ok(CTyp::Poly(i, 1, n))
                        }
                        _ => Err(TypeError::interpolate_unary(kctx, &vctx, self)),
                    },
                    Some(points) => {
                        let points_typ = points
                            .infer(kctx, fctx, vctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        match (points_typ, evals_typ) {
                            (CTyp::Vec(box bp, np), CTyp::Vec(box be, ne)) if np == ne => {
                                let ip = bp
                                    .to_scalar(kctx)
                                    .ok_or(TypeError::interpolate(kctx, &vctx, self))?;
                                let ie = be
                                    .to_scalar(kctx)
                                    .ok_or(TypeError::interpolate(kctx, &vctx, self))?;
                                if ip != ie {
                                    return Err(TypeError::interpolate(kctx, &vctx, self));
                                }
                                Ok(CTyp::Poly(ie, 1, ne))
                            }
                            _ => Err(TypeError::interpolate(kctx, &vctx, self)),
                        }
                    }
                }
            }

            CExp::Poly(box v) => {
                let typ = v
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match typ {
                    CTyp::Vec(box b, n) => {
                        let i = b
                            .to_scalar(kctx)
                            .ok_or(TypeError::poly(kctx, &vctx, self))?;
                        Ok(CTyp::Poly(i, 1, n))
                    }
                    _ => Err(TypeError::poly(kctx, &vctx, self)),
                }
            }

            CExp::Coef(box p) => {
                let typ = p
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match typ {
                    CTyp::Poly(tid, 1, n) => {
                        let k = kctx.get(&tid).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(&tid),
                        ))?;
                        // Only field elements can be evaluated
                        if k.is_scalar() {
                            Ok(CTyp::vec(&CTyp::Base(tid), n))
                        } else {
                            Err(TypeError::coef(kctx, vctx, self))
                        }
                    }
                    _ => Err(TypeError::coef(kctx, &vctx, self)),
                }
            }

            CExp::Evaluate(box p, opt_points) => {
                let p_typ = p
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match opt_points {
                    // Binary form: eval(p, points) — point or vector evaluation.
                    Some(box x) => {
                        let x_typ = x
                            .infer(kctx, fctx, vctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        match (p_typ, x_typ) {
                            // Univariate polynomial evaluated at a vector of points:
                            (CTyp::Poly(_i, 1, _n), CTyp::Vec(b, len_vec)) => {
                                let _i = b
                                    .to_scalar(kctx)
                                    .ok_or(TypeError::evaluate(kctx, &vctx, p, x))?;
                                Ok(CTyp::Vec(b, len_vec))
                            }
                            // Multivariate polynomial (MLE, virtual, etc.): n > 1.
                            (CTyp::Poly(_i, n, d), CTyp::Vec(b, len_vec)) if n > 1 => {
                                let i = b
                                    .to_scalar(kctx)
                                    .ok_or(TypeError::evaluate(kctx, &vctx, p, x))?;
                                if len_vec == n {
                                    return Ok(*b);
                                }
                                if len_vec < n {
                                    return Ok(CTyp::Poly(i, n - len_vec, d));
                                }
                                Err(TypeError::evaluate_mle_too_many_arguments(
                                    kctx, &vctx, p, x,
                                ))
                            }
                            _ => Err(TypeError::evaluate(kctx, &vctx, p, x)),
                        }
                    }
                    // Unary form: eval(p) — evaluation on the FFT grid (n roots of unity).
                    None => {
                        let t = p_typ;
                        match t.clone() {
                            CTyp::Poly(tid, 1, n) => {
                                let k = kctx.get(&tid).ok_or(TypeError::lub(
                                    TypeError::exp(kctx, vctx, self),
                                    LubError::kind_not_found(&tid),
                                ))?;
                                if !k.is_scalar() {
                                    return Err(TypeError::evaluate_grid(kctx, vctx, p, &t));
                                }
                                if !n.is_power_of_two() {
                                    return Err(TypeError::evaluate_grid_not_pow2(
                                        kctx, vctx, p, n, &t,
                                    ));
                                }
                                Ok(CTyp::vec(&CTyp::Base(tid), n))
                            }
                            _ => Err(TypeError::evaluate_grid(kctx, vctx, p, &t)),
                        }
                    }
                }
            }

            // Infer the type of an MLE from 2^n evaluations in a bool hypercube (as a vector)
            CExp::Mle(box v) => {
                // It must be a vector of fields, or a vector of Fin
                let typ = v
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match typ {
                    CTyp::Vec(box b, n) => {
                        let n_pow = n.ilog2() as usize;
                        if 2_usize.pow(n_pow as u32) != n {
                            return Err(TypeError::mle(kctx, &vctx, self));
                        }
                        let i = b
                            .to_scalar(kctx)
                            .ok_or(TypeError::poly(kctx, &vctx, self))?;
                        Ok(CTyp::Poly(i, n_pow, 1))
                    }
                    _ => Err(TypeError::mle(kctx, &vctx, self)),
                }
            }

            // Infer the type of a marginalize call.
            CExp::Marginalize(box rec) => {
                let rec_typ = rec
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                let CTyp::Record(ref fields) = rec_typ else {
                    return Err(TypeError::not_a_record(kctx, vctx, &rec, &rec_typ));
                };

                let poly_typ = fields
                    .get(&"poly".to_string())
                    .ok_or_else(|| TypeError::field_not_found(kctx, vctx, &rec, "poly", &fields))?;
                let (field_tid, n, d) = match poly_typ {
                    CTyp::Poly(tid, n, d) => (tid.clone(), *n, *d),
                    _ => return Err(TypeError::poly(kctx, vctx, self)),
                };

                let challenge_typ = fields.get(&"challenge".to_string()).ok_or_else(|| {
                    TypeError::field_not_found(kctx, vctx, &rec, "challenge", &fields)
                })?;
                let challenge_tid = challenge_typ
                    .to_scalar(kctx)
                    .ok_or_else(|| TypeError::exp(kctx, vctx, self))?;
                if challenge_tid != field_tid {
                    return Err(TypeError::exp(kctx, vctx, self));
                }

                let round_typ = fields.get(&"round".to_string()).ok_or_else(|| {
                    TypeError::field_not_found(kctx, vctx, &rec, "round", &fields)
                })?;
                if !matches!(round_typ, CTyp::Fin(_)) {
                    return Err(TypeError::exp(kctx, vctx, self));
                }

                let num_variables_typ =
                    fields.get(&"num_variables".to_string()).ok_or_else(|| {
                        TypeError::field_not_found(kctx, vctx, &rec, "num_variables", &fields)
                    })?;
                if !matches!(num_variables_typ, CTyp::Fin(_)) {
                    return Err(TypeError::exp(kctx, vctx, self));
                }

                let max_degree_typ = fields.get(&"max_degree".to_string()).ok_or_else(|| {
                    TypeError::field_not_found(kctx, vctx, &rec, "max_degree", &fields)
                })?;
                if !matches!(max_degree_typ, CTyp::Fin(_)) {
                    return Err(TypeError::exp(kctx, vctx, self));
                }

                // Runtime consumes max_degree as an index. When this is a singleton Fin,
                // preserve that precise degree in the inferred output type.
                let out_degree = match max_degree_typ {
                    CTyp::Fin(r) if r.step == 1 && r.end == r.start + 1 => r.start,
                    _ => d,
                };

                let mut out_fields = Ctx::new();
                let f_typ = CTyp::Base(field_tid.clone());
                out_fields.insert(
                    &"evaluations".to_string(),
                    &CTyp::vec(&f_typ, out_degree + 1),
                );
                let next_n = n.saturating_sub(1);
                out_fields.insert(
                    &"next_poly".to_string(),
                    &CTyp::Poly(field_tid.clone(), next_n, out_degree),
                );

                Ok(CTyp::Record(out_fields))
            }

            // Infer the type of a (nonempty) vector by unifying the types of its elements
            CExp::Vec(v) => {
                let ts: CTyps = v
                    .iter()
                    .map(|aexp| aexp.infer(kctx, fctx, vctx))
                    .collect::<Result<_, _>>()
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Vectors cannot be empty for type inference to work
                if ts.is_empty() {
                    return Err(TypeError::vec_empty(kctx, &vctx));
                }

                // For reference, the type of the first element
                let mut t = ts.0[0].clone();

                // Unify types of all elements in the vector to [t]
                for tx in ts.0[1..].iter() {
                    t = CTyp::lub_equ(&t, tx, kctx)
                        .map_err(|e| TypeError::vec(kctx, &vctx, tx, &t, e.into()))?;
                }

                // Vector length
                let n = ts.len();

                // Generalize the type of the parameters
                Ok(CTyp::vec(&t, n))
            }

            CExp::Pair(box t, box e) => {
                let ta = t
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = e
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_pair(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle +
            CExp::Bin(BinOp::Add, box a, box b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_add(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle -
            CExp::Bin(BinOp::Sub, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_sub(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle *
            CExp::Bin(BinOp::Mul, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_mul(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle /
            CExp::Bin(BinOp::Div, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_div(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle ^
            CExp::Bin(BinOp::Pow, box a, box b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_pow(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle .
            CExp::Bin(BinOp::Dot, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_dot(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            // Handle %
            CExp::Bin(BinOp::Rem, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_rem(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }
            // Handle ++
            CExp::Bin(BinOp::Concat, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                CTyp::lub_concat(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
            }

            CExp::Bin(BinOp::Equ, a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Values are equal when their types are equal (with unification)
                CTyp::lub_equ(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                Ok(CTyp::bool())
            }

            CExp::Bin(BinOp::And, box a, box b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Types [ta] and [tb] must be equal and boolean
                let t = CTyp::lub_and(&ta, &tb, kctx)
                    .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))?;
                if t == CTyp::Bool {
                    Ok(CTyp::bool())
                } else {
                    Err(TypeError::bool(kctx, vctx, &self))
                }
            }

            // Range expression
            CExp::Range(r) => {
                // Infer the type of the range expression as a vector of sizes
                let rr = Range::from_num(r.start, r.step, r.end)
                    .map_err(|e| TypeError::range(kctx, vctx, r, e))?;

                Ok(CTyp::vec(&CTyp::Fin(rr), rr.len()))
            }

            // Map comprehension
            CExp::Map(box x, id, box r) => {
                // Type infer the range expression
                let tr = r
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match tr {
                    CTyp::Vec(box inner, n) if n > 0 => {
                        // Clone the context
                        let mut innerctx = vctx.clone();

                        // Add variable [id] to the context with type [inner]
                        innerctx.insert(&id, &inner);

                        // Type infer the expression [x] with the new context
                        let tx = x
                            .infer(kctx, fctx, &innerctx)
                            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                        Ok(CTyp::vec(&tx, n))
                    }
                    _ => Err(TypeError::exp(kctx, vctx, self)),
                }
            }

            CExp::Reduce(op, box v) => {
                // Type infer the vector expression
                let tv = v
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match tv {
                    CTyp::Vec(box tv, n) if n > 0 => {
                        // Infer the return type
                        CTyp::lub_op(*op, &tv, &tv, kctx)
                            .map_err(|e| TypeError::lub(TypeError::exp(kctx, vctx, self), e))
                    }
                    _ => Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::reduce(kctx, vctx, *op, v, &tv),
                    )),
                }
            }
            // Variable context lookup
            CExp::Var(id) => vctx
                .get(&id)
                .cloned()
                .ok_or(TypeError::var_not_found(&id, vctx)),

            // Random oracle challenge
            CExp::Challenge(t, _) | CExp::Random(t, _) => {
                // What kind of [t]?
                kctx.get(&t).ok_or(TypeError::lub(
                    TypeError::exp(kctx, vctx, self),
                    LubError::kind_not_found(&t),
                ))?;

                Ok(CTyp::base(t))
            }

            // Random access into vectors
            CExp::Ram(a, b) => {
                let ta = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let tb = b
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Must be a vector, Uni, MLE and a Fin type
                match (ta.clone(), tb.clone()) {
                    (CTyp::Vec(box typ, n), CTyp::Fin(r)) => {
                        if r.end <= n {
                            Ok(typ)
                        } else {
                            Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                        }
                    }
                    (CTyp::Vec(box typ, n), CTyp::Vec(box CTyp::Fin(r), m)) => {
                        if r.end <= n {
                            Ok(CTyp::vec(&typ, m))
                        } else {
                            Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                        }
                    }
                    (CTyp::Poly(tbase, 1, n), CTyp::Fin(r)) => {
                        if r.end <= n {
                            Ok(CTyp::base(&tbase))
                        } else {
                            Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                        }
                    }
                    (CTyp::Poly(tbase, n, 1), CTyp::Fin(r)) => {
                        if r.end <= 1 << n {
                            Ok(CTyp::base(&tbase))
                        } else {
                            Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                        }
                    }
                    (CTyp::Poly(tbase, 1, n), CTyp::Vec(box CTyp::Fin(r), _m)) => {
                        if r.end <= n {
                            Ok(CTyp::Poly(tbase, 1, r.len()))
                        } else {
                            Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                        }
                    }
                    (CTyp::Poly(tbase, n, 1), CTyp::Vec(box CTyp::Fin(r), _m)) => {
                        if r.end <= 1 << n {
                            Ok(CTyp::Poly(tbase, r.len().ilog2() as usize, 1))
                        } else {
                            Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb))
                        }
                    }
                    (_, _) => Err(TypeError::ram(kctx, vctx, &a, ta, &b, tb)),
                }
            }

            // Function or polynomial application
            CExp::App(id, params) => {
                // type inference for each parameter
                let param_types: CTyps = params
                    .iter()
                    .map(|p| p.infer(kctx, fctx, vctx))
                    .collect::<Result<_, _>>()
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                // Is it a polynomial, MLE, or a function?
                match vctx.get(&id) {
                    Some(CTyp::Poly(tbase, 1, _)) => {
                        // It is a univariate polynomial
                        let k = kctx.get(&tbase).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(&tbase),
                        ))?;

                        // Only field elements can be evaluated and only 1 argument can be given
                        if !k.is_scalar() || param_types.len() != 1 {
                            return Err(TypeError::uni(kctx, vctx, id, params, &param_types));
                        }

                        // The argument must be a field and the same as the polynomial
                        if let Some(tb) = param_types.0[0].clone().to_scalar(kctx) {
                            if &tb == tbase {
                                // The polynomial is a field
                                Ok(CTyp::base(tbase))
                            } else {
                                Err(TypeError::uni(kctx, vctx, id, params, &param_types))
                            }
                        } else {
                            Err(TypeError::uni(kctx, vctx, id, params, &param_types))
                        }
                    }
                    Some(CTyp::Poly(tbase, n, 1)) => {
                        // It is a multilinear extension
                        let k = kctx.get(&tbase).ok_or(TypeError::lub(
                            TypeError::exp(kctx, vctx, self),
                            LubError::kind_not_found(&tbase),
                        ))?;
                        // Only field elements can be evaluated and only 1 argument can be given
                        if !k.is_scalar() || param_types.len() != 1 {
                            return Err(TypeError::mle_app(kctx, vctx, id, params, &param_types));
                        }

                        // The argument must be a field and the same as the MLE
                        match param_types.0[0].clone() {
                            CTyp::Fin(_r) if *n > 0 => Ok(CTyp::mle(tbase, n - 1)),
                            CTyp::Base(tb) if &tb == tbase && *n > 0 => Ok(CTyp::mle(tbase, n - 1)),
                            CTyp::Vec(box CTyp::Base(tb), m) if &tb == tbase && *n == m => {
                                Ok(CTyp::base(tbase))
                            }
                            CTyp::Vec(box CTyp::Fin(_), m) if *n == m => Ok(CTyp::base(tbase)),
                            CTyp::Vec(box CTyp::Fin(_), m) if *n > m => Ok(CTyp::mle(tbase, n - m)),
                            CTyp::Vec(box CTyp::Base(tb), m) if &tb == tbase && *n > m => {
                                Ok(CTyp::mle(tbase, n - m))
                            }
                            _ => Err(TypeError::mle_app(kctx, vctx, id, params, &param_types)),
                        }
                    }
                    _ => {
                        // It is a function
                        // Find all matching functions in function context [fctx]
                        let mut matching_sigs: Vec<_> = fctx
                            .iter()
                            .filter_map(|sig| {
                                if &sig.name != id {
                                    return None;
                                }
                                let (vs, _) = sig.clone().unify(&param_types, &kctx).ok()?;
                                Some(vs)
                            })
                            .collect();
                        // [CTyp::unify] uses max() on univariate degree so many overloads
                        // Poly<F,1,d> all unify with Poly<F,1,1>. When ambiguous, keep only
                        // signatures whose parameters match argument types exactly (no widening).
                        if matching_sigs.len() > 1 {
                            matching_sigs.retain(|vs| {
                                vs.args
                                    .iter()
                                    .zip(param_types.0.iter())
                                    .all(|(a, t)| a.typ == *t)
                            });
                        }

                        // Only one function shoud match
                        if matching_sigs.len() != 1 {
                            Err(TypeError::next(
                                TypeError::exp(kctx, vctx, self),
                                TypeError::app_multiple(fctx, id, param_types),
                            ))
                        } else {
                            let sig = &matching_sigs[0];
                            Ok(sig.ret.clone())
                        }
                    }
                }
            }

            CExp::Assert(box a) | CExp::Verify(box a) => {
                let t = a
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                if t == CTyp::Bool {
                    Ok(CTyp::bool())
                } else {
                    Err(TypeError::bool(kctx, vctx, &self))
                }
            }

            CExp::Let(Some(var), box left, box right) | CExp::Log(var, box left, box right) => {
                let tleft = left.infer(kctx, fctx, vctx)?;
                let mut vctx = vctx.clone();
                vctx.insert(&var, &tleft);
                let tright = right.infer(kctx, fctx, &vctx)?;
                Ok(tright)
            }
            CExp::Let(None, box left, box right) => {
                left.infer(kctx, fctx, vctx)?;
                right.infer(kctx, fctx, vctx)
            }

            CExp::Fun(vars, box body) => {
                // Create a new variable context with the parameters
                let mut new_vctx = vctx.clone();

                // Find a field type
                let field_tid = kctx
                    .iter()
                    .find(|(_, k)| k.is_scalar())
                    .map(|(tid, _)| tid.clone())
                    .ok_or(TypeError::exp(kctx, vctx, self))?;

                if vars.len() == 1 {
                    // Univariate polynomial - type the variable as Poly(F, 1, 1) (degree-1 polynomial)
                    // Then type inference will compute the actual degree through lub operations
                    for var in vars {
                        new_vctx.insert(var, &CTyp::Poly(field_tid.clone(), 1, 1));
                    }

                    // Infer the type of the body - should get Poly(F, 1, N) where N is the degree
                    let body_type = body.infer(kctx, fctx, &new_vctx)?;

                    // Extract the degree from the inferred type
                    match body_type {
                        CTyp::Poly(tid, 1, degree) => Ok(CTyp::Poly(tid, 1, degree)),
                        CTyp::Base(tid) => Ok(CTyp::Poly(tid, 1, 0)), // Constant polynomial
                        _ => Err(TypeError::exp(kctx, vctx, self)),
                    }
                } else {
                    // Multilinear polynomial - type variables as scalars and validate structure
                    for var in vars {
                        new_vctx.insert(var, &CTyp::Base(field_tid.clone()));
                    }

                    let body_type = body.infer(kctx, fctx, &new_vctx)?;

                    match body_type {
                        CTyp::Base(tid)
                            if kctx.get(&tid).map(|k| k.is_scalar()).unwrap_or(false) =>
                        {
                            // For multilinear, we just return Mle with the number of variables
                            // Backend validation will catch if it's not actually multilinear
                            Ok(CTyp::mle(&tid, vars.len()))
                        }
                        _ => Err(TypeError::exp(kctx, vctx, self)),
                    }
                }
            }

            CExp::Record(fields) => {
                let mut field_types = Ctx::new();

                // Infer the type of each field
                for (field_name, field_exp) in fields.iter() {
                    let field_typ = field_exp
                        .infer(kctx, fctx, vctx)
                        .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                    field_types.insert(field_name, &field_typ);
                }

                Ok(CTyp::Record(field_types))
            }

            CExp::Proj(box record_exp, field_name) => {
                // Infer the type of the record expression
                let record_typ = record_exp
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

                match record_typ {
                    CTyp::Record(fields) => {
                        // Look up the field in the record type
                        fields.get(&field_name).cloned().ok_or_else(|| {
                            TypeError::next(
                                TypeError::exp(kctx, vctx, self),
                                TypeError::field_not_found(
                                    kctx,
                                    vctx,
                                    &record_exp,
                                    &field_name,
                                    &fields,
                                ),
                            )
                        })
                    }
                    _ => Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::not_a_record(kctx, vctx, &record_exp, &record_typ),
                    )),
                }
            }

            CExp::SetRecord(box record_exp, field_name, box value_exp) => {
                // Infer the type of the record expression (must be a record)
                let record_typ = record_exp
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let CTyp::Record(fields) = &record_typ else {
                    return Err(TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::not_a_record(kctx, vctx, &record_exp, &record_typ),
                    ));
                };
                // Check the field exists and the value has a type compatible with the field (e.g. Fin unifies with F)
                let field_typ = fields.get(&field_name).ok_or_else(|| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::field_not_found(kctx, vctx, &record_exp, field_name, fields),
                    )
                })?;
                let value_typ = value_exp
                    .infer(kctx, fctx, vctx)
                    .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
                let _ = CTyp::lub_equ(&value_typ, field_typ, kctx).map_err(|e| {
                    TypeError::next(
                        TypeError::exp(kctx, vctx, self),
                        TypeError::lub(TypeError::exp(kctx, vctx, self), e),
                    )
                })?;
                // Result type is the same record type
                Ok(record_typ.clone())
            }
        }
    }
}

/// Type inference for [Body]
impl Typeable for CBody {
    type Context = Ctx<Vid, CTyp>;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError> {
        // Type inference for each statement in the Body
        match self {
            CBody::Proto { relation, body } => {
                // First the relation
                let tr = relation.infer(kctx, fctx, &vctx.clone())?;
                if tr != CTyp::Bool {
                    return Err(TypeError::bool(kctx, vctx, &relation));
                }

                // Then the body
                let tbody = body.infer(kctx, fctx, &vctx.clone())?;

                if tbody != CTyp::Bool {
                    Err(TypeError::bool(kctx, vctx, &body))
                } else {
                    Ok(CTyp::Bool)
                }
            }
            CBody::Func { body } => body.infer(kctx, fctx, &vctx.clone()),
            CBody::TypeAlias => Ok(CTyp::Bool), // Type aliases have no body to check
        }
    }
}

/// Unit tests for type inference
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Args, CArg, CExp, Exps, Sig};
    use crate::id::{Tid, Vid};
    use crate::typ::range::Range;
    use crate::typ::{CTyp, Kind, TypeVar, TypeVars};
    use lazy_static::lazy_static;
    use share::{Ctx, Set};

    lazy_static! {
        static ref KIND_CTX: Ctx<Tid, CKind> = {
            let mut kctx = Ctx::new();
            // Add field type "F"
            kctx.insert(&Tid::from("F"), &Kind::Field);
            // Add group type "G"
            kctx.insert(&Tid::from("G"), &Kind::Group);
            // Add scalar type "S"
            kctx.insert(&Tid::from("S"), &Kind::scalar1("G"));
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
            // Add variable "s1" of type "S"
            vctx.insert(&Vid::from("s1"), &CTyp::Base(Tid::from("S")));
            // Add variable "s2" of type "S"
            vctx.insert(&Vid::from("s2"), &CTyp::Base(Tid::from("S")));
            // Add variable "p" of type "Uni<F, 5>"
            vctx.insert(&Vid::from("p"), &CTyp::Poly(Tid::from("F"), 1, 5));
            // Add variable "m" of type "Mle<F, 8>"
            vctx.insert(&Vid::from("m"), &CTyp::Poly(Tid::from("F"), 8, 1));
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
        assert_eq!(
            lit.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Fin(Range::singleton(5)))
        );
    }

    // Tests for binary operations
    #[test]
    fn test_binary_add_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x + y
        let field_add = CExp::add(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(
            field_add.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create expression g1 + g2
        let group_add = CExp::add(CExp::varstr("g1"), CExp::varstr("g2"));
        assert_eq!(
            group_add.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("G")))
        );

        // Create expression s1 + s2
        let mult_group_add = CExp::add(CExp::varstr("s1"), CExp::varstr("s2"));
        assert_eq!(
            mult_group_add.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("S")))
        );

        // Create expression v1 + v1
        let vec_add1 = CExp::add(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(
            vec_add1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5))
        );

        // Create expression v1 + v2
        let vec_add2 = CExp::add(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_add2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for subtraction
    #[test]
    fn test_binary_sub_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x - y
        let field_sub = CExp::sub(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(
            field_sub.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create expression g1 - g2
        let group_sub = CExp::sub(CExp::varstr("g1"), CExp::varstr("g2"));
        assert_eq!(
            group_sub.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("G")))
        );

        // Create expression s1 - s2
        let mult_group_sub = CExp::sub(CExp::varstr("s1"), CExp::varstr("s2"));
        assert_eq!(
            mult_group_sub.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("S")))
        );

        // Create expression v1 - v1
        let vec_sub1 = CExp::sub(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(
            vec_sub1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5))
        );

        // Create expression v1 - v2
        let vec_sub2 = CExp::sub(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_sub2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for multiplication
    #[test]
    fn test_binary_mul_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x * y
        let field_mul = CExp::mul(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(
            field_mul.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create expression g1 * g2
        let group_mul = CExp::mul(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_mul.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression s1 * s2
        let mult_group_mul = CExp::mul(CExp::varstr("s1"), CExp::varstr("s2"));
        assert_eq!(
            mult_group_mul.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("S")))
        );

        // Create expression v1 * v1
        let vec_mul1 = CExp::mul(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(
            vec_mul1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5))
        );

        // Create expression v1 * v2
        let vec_mul2 = CExp::mul(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_mul2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for division
    #[test]
    fn test_binary_div_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x / y
        let field_div = CExp::div(CExp::varstr("f1"), CExp::varstr("f2"));

        assert_eq!(
            field_div.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create expression g1 / g2
        let group_div = CExp::div(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_div.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression s1 / s2
        let mult_group_div = CExp::div(CExp::varstr("s1"), CExp::varstr("s2"));
        assert_eq!(
            mult_group_div.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("S")))
        );

        // Create expression v1 / v1
        let vec_div1 = CExp::div(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(
            vec_div1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Vec(Box::new(CTyp::Base(Tid::from("F"))), 5))
        );

        // Create expression v1 / v2
        let vec_div2 = CExp::div(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_div2.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression p / p
        let uni_div = CExp::div(CExp::varstr("p"), CExp::varstr("p"));
        assert_eq!(
            uni_div.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, 1))
        );
    }

    // Test for remainder
    #[test]
    fn test_binary_rem_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x % y
        let field_rem = CExp::rem(CExp::varstr("f1"), CExp::varstr("f2"));

        // fields have no modulo
        assert!(field_rem.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression g1 % g2, groups have no modulo
        let group_rem = CExp::rem(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_rem.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression s1 % s2
        let mult_group_rem = CExp::rem(CExp::varstr("s1"), CExp::varstr("s2"));
        assert!(mult_group_rem.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression p % p
        let uni_rem = CExp::rem(CExp::varstr("p"), CExp::varstr("p"));
        assert_eq!(
            uni_rem.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, 4))
        );
    }

    // Test for power
    #[test]
    fn test_binary_pow_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x ^ y
        let field_pow = CExp::pow(CExp::varstr("f1"), CExp::lit(2));

        assert_eq!(
            field_pow.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create expression g1 ^ g2
        let group_pow = CExp::pow(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_pow.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression s1 ^ s2
        let mult_group_pow1 = CExp::pow(CExp::varstr("s1"), CExp::lit(2));
        assert_eq!(
            mult_group_pow1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("S")))
        );

        // Create expression s1 ^ f1
        let mult_group_pow1 = CExp::pow(CExp::varstr("s1"), CExp::varstr("f1"));
        assert!(mult_group_pow1.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression v1 ^ v1
        let vec_pow1 = CExp::pow(CExp::varstr("v1"), CExp::vec(vec![CExp::lit(1); 5]));
        assert_eq!(
            vec_pow1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::varstr("F"), 5))
        );

        // Create expression v1 ^ v2
        let vec_pow2 = CExp::pow(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_pow2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for dot product
    #[test]
    fn test_binary_dot_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x . y
        let field_dot = CExp::dot(CExp::varstr("f1"), CExp::varstr("f2"));
        // Only vectors and polynomials can be dotted
        assert!(field_dot.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression g1 . g2
        let group_dot = CExp::dot(CExp::varstr("g1"), CExp::varstr("g2"));
        assert!(group_dot.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression s1 . s2
        let mult_group_dot = CExp::dot(CExp::varstr("s1"), CExp::varstr("s2"));
        assert!(mult_group_dot.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Create expression v1 . v1
        let vec_dot1 = CExp::dot(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(
            vec_dot1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create expression v1 . v2
        let vec_dot2 = CExp::dot(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_dot2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for concatenation
    #[test]
    fn test_binary_concat_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression v1 ++ v2
        let vec_concat = CExp::concat(CExp::varstr("v1"), CExp::varstr("v2"));

        assert_eq!(
            vec_concat.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::varstr("F"), 9))
        );

        // Create expression v1 ++ f1
        let fv1_concat = CExp::concat(CExp::varstr("v1"), CExp::varstr("f1"));

        assert_eq!(
            fv1_concat.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::varstr("F"), 6))
        );

        // Create expression f2 ++ v1
        let fv2_concat = CExp::concat(CExp::varstr("f2"), CExp::varstr("v2"));
        assert_eq!(
            fv2_concat.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::varstr("F"), 5))
        );
    }

    // Test for equality
    #[test]
    fn test_binary_equ_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create expression x == y
        let field_equ = CExp::equ(CExp::varstr("f1"), CExp::varstr("f2"));
        assert_eq!(field_equ.infer(&KIND_CTX, &fctx, &vctx), Ok(CTyp::Bool));

        // Create expression g1 == g2
        let group_equ = CExp::equ(CExp::varstr("g1"), CExp::varstr("g2"));
        assert_eq!(group_equ.infer(&KIND_CTX, &fctx, &vctx), Ok(CTyp::Bool));

        // Create expression s1 == s2
        let mult_group_equ = CExp::equ(CExp::varstr("s1"), CExp::varstr("s2"));
        assert_eq!(
            mult_group_equ.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Bool)
        );

        // Create expression v1 == v1
        let vec_equ1 = CExp::equ(CExp::varstr("v1"), CExp::varstr("v1"));
        assert_eq!(vec_equ1.infer(&KIND_CTX, &fctx, &vctx), Ok(CTyp::Bool));

        // Create expression v1 == v2
        let vec_equ2 = CExp::equ(CExp::varstr("v1"), CExp::varstr("v2"));
        assert!(vec_equ2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for vector creation
    #[test]
    fn test_vector_inference() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a vector expression [1, 2, 3]
        let lit_vec = CExp::vec(vec![CExp::lit(1), CExp::lit(2), CExp::lit(3)]);
        assert_eq!(
            lit_vec.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Fin(Range::new(1, 4)), 3))
        );

        // Create a vector expression [1, f1, 3]
        let lit_vec2 = CExp::vec(vec![CExp::lit(1), CExp::varstr("f1"), CExp::lit(3)]);
        assert_eq!(
            lit_vec2.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::varstr("F"), 3))
        );

        // Create a vector expression [1, f1, g1]
        let lit_vec_bad = CExp::vec(vec![CExp::lit(1), CExp::varstr("f1"), CExp::varstr("g1")]);
        assert!(lit_vec_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for error: empty vector
    #[test]
    fn test_empty_vector_error() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an empty vector expression []
        let empty = CExp::vec(vec![]);

        assert!(empty.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test interpolate
    #[test]
    fn test_interpolate() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Pow2 length required by the spec (radix-2 FFT).
        let interp1 = CExp::interpolate_grid(CExp::vec(vec![
            CExp::varstr("f1"),
            CExp::lit(2),
            CExp::lit(3),
            CExp::lit(5),
        ]));

        assert_eq!(
            interp1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, 4))
        );

        let interp_bad =
            CExp::interpolate_grid(CExp::vec(vec![CExp::varstr("f1"), CExp::varstr("g1")]));

        assert!(interp_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // Non-power-of-two length is rejected.
        let interp_non_pow2 = CExp::interpolate_grid(CExp::vec(vec![
            CExp::varstr("f1"),
            CExp::lit(2),
            CExp::lit(3),
        ]));
        assert!(interp_non_pow2.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    #[test]
    fn test_poly() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create an interpolation expressionin poly([1, 2, 3], [1, 2, 3])
        let interp1 = CExp::poly(CExp::vec(vec![
            CExp::varstr("f1"),
            CExp::lit(2),
            CExp::lit(3),
        ]));

        assert_eq!(
            interp1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, 3))
        );

        let interp_bad = CExp::poly(CExp::vec(vec![CExp::varstr("f1"), CExp::varstr("g1")]));

        assert!(interp_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    #[test]
    fn test_coef() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        let interp1 = CExp::coef(CExp::poly(CExp::vec(vec![
            CExp::varstr("f1"),
            CExp::lit(2),
            CExp::lit(3),
        ])));

        assert_eq!(
            interp1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), 3))
        );
    }

    // Test evaluation
    #[test]
    fn test_fft() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Pow2 length required by the spec (radix-2 FFT).
        let eval1 = CExp::evaluate_grid(CExp::interpolate_grid(CExp::vec(vec![
            CExp::varstr("f1"),
            CExp::lit(2),
            CExp::lit(3),
            CExp::lit(5),
        ])));

        assert_eq!(
            eval1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), 4))
        );

        let eval_bad = CExp::evaluate_grid(CExp::vec(vec![CExp::varstr("f1")]));

        assert!(eval_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Unary `eval(p)` is FFT-grid evaluation; only valid on univariate polynomials.
    // `m` in VAR_CTX has type Poly(F, 8, 1) (MLE in 8 vars), so eval(m) must be
    // rejected at the type-inference layer rather than silently producing
    // Vec(F, 256) and panicking later in Op::Fft.typ() at the IR level.
    #[test]
    fn test_evaluate_on_mle_rejected() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        let eval_mle = CExp::evaluate_grid(CExp::varstr("m"));

        assert!(eval_mle.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Characterization tests for CExp::Mle inference: pin the observable behavior
    // so the redundant-infer cleanup in this arm cannot silently regress it.
    #[test]
    fn test_mle_pow2_vec() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // v2: Vec(F, 4) — 4 = 2^2, so MLE in 2 vars.
        let m = CExp::mle(CExp::varstr("v2"));

        assert_eq!(
            m.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 2, 1))
        );
    }

    #[test]
    fn test_mle_rejects_scalar_arg() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // f1 is a scalar (not a vector); mle(f1) must be rejected.
        let m_bad = CExp::mle(CExp::varstr("f1"));

        assert!(m_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    #[test]
    fn test_mle_rejects_non_pow2_vec() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // v1: Vec(F, 5) — 5 is not a power of two; mle(v1) must be rejected.
        let m_bad = CExp::mle(CExp::varstr("v1"));

        assert!(m_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
    }

    // Test for function application
    #[test]
    fn test_app() {
        let fctx = Set::singleton(Sig {
            name: "fun".into(),
            typevars: TypeVars::from([
                TypeVar::new_str("F", Kind::Field),
                TypeVar::new_str("G", Kind::Group),
            ]),
            args: Args::from([
                CArg::public("a", CTyp::Base(Tid::from("F"))),
                CArg::public("b", CTyp::Base(Tid::from("F"))),
                CArg::public("c", CTyp::Base(Tid::from("G"))),
            ]),
            ret: CTyp::Base(Tid::from("G")),
        });

        let mut vctx = VAR_CTX.clone();

        // Create a function application fun(2, f1, g1)
        let app1 = CExp::app(
            "fun".into(),
            Exps::from([CExp::lit(2), CExp::varstr("f1"), CExp::varstr("g1")]),
        );

        assert!(app1.infer(&KIND_CTX, &Set::new(), &vctx).is_err());
        assert_eq!(
            app1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("G")))
        );

        // Create a function application fun(1, 2)
        let app2 = CExp::app("fun".into(), Exps::from([CExp::lit(1), CExp::lit(2)]));
        assert!(app2.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // A polynomial application to scalar
        let uni_app = CExp::app("p".into(), Exps::from([CExp::lit(1)]));
        assert_eq!(
            uni_app.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        let uni_app_vec = CExp::app("p".into(), Exps::from([CExp::varstr("v1")]));
        assert!(uni_app_vec.infer(&KIND_CTX, &fctx, &vctx).is_err());

        // A MLE application to scalar and vector of scalars
        let mle_app = CExp::app("m".into(), Exps::from([CExp::lit(1)]));
        assert_eq!(
            mle_app.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 7, 1))
        );

        let mle_app_vec = CExp::app("m".into(), Exps::from([CExp::varstr("v1")]));
        assert_eq!(
            mle_app_vec.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 3, 1))
        );
    }

    // Test for random access
    #[test]
    fn test_ram() {
        let fctx = Set::new();
        let mut vctx = VAR_CTX.clone();

        // Create a random access expression v1[2]
        let ram1 = CExp::ram(CExp::varstr("v1"), CExp::lit(2));

        assert_eq!(
            ram1.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F")))
        );

        // Create a random access expression v1[0..4]
        let ram2 = CExp::ram(CExp::varstr("v1"), CExp::range(Range::new(0, 4)));

        assert_eq!(
            ram2.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), 4))
        );
    }
}
