use crate::ast::range::{Range, RangeError};
use crate::ast::sig::CSig;
use crate::ast::spanned::Spanned;
use crate::ast::{BinOp, CExp, CExps};
use crate::id::{Tid, Vid};
use crate::typ::lub::LubError;
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, CTyps};
use share::{Ctx, Set};
use thiserror::Error;

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

    #[error("EvaluateError: Arguments to [eval] must be a polynomial and a scalar point or vector of scalars:\n\t{0}, {1} |- eval {2} {3}")]
    Evaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    #[error("EvaluateUnivariateVectorError: A univariate polynomial Poly<F,1,_> cannot be evaluated at a vector of points. Evaluate at a single scalar with `p(x)`, or write `[p(x) for x in points]` to evaluate at many points:\n\t{0}, {1} |- eval {2} {3}")]
    EvaluateUnivariateVector(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    #[error("SelectedEvaluateError: Arguments to [eval<{4}>] must be a polynomial Poly<F,N,D>, a nonempty contiguous free range within N, and exactly N-(range length) fixed scalars:\n\t{0}, {1} |- eval<{4}> {2} {3}")]
    SelectedEvaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp, Range<usize>),

    #[error("InternalInvariantError: selected eval must include explicit points/fixed values after parser conversion:\n\t{0}, {1} |- eval<{3}> {2}")]
    EvaluateSelectorWithoutPoints(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Range<usize>),

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

    #[error("ReduceAccError: reduce({2}, {3}) has element type {4}, but {2}({4}, {4}) = {5}, which differs from {4}; reduce requires the operator to have a fixed point at the element type:\n\t{0}, {1} |- reduce ({2}, {3} : Vec<{4}>)")]
    ReduceAcc(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, BinOp, CExp, CTyp, CTyp),

    #[error("UniError: Univariate polynomials over a field must be evaluated over a single scalar:\n\t{0}, {1} |- {2}( {3} : {4} )")]
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
        "EvaluateGridError: Unary [eval] requires the polynomial's coefficient count (m+1) to be a power of two; got max_degree={3} (m+1={3}+1 coefficients):\n\t{0}, {1} |- eval ( {2}: {4})"
    )]
    EvaluateGridNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize, CTyp),

    #[error("RamError: Index {4} must be a Fin type within the bounds of the vector {2}:\n\t{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    Ram(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("RamError: Index {4} must be a compile-time constant (literal or range), got {5}:\n\t{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    RamDynamicIndex(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    #[error("AppMultipleError: Function has multiple matching definitions in context\n\t{0} |- {1} ( {2} )")]
    AppMultiple(Set<CSig>, Vid, CTyps),

    #[error("FuncNotFound: No matching definition found for function:\n\t{0} |- {1} ( {2} )")]
    FuncNotFound(Set<CSig>, Vid, CTyps),

    #[error("UnitError: Expected unit-typed expression:\n\t{0}, {1} |- {2}")]
    Unit(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    #[error("ConstraintMismatchError: Constraint operands have incompatible types {4} vs {5}:\n\t{0}, {1} |- {2} == {3}")]
    ConstraintMismatch(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp, CTyp, CTyp),

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

impl TypeError {
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
    pub fn evaluate_univariate_vector(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        x: &CExp,
    ) -> Self {
        TypeError::EvaluateUnivariateVector(kctx.clone(), vctx.clone(), p.clone(), x.clone())
    }
    pub fn evaluate_selected(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        x: &CExp,
        range: Range<usize>,
    ) -> Self {
        TypeError::SelectedEvaluate(kctx.clone(), vctx.clone(), p.clone(), x.clone(), range)
    }
    pub fn evaluate_selector_without_points(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        range: Range<usize>,
    ) -> Self {
        TypeError::EvaluateSelectorWithoutPoints(kctx.clone(), vctx.clone(), p.clone(), range)
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
    pub fn ram_dynamic_index(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        a: &CExp,
        ta: CTyp,
        b: &CExp,
        tb: CTyp,
    ) -> Self {
        TypeError::RamDynamicIndex(kctx.clone(), vctx.clone(), a.clone(), ta, b.clone(), tb)
    }
    pub fn unit(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Unit(kctx.clone(), vctx.clone(), e.clone())
    }
    pub fn constraint_mismatch(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        lhs: &CExp,
        rhs: &CExp,
        ta: &CTyp,
        tb: &CTyp,
    ) -> Self {
        TypeError::ConstraintMismatch(
            kctx.clone(),
            vctx.clone(),
            lhs.clone(),
            rhs.clone(),
            ta.clone(),
            tb.clone(),
        )
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
        _fields: &Ctx<Spanned<String>, Spanned<CTyp>>,
    ) -> Self {
        TypeError::FieldNotFound(kctx.clone(), vctx.clone(), e.clone(), field.to_string())
    }
    pub fn not_a_record(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::NotARecord(kctx.clone(), vctx.clone(), e.clone(), t.clone())
    }
}
