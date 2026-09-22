use crate::ast::range::{Range, RangeError};
use crate::ast::sig::CSig;
use crate::ast::{BinOp, CExp, CExps};
use crate::id::{Tid, Vid};
use crate::typ::lub::LubError;
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, CTyps};
use share::{Ctx, Set};
use thiserror::Error;

/// User-facing failure of source-level type inference over a concretized module.
///
/// One variant exists per surface construct that carries a bespoke typing rule, so that
/// `Display` can print the full typing judgement `kctx, vctx |- e : t` that failed. Most
/// variants therefore capture the kind context (`Ctx<Tid, CKind>`), the variable context
/// (`Ctx<Vid, CTyp>`) and the offending expression alongside the inferred types. This is the
/// `lang`-level, user-directed error channel; shape violations discovered later in the IR are
/// invariants and panic instead.
#[derive(Error, PartialEq, Debug)]
pub enum TypeError {
    /// Wraps an inner error with the declaration whose body failed to type-check.
    #[error("TypeError: In declaration {0}:\n\n{1}")]
    Decl(Vid, Box<TypeError>),

    /// Chains two errors so that a specific failure can be reported with its follow-on cause.
    #[error("{0}\n\n{1}")]
    Next(Box<TypeError>, Box<TypeError>),

    /// Attaches the source span of the expression whose inference failed. Only the innermost
    /// spanned expression on the failing path is recorded; `Display` is unchanged.
    #[error("{1}")]
    Located(std::ops::Range<usize>, Box<TypeError>),

    /// A specification relation referenced transcript or randomness, so it is not a pure
    /// predicate over the statement and witness.
    #[error(
        "TypeError: Specification relation must be pure (no transcript and randomness):\n\t{0}"
    )]
    NotPureRel(CExp),

    /// A `where` clause inferred to something other than `Bool`.
    #[error("TypeError: where clause must infer to Bool, got {0}:\n\t{1}")]
    RelationNotBool(CTyp, CExp),

    /// A source type has no `ATyp` image, i.e. it cannot be lowered to an `arkworks` runtime
    /// type under the current kind context.
    #[error("TypeError: Cannot find an Arkworks type for {0}, {1} |- {2} : {3}")]
    Ark(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// Generic inference failure for an expression with no more specific variant.
    #[error("TypeError: In expression {0}, {1} |- {2}")]
    CExp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// An empty vector literal has no element type to infer from.
    #[error("VecEmptyError: Cannot infer the type of the empty vector {0}, {1} |- []")]
    VecEmpty(Ctx<Tid, CKind>, Ctx<Vid, CTyp>),

    /// Two elements of a vector literal failed `lub_equ`, so the literal has no single element
    /// type; the boxed error is the underlying least-upper-bound failure.
    #[error(
        "VecTypeError: Vector elements must have the same type: {0}, {1} |- {2} != {3} \n\n\t{4}"
    )]
    Vec(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CTyp, CTyp, Box<TypeError>),

    /// The argument list of `interpolate` was not a pair of field vectors.
    #[error("InterpolateError: Arguments to [interpolate] must be vectors of fields:\n\t{0}, {1} |- interpolate {2}")]
    Interpolate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// The single argument of the one-argument `interpolate` form was not a field vector.
    #[error("InterpolateError: Unary [interpolate] expects a vector of fields:\n\t{0}, {1} |- interpolate {2}")]
    InterpolateUnary(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// Unary `interpolate` lowers to an inverse FFT, so its input vector length must be a power
    /// of two; the offending length is carried as the last component.
    #[error(
        "InterpolateError: Unary [interpolate] requires a vector whose length is a power of two; got n={3}:\n\t{0}, {1} |- interpolate {2}"
    )]
    InterpolateUnaryNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize),

    /// `poly` was applied to something other than a vector of field elements.
    #[error("PolyError: Argument to [poly] must be a vector of fields:\n\t{0}, {1} |- poly {2}")]
    Poly(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// Polynomial evaluation received operands that are not a polynomial applied to a scalar
    /// point or a vector of scalar points.
    #[error("EvaluateError: Arguments to [eval] must be a polynomial and a scalar point or vector of scalars:\n\t{0}, {1} |- eval {2} {3}")]
    Evaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    /// A univariate polynomial was applied to a vector of points; univariate evaluation takes a
    /// single scalar, and batching must be written as an explicit comprehension.
    #[error("EvaluateUnivariateVectorError: A univariate polynomial Poly<F,1,_> cannot be evaluated at a vector of points. Evaluate at a single scalar with `p(x)`, or write `[p(x) for x in points]` to evaluate at many points:\n\t{0}, {1} |- eval {2} {3}")]
    EvaluateUnivariateVector(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    /// Partial evaluation `eval<range>` was given a bad selector: the free range must be a
    /// nonempty contiguous window inside the polynomial's variables, and the remaining
    /// variables must each receive exactly one fixed scalar.
    #[error("SelectedEvaluateError: Arguments to [eval<{4}>] must be a polynomial Poly<F,N,D>, a nonempty contiguous free range within N, and exactly N-(range length) fixed scalars:\n\t{0}, {1} |- eval<{4}> {2} {3}")]
    SelectedEvaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp, Range<usize>),

    /// Internal invariant breach: a selected-evaluation node survived parser conversion without
    /// the explicit point and fixed-value arguments that lowering requires.
    #[error("InternalInvariantError: selected eval must include explicit points/fixed values after parser conversion:\n\t{0}, {1} |- eval<{3}> {2}")]
    EvaluateSelectorWithoutPoints(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Range<usize>),

    /// A multilinear extension was applied to more points than it has variables.
    #[error("EvaluateMleTooManyArgumentsError: Arguments to [eval] for a multilinear extension had too many arguments:\n\t{0}, {1} |- evalMle {2} {3}")]
    EvaluateMleTooManyArguments(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    /// `coef` was applied to a non-polynomial; only polynomials expose a coefficient vector.
    #[error("CoefError: Arguments to [coef] must be a polynomial:\n\t{0}, {1} |- coef {2}")]
    Coef(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// `mle` requires a vector whose length is a power of two, since the multilinear encoding
    /// stores `2^n` evaluation slots.
    #[error("MleError: Arguments to [mle] must be a vector type with size a power of 2:\n\t{0}, {1} |- mle {2}")]
    Mle(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// A multilinear extension was applied to arguments that are neither scalars nor vectors of
    /// scalars.
    #[error("MleError: Must apply MLE to a scalar or vector of scalars:\n\t{0}, {1} |- {2} ( {3} : {4} )")]
    MleApp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Vid, CExps, CTyps),

    /// The source of a `for` comprehension did not infer to a vector type.
    #[error(
        "MapError: Arguments to [for] must be a vector type:\n\t{0}, {1} |- [{2} for {3} in {4}]"
    )]
    Map(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Vid, CExp),

    /// `reduce` was applied to an expression that is not a vector.
    #[error("ReduceError: Arguments to [reduce] must be a vector type:\n\t{0}, {1} |- reduce ({2}, {3} : {4})")]
    Reduce(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, BinOp, CExp, CTyp),

    /// The reduction operator is not closed over the element type: `lub_op` of the element type
    /// with itself produced a different type, so the accumulator has no fixed point.
    #[error("ReduceAccError: reduce({2}, {3}) has element type {4}, but {2}({4}, {4}) = {5}, which differs from {4}; reduce requires the operator to have a fixed point at the element type:\n\t{0}, {1} |- reduce ({2}, {3} : Vec<{4}>)")]
    ReduceAcc(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, BinOp, CExp, CTyp, CTyp),

    /// A univariate polynomial was applied to arguments other than one scalar point.
    #[error("UniError: Univariate polynomials over a field must be evaluated over a single scalar:\n\t{0}, {1} |- {2}( {3} : {4} )")]
    Uni(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Vid, CExps, CTyps),

    /// A Fiat-Shamir `challenge` was asked to produce a non-field value; challenges are drawn
    /// from the scalar field only.
    #[error("ChallengeError: Only challenges returning field elements are allowed:\n\t {0}, {1} |- challenge< {2} : {3} >")]
    Challenge(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Tid, CKind),

    /// A variable occurrence has no binding in the variable context.
    #[error("VarError: Variable {0} not found in context {1}")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),

    /// A range expression is ill-formed; the wrapped `RangeError` states why.
    #[error("RangeError: Not a valid range expression:\n\t{0}, {1} |- {2}\n\n{3}")]
    Range(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Range<usize>, RangeError),

    /// `interpolate` argument inferred to a type that is not a field vector; carries the type
    /// actually inferred.
    #[error("InterpolateError: Expects a field vector:\n\t{0}, {1} |- interpolate ( {2}: {3})")]
    Interp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// Unary `eval` (evaluation over the full FFT/boolean grid) was applied to a value that is
    /// neither a univariate polynomial nor a multilinear extension.
    #[error("EvaluateGridError: Expects a polynomial (univariate or MLE):\n\t{0}, {1} |- eval ( {2}: {3})")]
    EvaluateGrid(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// Unary `eval` lowers to a forward FFT, so a univariate operand must have a power-of-two
    /// coefficient count `m + 1`; the offending `max_degree` is carried as the fourth field.
    #[error(
        "EvaluateGridError: Unary [eval] requires the polynomial's coefficient count (m+1) to be a power of two; got max_degree={3} (m+1={3}+1 coefficients):\n\t{0}, {1} |- eval ( {2}: {4})"
    )]
    EvaluateGridNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize, CTyp),

    /// A vector index is not a `Fin` type bounded by the vector's length, so the access cannot
    /// be proven in range.
    #[error("RamError: Index {4} must be a Fin type within the bounds of the vector {2}:\n\t{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    Ram(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    /// A vector index depends on runtime data; indices must be compile-time literals or ranges
    /// because the DAG is statically shaped.
    #[error("RamError: Index {4} must be a compile-time constant (literal or range), got {5}:\n\t{0}, {1} |- {2} : {3} [ {4} : {5} ]")]
    RamDynamicIndex(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    /// Overload resolution found more than one signature in the function context matching the
    /// call's argument types.
    #[error("AppMultipleError: Function has multiple matching definitions in context\n\t{0} |- {1} ( {2} )")]
    AppMultiple(Set<CSig>, Vid, CTyps),

    /// Overload resolution found no signature matching the call's argument types.
    #[error("FuncNotFound: No matching definition found for function:\n\t{0} |- {1} ( {2} )")]
    FuncNotFound(Set<CSig>, Vid, CTyps),

    /// An expression used in statement position did not infer to the unit type.
    #[error("UnitError: Expected unit-typed expression:\n\t{0}, {1} |- {2}")]
    Unit(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// The two sides of a `==` constraint have types with no common upper bound.
    #[error("ConstraintMismatchError: Constraint operands have incompatible types {4} vs {5}:\n\t{0}, {1} |- {2} == {3}")]
    ConstraintMismatch(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp, CTyp, CTyp),

    /// A function body's inferred type disagrees with its declared return type; the fifth field
    /// is the declared type and the sixth the inferred one.
    #[error("FuncRetError: The return type of function {3} must be {4} but is found:\n\t{0}, {1} |- {2} : {5}")]
    FuncRet(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Vid, CTyp, CTyp),

    /// `pair` was applied to operands that are not a `G1`/`G2` pair of a pairing-friendly curve
    /// declared in the kind context.
    #[error("PairError: Expected group pairing between two pairing-friendly curves:\n\t{0}, {1} |- pair({2}: {3}, {4} : {5})")]
    Pair(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    /// A record projection named a field the record type does not declare.
    #[error("RecordError: Field {3} not found in record:\n\t{0}, {1} |- {2}.{3}")]
    FieldNotFound(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, String),

    /// A field projection was applied to an expression whose type is not a record.
    #[error("RecordError: Expression is not a record type:\n\t{0}, {1} |- {2} : {3}")]
    NotARecord(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// A kind-aware unification step failed; see `UnifyError`.
    #[error(transparent)]
    Unify(#[from] UnifyError),

    /// A least-upper-bound computation failed; see `LubError`.
    #[error(transparent)]
    Lub(#[from] LubError),
}

impl TypeError {
    /// Attributes an existing error to the declaration `id` currently being checked.
    pub fn decl(id: &Vid, e: TypeError) -> Self {
        TypeError::Decl(id.clone(), Box::new(e))
    }
    /// Attaches `span` to `e` unless `e` already carries a location or `span` is a dummy
    /// (empty) span, so the innermost real location wins.
    pub fn located(span: &std::ops::Range<usize>, e: TypeError) -> Self {
        if span.is_empty() || e.span().is_some() {
            e
        } else {
            TypeError::Located(span.clone(), Box::new(e))
        }
    }
    /// Source span of the innermost located sub-error, if inference recorded one.
    pub fn span(&self) -> Option<std::ops::Range<usize>> {
        match self {
            TypeError::Located(span, e) => e.span().or_else(|| Some(span.clone())),
            TypeError::Next(a, b) => b.span().or_else(|| a.span()),
            TypeError::Decl(_, e) | TypeError::Vec(_, _, _, _, e) => e.span(),
            _ => None,
        }
    }
    /// The most specific error in the chain, skipping location, declaration, and
    /// parent-expression wrappers.
    pub fn cause(&self) -> &TypeError {
        match self {
            TypeError::Located(_, e) | TypeError::Decl(_, e) | TypeError::Next(_, e) => e.cause(),
            _ => self,
        }
    }
    /// A one-line description of [`Self::cause`], without the kind and variable contexts
    /// that the full `Display` prints.
    pub fn summary(&self) -> String {
        fn short(e: &impl std::fmt::Display) -> String {
            const MAX: usize = 80;
            let s = e
                .to_string()
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ");
            if s.chars().count() > MAX {
                format!("{}...", s.chars().take(MAX).collect::<String>())
            } else {
                s
            }
        }
        match self.cause() {
            TypeError::CExp(_, _, e @ CExp::Map(..)) => format!(
                "MapError: A [for] comprehension must range over a non-empty vector: `{}`",
                short(e)
            ),
            TypeError::CExp(_, _, e) => format!("TypeError: ill-typed expression `{}`", short(e)),
            TypeError::VecEmpty(..) => {
                "VecEmptyError: Cannot infer the type of an empty vector".to_string()
            }
            TypeError::Vec(_, _, a, b, _) => {
                format!("VecTypeError: Vector elements must have the same type: {a} != {b}")
            }
            TypeError::Ark(_, _, e, t) => format!(
                "TypeError: Cannot find an Arkworks type for `{}` : {t}",
                short(e)
            ),
            TypeError::VarNotFound(v, _) => format!("VarError: Variable {v} not found"),
            e => e
                .to_string()
                .lines()
                .next()
                .unwrap_or_default()
                .trim_end_matches([':', ' '])
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" "),
        }
    }
    /// Chains `b` after `a` so both the specific failure and its cause are reported.
    pub fn next(a: Self, b: Self) -> Self {
        TypeError::Next(Box::new(a), Box::new(b))
    }
    /// Chains a unification failure `u` behind the higher-level error `a`.
    pub fn unify(a: Self, u: UnifyError) -> Self {
        TypeError::next(a, TypeError::from(u))
    }
    /// Reports that specification relation `e` is not pure.
    pub fn not_pure_rel(e: &CExp) -> Self {
        TypeError::NotPureRel(e.clone())
    }
    /// Reports that a `where` clause `e` inferred to `t` instead of `Bool`.
    pub fn relation_not_bool(t: &CTyp, e: &CExp) -> Self {
        TypeError::RelationNotBool(t.clone(), e.clone())
    }
    /// Chains a least-upper-bound failure `l` behind the higher-level error `a`.
    pub fn lub(a: Self, l: LubError) -> Self {
        TypeError::next(a, TypeError::from(l))
    }
    /// Reports that type `t` of `e` has no `arkworks` (`ATyp`) image under `kctx`.
    pub fn ark(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::Ark(kctx.clone(), vctx.clone(), e.clone(), t.clone())
    }
    /// Reports a generic inference failure for expression `e` under the given contexts.
    pub fn exp(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::CExp(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports that an empty vector literal has no inferable element type.
    pub fn vec_empty(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VecEmpty(kctx.clone(), vctx.clone())
    }
    /// Reports two vector element types `e` and `t` that failed to unify, carrying the
    /// underlying failure `r`.
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
    /// Reports ill-typed arguments to the two-argument `interpolate` form.
    pub fn interpolate(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Interpolate(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports that the unary `interpolate` argument is not a field vector.
    pub fn interpolate_unary(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::InterpolateUnary(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports that unary `interpolate` got a vector of non-power-of-two length `n`.
    pub fn interpolate_unary_not_pow2(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        n: usize,
    ) -> Self {
        TypeError::InterpolateUnaryNotPow2(kctx.clone(), vctx.clone(), e.clone(), n)
    }
    /// Reports that unary `eval` got a polynomial of type `t` whose degree `n` yields a
    /// non-power-of-two coefficient count.
    pub fn evaluate_grid_not_pow2(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        n: usize,
        t: &CTyp,
    ) -> Self {
        TypeError::EvaluateGridNotPow2(kctx.clone(), vctx.clone(), e.clone(), n, t.clone())
    }
    /// Reports that `poly` was applied to a non-field-vector argument.
    pub fn poly(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Poly(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports that `coef` was applied to a non-polynomial argument.
    pub fn coef(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Coef(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports that evaluating polynomial `p` at point `x` is ill-typed.
    pub fn evaluate(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, p: &CExp, x: &CExp) -> Self {
        TypeError::Evaluate(kctx.clone(), vctx.clone(), p.clone(), x.clone())
    }
    /// Reports that univariate polynomial `p` was applied to a vector of points `x`.
    pub fn evaluate_univariate_vector(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        x: &CExp,
    ) -> Self {
        TypeError::EvaluateUnivariateVector(kctx.clone(), vctx.clone(), p.clone(), x.clone())
    }
    /// Reports an ill-formed partial evaluation `eval<range>` of `p` at `x`.
    pub fn evaluate_selected(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        x: &CExp,
        range: Range<usize>,
    ) -> Self {
        TypeError::SelectedEvaluate(kctx.clone(), vctx.clone(), p.clone(), x.clone(), range)
    }
    /// Reports the internal invariant breach of a selector-bearing `eval` that carries no
    /// point arguments after parser conversion.
    pub fn evaluate_selector_without_points(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        range: Range<usize>,
    ) -> Self {
        TypeError::EvaluateSelectorWithoutPoints(kctx.clone(), vctx.clone(), p.clone(), range)
    }
    /// Reports that multilinear extension `p` was applied to more points than it has variables.
    pub fn evaluate_mle_too_many_arguments(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        p: &CExp,
        x: &CExp,
    ) -> Self {
        TypeError::EvaluateMleTooManyArguments(kctx.clone(), vctx.clone(), p.clone(), x.clone())
    }
    /// Reports that `mle` was applied to something other than a power-of-two-length vector.
    pub fn mle(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Mle(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports that multilinear extension `id` was applied to arguments `e` of types `t` that
    /// are neither scalars nor scalar vectors.
    pub fn mle_app(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        id: &Vid,
        e: &CExps,
        t: &CTyps,
    ) -> Self {
        TypeError::MleApp(kctx.clone(), vctx.clone(), id.clone(), e.clone(), t.clone())
    }
    /// Reports that the source `r` of the comprehension `[e for id in r]` is not a vector.
    pub fn map(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: CExp, id: Vid, r: CExp) -> Self {
        TypeError::Map(kctx.clone(), vctx.clone(), e, id, r)
    }
    /// Reports that `reduce(op, e)` was given an operand `e` of non-vector type `t`.
    pub fn reduce(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        op: BinOp,
        e: &CExp,
        t: &CTyp,
    ) -> Self {
        TypeError::Reduce(kctx.clone(), vctx.clone(), op, e.clone(), t.clone())
    }
    /// Reports that univariate polynomial `id` was applied to argument list `e` of types `ts`
    /// rather than to a single scalar.
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
    /// Reports a `challenge` whose requested type `t` has non-field kind `k`.
    pub fn challenge(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, t: &Tid, k: &CKind) -> Self {
        TypeError::Challenge(kctx.clone(), vctx.clone(), t.clone(), k.clone())
    }
    /// Reports that variable `id` is unbound in `vctx`.
    pub fn var_not_found(id: &Vid, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VarNotFound(id.clone(), vctx.clone())
    }
    /// Reports an invalid range `r`, carrying the originating `RangeError`.
    pub fn range(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        r: &Range<usize>,
        e: RangeError,
    ) -> Self {
        TypeError::Range(kctx.clone(), vctx.clone(), r.clone(), e)
    }
    /// Reports that the `interpolate` operand `a` has type `ta`, which is not a field vector.
    pub fn interp(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, a: &CExp, ta: &CTyp) -> Self {
        TypeError::Interp(kctx.clone(), vctx.clone(), a.clone(), ta.clone())
    }
    /// Reports that unary `eval` operand `a` has non-polynomial type `ta`.
    pub fn evaluate_grid(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        a: &CExp,
        ta: &CTyp,
    ) -> Self {
        TypeError::EvaluateGrid(kctx.clone(), vctx.clone(), a.clone(), ta.clone())
    }
    /// Reports an out-of-bounds-capable index `b` of type `tb` into the vector `a` of type `ta`.
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
    /// Reports a runtime-dependent index `b` of type `tb` into the vector `a` of type `ta`.
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
    /// Reports that expression `e` in statement position is not unit-typed.
    pub fn unit(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp) -> Self {
        TypeError::Unit(kctx.clone(), vctx.clone(), e.clone())
    }
    /// Reports a constraint `lhs == rhs` whose sides have incompatible types `ta` and `tb`.
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
    /// Reports that call `id(params)` matches several signatures in `fctx`.
    pub fn app_multiple(fctx: &Set<CSig>, id: &Vid, params: CTyps) -> Self {
        TypeError::AppMultiple(fctx.clone(), id.clone(), params)
    }
    /// Reports that call `id(params)` matches no signature in `fctx`.
    pub fn func_not_found(fctx: &Set<CSig>, id: &Vid, params: CTyps) -> Self {
        TypeError::FuncNotFound(fctx.clone(), id.clone(), params)
    }
    /// Reports that the body `e` of function `id` inferred to `r` instead of its declared
    /// return type `t`.
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
    /// Reports that `pair(t, e)` with operand types `ta` and `te` is not a valid `G1`/`G2`
    /// pairing under `kctx`.
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
    /// Reports that record expression `e` has no field named `field`.
    pub fn field_not_found(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        field: &str,
    ) -> Self {
        TypeError::FieldNotFound(kctx.clone(), vctx.clone(), e.clone(), field.to_string())
    }
    /// Reports that `e` has type `t`, which is not a record, so projection is ill-typed.
    pub fn not_a_record(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::NotARecord(kctx.clone(), vctx.clone(), e.clone(), t.clone())
    }
}
