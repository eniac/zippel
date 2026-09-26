use crate::ast::range::{Range, RangeError};
use crate::ast::sig::CSig;
use crate::ast::spanned::Spanned;
use crate::ast::{BinOp, CExp, CExps};
use crate::diagnostic::{Applicability, Diagnostic, Phase};
use crate::id::{Tid, Vid};
use crate::semantic::levenshtein;
use crate::typ::lub::{describe_bin, LubError};
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, CTyps};
use share::{Ctx, Set};
use thiserror::Error;

/// User-facing failure of source-level type inference over a concretized module.
///
/// One variant exists per surface construct that carries a bespoke typing rule. `Display` is
/// the one-line message shown to users: wrappers (`Decl`, `Next`, `Located`) display their
/// cause, and no message repeats the offending expression, which a diagnostic's span shows.
/// Most variants also capture the kind context (`Ctx<Tid, CKind>`), the variable context
/// (`Ctx<Vid, CTyp>`) and the offending expression, so `Debug` shows the full typing judgement
/// `kctx, vctx |- e : t` that failed. This is the `lang`-level, user-directed error channel;
/// shape violations discovered later in the IR are invariants and panic instead.
#[derive(Error, PartialEq, Debug)]
pub enum TypeError {
    /// Wraps an inner error with the declaration whose body failed to type-check.
    #[error("{1}")]
    Decl(Vid, Box<TypeError>),

    /// Chains two errors so that a specific failure can be reported with its follow-on cause.
    #[error("{1}")]
    Next(Box<TypeError>, Box<TypeError>),

    /// Attaches the source span of the expression whose inference failed. Only the innermost
    /// spanned expression on the failing path is recorded; `Display` is unchanged.
    #[error("{1}")]
    Located(std::ops::Range<usize>, Box<TypeError>),

    /// A specification relation referenced transcript or randomness, so it is not a pure
    /// predicate over the statement and witness.
    #[error("A `where` clause cannot use the transcript or randomness")]
    NotPureRel(CExp),

    /// A `where` clause inferred to something other than `Bool`.
    #[error("A `where` clause must be a boolean condition, but this has type {}", kinded(.1, .0))]
    RelationNotBool(Ctx<Tid, CKind>, CTyp, CExp),

    /// A source type has no `ATyp` image, i.e. it cannot be lowered to an `arkworks` runtime
    /// type under the current kind context.
    #[error("Type {} is not supported by the arkworks backend", kinded(.3, .0))]
    Ark(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// Generic inference failure for an expression with no more specific variant.
    #[error("Ill-typed expression")]
    CExp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// A binary operator was applied to operand types it is not defined on. The operand types
    /// are spanned at the operands; the `LubError` is the underlying failure.
    #[error("{}", describe_bin(*.3, &kinded(.4, .0), &kinded(.5, .0)))]
    Bin(
        Ctx<Tid, CKind>,
        Ctx<Vid, CTyp>,
        CExp,
        BinOp,
        Spanned<CTyp>,
        Spanned<CTyp>,
        LubError,
    ),

    /// The condition of a `verify` or `assert` is not a boolean.
    #[error("`{}` expects a boolean condition, but this has type {}", condition_keyword(.2), kinded(.3, .0))]
    Condition(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// The body of a `fun` has a type its variables cannot make into a polynomial; carries the
    /// `fun`, its number of variables, and the body's type.
    #[error("{}", fun_body_message(*.3, &kinded(.4, .0)))]
    FunBody(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize, CTyp),

    /// An empty vector literal has no element type to infer from.
    #[error("Cannot infer the element type of an empty vector")]
    VecEmpty(Ctx<Tid, CKind>, Ctx<Vid, CTyp>),

    /// Two elements of a vector literal failed `lub_equ`, so the literal has no single element
    /// type; the boxed error is the underlying least-upper-bound failure.
    #[error("Vector elements must all have the same type, but found {} and {}", kinded(.3, .0), kinded(.2, .0))]
    Vec(
        Ctx<Tid, CKind>,
        Ctx<Vid, CTyp>,
        Spanned<CTyp>,
        Spanned<CTyp>,
        Box<TypeError>,
        CExp,
        CExp,
    ),

    /// The argument list of `interpolate` was not a pair of field vectors.
    #[error("`interpolate` expects vectors of field elements")]
    Interpolate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// The single argument of the one-argument `interpolate` form was not a field vector.
    #[error("`interpolate` expects a vector of field elements")]
    InterpolateUnary(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// Unary `interpolate` lowers to an inverse FFT, so its input vector length must be a power
    /// of two; the offending length is carried as the last component.
    #[error(
        "`interpolate` needs a vector whose length is a power of two, but this has length {3}"
    )]
    InterpolateUnaryNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize),

    /// `poly` was applied to something other than a vector of field elements.
    #[error("`poly` expects a vector of field elements")]
    Poly(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// Polynomial evaluation received operands that are not a polynomial applied to a scalar
    /// point or a vector of scalar points.
    #[error("A polynomial can only be evaluated at a scalar or a vector of scalars")]
    Evaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    /// A univariate polynomial was applied to a vector of points; univariate evaluation takes a
    /// single scalar, and batching must be written as an explicit comprehension.
    #[error(
        "A univariate polynomial cannot be evaluated at a vector of points; evaluate at one point with `p(x)`, or write `[p(x) for x in points]`"
    )]
    EvaluateUnivariateVector(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    /// Partial evaluation `eval<range>` was given a bad selector: the free range must be a
    /// nonempty contiguous window inside the polynomial's variables, and the remaining
    /// variables must each receive exactly one fixed scalar.
    #[error(
        "`eval<{4}>` needs a polynomial, a non-empty contiguous range of its variables, and one fixed scalar for each remaining variable"
    )]
    SelectedEvaluate(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp, Range<usize>),

    /// Internal invariant breach: a selected-evaluation node survived parser conversion without
    /// the explicit point and fixed-value arguments that lowering requires.
    #[error("Internal compiler error: `eval<{3}>` lost its point arguments during parsing")]
    EvaluateSelectorWithoutPoints(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Range<usize>),

    /// A multilinear extension was applied to more points than it has variables.
    #[error("Too many evaluation points for this multilinear extension")]
    EvaluateMleTooManyArguments(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp),

    /// `coef` was applied to a non-polynomial; only polynomials expose a coefficient vector.
    #[error("`coef` expects a polynomial")]
    Coef(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// `mle` requires a vector whose length is a power of two, since the multilinear encoding
    /// stores `2^n` evaluation slots.
    #[error("`mle` expects a vector whose length is a power of two")]
    Mle(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp),

    /// A multilinear extension was applied to arguments that are neither scalars nor vectors of
    /// scalars.
    #[error("Multilinear extension `{2}` must be applied to scalars or a vector of scalars, but got {}", kinded_list(.4, .0))]
    MleApp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Vid, CExps, CTyps),

    /// The source of a `for` comprehension did not infer to a non-empty vector type; carries
    /// the type actually inferred.
    #[error("A `for` comprehension must range over a non-empty vector, but this has type {}", kinded(.5, .0))]
    Map(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, Vid, CExp, CTyp),

    /// `reduce` was applied to an expression that is not a vector.
    #[error("`reduce` expects a vector, but got {}", kinded(.4, .0))]
    Reduce(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, BinOp, CExp, CTyp),

    /// The reduction operator is not closed over the element type: `lub_op` of the element type
    /// with itself produced a different type, so the accumulator has no fixed point.
    #[error("`reduce` with `{op}` needs `{op}` to keep the element type {elem}, but it gives {res}", op = .2, elem = kinded(.4, .0), res = kinded(.5, .0))]
    ReduceAcc(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, BinOp, CExp, CTyp, CTyp),

    /// A univariate polynomial was applied to arguments other than one scalar point.
    #[error("Univariate polynomial `{2}` must be evaluated at a single scalar, but got {}", kinded_list(.4, .0))]
    Uni(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Vid, CExps, CTyps),

    /// A Fiat-Shamir `challenge` was asked to produce a non-field value; challenges are drawn
    /// from the scalar field only.
    #[error("Challenges must be field elements, but {2} has kind {3}")]
    Challenge(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Tid, CKind),

    /// A variable occurrence has no binding in the variable context.
    #[error("Variable `{0}` is not defined")]
    VarNotFound(Vid, Ctx<Vid, CTyp>),

    /// A range expression is ill-formed; the wrapped `RangeError` states why.
    #[error("Invalid range {2}: {3}")]
    Range(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, Range<usize>, RangeError),

    /// `interpolate` argument inferred to a type that is not a field vector; carries the type
    /// actually inferred.
    #[error("`interpolate` expects a vector of field elements, but got {}", kinded(.3, .0))]
    Interp(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// Unary `eval` (evaluation over the full FFT/boolean grid) was applied to a value that is
    /// neither a univariate polynomial nor a multilinear extension.
    #[error("`eval` expects a univariate polynomial or a multilinear extension, but got {}", kinded(.3, .0))]
    EvaluateGrid(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// Unary `eval` lowers to a forward FFT, so a univariate operand must have a power-of-two
    /// coefficient count `m + 1`; the offending `max_degree` is carried as the fourth field.
    #[error(
        "`eval` needs a polynomial with a power-of-two number of coefficients, but this has degree {3}"
    )]
    EvaluateGridNotPow2(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, usize, CTyp),

    /// A vector index is not a `Fin` type bounded by the vector's length, so the access cannot
    /// be proven in range.
    #[error("{}", index_message(.2, .3, .4, .0))]
    Ram(
        Ctx<Tid, CKind>,
        Ctx<Vid, CTyp>,
        CExp,
        Spanned<CTyp>,
        Spanned<CTyp>,
    ),

    /// A vector index depends on runtime data; indices must be compile-time literals or ranges
    /// because the DAG is statically shaped.
    #[error("Index `{}` must be a compile-time constant, but has type {}", ram_index_text(.2), kinded(.4, .0))]
    RamDynamicIndex(
        Ctx<Tid, CKind>,
        Ctx<Vid, CTyp>,
        CExp,
        Spanned<CTyp>,
        Spanned<CTyp>,
    ),

    /// Overload resolution found more than one signature in the function context matching the
    /// call's argument types.
    #[error("Call to `{2}` is ambiguous: several definitions accept arguments of type {}", kinded_list(.3, .0))]
    AppMultiple(Ctx<Tid, CKind>, Set<CSig>, Spanned<Vid>, CTyps, CExps),

    /// Overload resolution found no signature matching the call's argument types.
    #[error("{}", func_not_found_message(.1, .2, .3, .0))]
    FuncNotFound(Ctx<Tid, CKind>, Set<CSig>, Spanned<Vid>, CTyps, CExps),

    /// A protocol body ended in an expression that is not unit-typed; carries its type.
    #[error("A protocol body must end in a statement such as `verify(...)`, but this has type {}", kinded(.3, .0))]
    Unit(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp),

    /// The two sides of a `==` constraint have types with no common upper bound.
    #[error("{}", describe_bin(BinOp::Equ, &kinded(.4, .0), &kinded(.5, .0)))]
    ConstraintMismatch(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CExp, CTyp, CTyp),

    /// A function body's inferred type disagrees with its declared return type; the fifth field
    /// is the declared type and the sixth the inferred one.
    #[error("Function `{3}` must return {}, but {}", kinded(.4, .0), body_result(.5, .0))]
    FuncRet(
        Ctx<Tid, CKind>,
        Ctx<Vid, CTyp>,
        CExp,
        Vid,
        Spanned<CTyp>,
        CTyp,
    ),

    /// `pair` was applied to operands that are not a `G1`/`G2` pair of a pairing-friendly curve
    /// declared in the kind context.
    #[error("`pair` expects the two groups of a pairing-friendly curve, but got {} and {}", kinded(.3, .0), kinded(.5, .0))]
    Pair(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, CTyp, CExp, CTyp),

    /// A record projection named a field the record type does not declare.
    #[error("Record has no field `{3}`")]
    FieldNotFound(Ctx<Tid, CKind>, Ctx<Vid, CTyp>, CExp, String),

    /// A field projection was applied to an expression whose type is not a record.
    #[error("Expected a record, but got {}", kinded(.3, .0))]
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
            TypeError::Decl(_, e) | TypeError::Vec(_, _, _, _, e, ..) => e.span(),
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
    pub fn relation_not_bool(kctx: &Ctx<Tid, CKind>, t: &CTyp, e: &CExp) -> Self {
        TypeError::RelationNotBool(kctx.clone(), t.clone(), e.clone())
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
    /// Reports that binary expression `e` applies `op` to operands of types `a` and `b`, on
    /// which it is not defined; `l` is the underlying least-upper-bound failure.
    pub fn bin(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        a: &CTyp,
        b: &CTyp,
        l: LubError,
    ) -> Self {
        let CExp::Bin(op, x, y) = e else {
            unreachable!("`TypeError::bin` is only raised for binary expressions")
        };
        TypeError::Bin(
            kctx.clone(),
            vctx.clone(),
            e.clone(),
            *op,
            Spanned::new(a.clone(), x.span.clone()),
            Spanned::new(b.clone(), y.span.clone()),
            l,
        )
    }

    /// Reports that the condition of the `verify`/`assert` statement `e` has type `t`, not
    /// `Bool`.
    pub fn condition(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::Condition(kctx.clone(), vctx.clone(), e.clone(), t.clone())
    }

    /// Reports that the body of the `fun` `e`, over `vars` variables, has type `t`.
    pub fn fun_body(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        vars: usize,
        t: &CTyp,
    ) -> Self {
        TypeError::FunBody(kctx.clone(), vctx.clone(), e.clone(), vars, t.clone())
    }
    /// Reports that an empty vector literal has no inferable element type.
    pub fn vec_empty(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>) -> Self {
        TypeError::VecEmpty(kctx.clone(), vctx.clone())
    }
    /// Reports that element `elem` of type `elem_typ` does not unify with the first element
    /// `first` of type `first_typ`; `r` is the underlying failure.
    pub fn vec(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        elem: &Spanned<CExp>,
        elem_typ: &CTyp,
        first: &Spanned<CExp>,
        first_typ: &CTyp,
        r: TypeError,
    ) -> Self {
        TypeError::Vec(
            kctx.clone(),
            vctx.clone(),
            Spanned::new(elem_typ.clone(), elem.span.clone()),
            Spanned::new(first_typ.clone(), first.span.clone()),
            Box::new(r),
            elem.node.clone(),
            first.node.clone(),
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
    /// Reports that the source `r` of the comprehension `[e for id in r]` has type `t`, which
    /// is not a non-empty vector.
    pub fn map(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        id: &Vid,
        r: &CExp,
        t: &CTyp,
    ) -> Self {
        TypeError::Map(
            kctx.clone(),
            vctx.clone(),
            e.clone(),
            id.clone(),
            r.clone(),
            t.clone(),
        )
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
    /// Reports that the index of `e` (`a[b]`), of type `tb`, may be out of bounds for `a` of
    /// type `ta`.
    pub fn ram(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        ta: CTyp,
        tb: CTyp,
    ) -> Self {
        let (a, b) = ram_parts(e);
        TypeError::Ram(
            kctx.clone(),
            vctx.clone(),
            e.clone(),
            Spanned::new(ta, a.span.clone()),
            Spanned::new(tb, b.span.clone()),
        )
    }
    /// Reports that the index of `e` (`a[b]`), of type `tb`, depends on runtime data; `a` has
    /// type `ta`.
    pub fn ram_dynamic_index(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        ta: CTyp,
        tb: CTyp,
    ) -> Self {
        let (a, b) = ram_parts(e);
        TypeError::RamDynamicIndex(
            kctx.clone(),
            vctx.clone(),
            e.clone(),
            Spanned::new(ta, a.span.clone()),
            Spanned::new(tb, b.span.clone()),
        )
    }
    /// Reports that the protocol body ends in `e`, of type `t` rather than unit.
    pub fn unit(kctx: &Ctx<Tid, CKind>, vctx: &Ctx<Vid, CTyp>, e: &CExp, t: &CTyp) -> Self {
        TypeError::Unit(kctx.clone(), vctx.clone(), e.clone(), t.clone())
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
    pub fn app_multiple(
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        id: &Spanned<Vid>,
        params: CTyps,
        args: &CExps,
    ) -> Self {
        TypeError::AppMultiple(kctx.clone(), fctx.clone(), id.clone(), params, args.clone())
    }

    /// Reports that call `id(params)` matches no signature in `fctx`.
    pub fn func_not_found(
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        id: &Spanned<Vid>,
        params: CTyps,
        args: &CExps,
    ) -> Self {
        TypeError::FuncNotFound(kctx.clone(), fctx.clone(), id.clone(), params, args.clone())
    }

    /// Reports that the body `e` of function `id` inferred to `r` instead of its declared
    /// return type `t`.
    pub fn func_ret(
        kctx: &Ctx<Tid, CKind>,
        vctx: &Ctx<Vid, CTyp>,
        e: &CExp,
        id: &Vid,
        t: &Spanned<CTyp>,
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

// ── Conversion to diagnostics ─────────────────────────────────────────

/// Anchored at the innermost located expression, headed by the error's message, with labels
/// from [`primary_label`] and [`decorate`]. Attach a fallback location with
/// [`TypeError::located`] first when inference may have recorded none.
impl From<&TypeError> for Diagnostic {
    fn from(e: &TypeError) -> Self {
        let d = Diagnostic::error(Phase::Type, e.span().unwrap_or(0..0), &e.to_string())
            .primary_label(&primary_label(e.cause()));
        decorate(e.cause(), d)
    }
}

impl From<TypeError> for Diagnostic {
    fn from(e: TypeError) -> Self {
        Diagnostic::from(&e)
    }
}

/// The primary label for `cause`: what is wrong with the expression under the caret.
fn primary_label(cause: &TypeError) -> String {
    use TypeError as E;
    let has_type = |t: &CTyp, kctx: &Ctx<Tid, CKind>| format!("has type {}", kinded(t, kctx));
    match cause {
        E::NotPureRel(_) => "uses the transcript or randomness".to_string(),
        E::RelationNotBool(kctx, t, _) => has_type(t, kctx),
        E::Ark(kctx, _, _, t)
        | E::Condition(kctx, _, _, t)
        | E::Interp(kctx, _, _, t)
        | E::EvaluateGrid(kctx, _, _, t)
        | E::NotARecord(kctx, _, _, t)
        | E::Unit(kctx, _, _, t)
        | E::FunBody(kctx, _, _, _, t)
        | E::FuncRet(kctx, _, _, _, _, t) => match (cause, t) {
            (E::FuncRet(..), CTyp::Unit) => "produces no value".to_string(),
            _ => has_type(t, kctx),
        },
        E::CExp(..) => "cannot be typed".to_string(),
        E::VecEmpty(..) => "this vector is empty".to_string(),
        E::Map(kctx, _, _, _, _, t) => format!("ranges over {}", kinded(t, kctx)),
        E::Reduce(kctx, _, _, _, t) => format!("reduces over {}", kinded(t, kctx)),
        E::ReduceAcc(kctx, _, op, _, elem, res) => format!(
            "`{}` on {} gives {}",
            op,
            kinded(elem, kctx),
            kinded(res, kctx)
        ),
        E::MleApp(kctx, _, _, _, ts) | E::Uni(kctx, _, _, _, ts) => {
            format!("applied to {}", kinded_list(ts, kctx))
        }
        E::Challenge(_, _, t, k) => format!("{t} has kind {k}"),
        E::VarNotFound(v, _) => format!("`{v}` is not defined here"),
        E::Range(_, _, r, _) => format!("range {r}"),
        E::InterpolateUnaryNotPow2(_, _, _, n) => format!("has length {n}"),
        E::EvaluateGridNotPow2(_, _, _, n, _) => format!("has degree {n}"),
        E::Interpolate(..) => "arguments are not vectors of field elements".to_string(),
        E::InterpolateUnary(..) | E::Poly(..) => {
            "argument is not a vector of field elements".to_string()
        }
        E::Coef(..) => "argument is not a polynomial".to_string(),
        E::Mle(..) => "argument's length is not a power of two".to_string(),
        E::Evaluate(..) => "cannot be evaluated at these points".to_string(),
        E::EvaluateUnivariateVector(..) => "evaluated at a vector of points".to_string(),
        E::SelectedEvaluate(..) => "invalid selector or points".to_string(),
        E::EvaluateSelectorWithoutPoints(..) => "internal compiler error".to_string(),
        E::EvaluateMleTooManyArguments(..) => "too many evaluation points".to_string(),
        E::Pair(kctx, _, _, a, _, b) => {
            format!("pairs {} with {}", kinded(a, kctx), kinded(b, kctx))
        }
        E::ConstraintMismatch(kctx, _, _, _, a, b) => {
            format!("compares {} with {}", kinded(a, kctx), kinded(b, kctx))
        }
        E::FieldNotFound(_, _, _, f) => format!("no field `{f}`"),
        E::Unify(_) | E::Lub(_) => "types do not match here".to_string(),
        // Labelled by `decorate`, which knows the parts of the expression.
        E::Bin(..)
        | E::Vec(..)
        | E::Ram(..)
        | E::RamDynamicIndex(..)
        | E::AppMultiple(..)
        | E::FuncNotFound(..) => String::new(),
        E::Decl(..) | E::Next(..) | E::Located(..) => unreachable!("skipped by `cause`"),
    }
}

/// Labels the parts of the failing expression with their types, and adds the notes and
/// suggestions specific to `cause`.
fn decorate(cause: &TypeError, mut d: Diagnostic) -> Diagnostic {
    // "`x` has type F (Field)", under `x`.
    let has_type = |d: Diagnostic, span: &std::ops::Range<usize>, e: &CExp, t: String| {
        if span.is_empty() {
            d
        } else {
            d.secondary_label(span.clone(), &format!("`{e:.MESSAGE_DEPTH$}` has type {t}"))
        }
    };
    match cause {
        TypeError::Bin(kctx, _, CExp::Bin(_, x, y), op, a, b, _) => {
            // Point at the operator: the source between the two operands.
            if !a.span.is_empty() && !b.span.is_empty() && a.span.end <= b.span.start {
                d.span = a.span.end..b.span.start;
            }
            d.primary_label = format!("`{}` is not defined for these operands", op);
            d = has_type(d, &a.span, &x.node, kinded(a, kctx));
            has_type(d, &b.span, &y.node, kinded(b, kctx))
        }
        TypeError::Vec(kctx, _, elem, first, _, elem_exp, first_exp) => {
            d.primary_label = "in this vector".to_string();
            d = has_type(d, &first.span, first_exp, kinded(first, kctx));
            has_type(d, &elem.span, elem_exp, kinded(elem, kctx))
        }
        TypeError::Ram(kctx, _, e, ta, tb) | TypeError::RamDynamicIndex(kctx, _, e, ta, tb) => {
            let (a, i) = ram_parts(e);
            // The caret goes on the index; the vector gets its own label.
            if !tb.span.is_empty() {
                d.span = tb.span.clone();
            }
            if matches!(cause, TypeError::RamDynamicIndex(..)) {
                d.primary_label =
                    format!("`{:.MESSAGE_DEPTH$}` has type {}", i.node, kinded(tb, kctx));
                return d;
            }
            let which = if matches!(tb.node, CTyp::Vec(..)) {
                "indices"
            } else {
                "index"
            };
            d.primary_label = format!("{which} `{:.MESSAGE_DEPTH$}`", i.node);
            if a.span.is_empty() {
                return d;
            }
            let vector = match &ta.node {
                CTyp::Vec(_, n) => format!("`{:.MESSAGE_DEPTH$}` has length {n}", a.node),
                _ => format!("`{:.MESSAGE_DEPTH$}` has type {}", a.node, kinded(ta, kctx)),
            };
            d.secondary_label(a.span.clone(), &vector)
        }
        TypeError::FuncRet(kctx, _, _, id, declared, _) => {
            let must_return = format!("`{id}` must return {}", kinded(declared, kctx));
            if declared.span.is_empty() {
                d
            } else if declared.span == d.span {
                // An empty body has no span of its own; the error sits on the annotation.
                d.primary_label = must_return;
                d
            } else {
                d.secondary_label(declared.span.clone(), &must_return)
            }
        }
        TypeError::FuncNotFound(kctx, fctx, id, ts, args)
        | TypeError::AppMultiple(kctx, fctx, id, ts, args) => {
            let defined = candidates(fctx, id);
            if !defined.is_empty() {
                d.primary_label = if matches!(cause, TypeError::FuncNotFound(..)) {
                    "no definition takes these argument types"
                } else {
                    "several definitions take these argument types"
                }
                .to_string();
                for (arg, t) in args.0.iter().zip(ts.iter()) {
                    d = has_type(d, &arg.span, &arg.node, kinded(t, kctx));
                }
            }
            if defined.is_empty() {
                // No declaration has this name: point at the name, like an undefined variable.
                if !id.span.is_empty() {
                    d.span = id.span.clone();
                }
                d.primary_label = format!("`{id}` is not defined in this scope");
                let mut similar: Vec<&str> = fctx
                    .iter()
                    .map(|sig| sig.name.node.0.as_str())
                    .filter(|n| (1..=2).contains(&levenshtein(&id.node.0, n)))
                    .collect();
                similar.sort_unstable();
                similar.dedup();
                if let Some(first) = similar.first() {
                    let names: Vec<String> = similar.iter().map(|n| format!("`{n}`")).collect();
                    d = d.suggestion(
                        &format!("did you mean {}?", names.join(", ")),
                        id.span.clone(),
                        first,
                        Applicability::MaybeIncorrect,
                    );
                }
            }
            const MAX_SHOWN: usize = 4;
            for args in defined.iter().take(MAX_SHOWN) {
                d = d.note(&format!("`{id}` takes {args}"));
            }
            if defined.len() > MAX_SHOWN {
                d = d.note(&format!(
                    "... and {} more definitions of `{id}`",
                    defined.len() - MAX_SHOWN
                ));
            }
            d
        }
        _ => d,
    }
}

/// The distinct argument lists of the declarations named `id`, each type with its kind in that
/// declaration.
fn candidates(fctx: &Set<CSig>, id: &Spanned<Vid>) -> Vec<String> {
    let mut args: Vec<String> = fctx
        .iter()
        .filter(|sig| sig.name.node == id.node)
        .map(|sig| {
            let kctx = sig.typevars.node.to_ctx();
            sig.args
                .iter()
                .map(|a| kinded(&a.typ.node, &kctx))
                .collect::<Vec<_>>()
                .join(", ")
        })
        .collect();
    args.sort();
    args.dedup();
    args
}

// ── Message helpers (used by the `#[error]` messages and the labels above) ──

/// `t` with the kinds of its type variables: `F (Scalar<G>)` for a type variable,
/// `[F; 2] (F: Scalar<G>)` for a type built from them, and `an integer` for `Fin`.
fn kinded(t: &CTyp, kctx: &Ctx<Tid, CKind>) -> String {
    match t {
        CTyp::Fin(_) => "an integer".to_string(),
        CTyp::Base(tid) => kctx
            .get(tid)
            .map_or_else(|| t.to_string(), |k| format!("{t} ({k})")),
        _ => {
            let mut vars = Vec::new();
            type_vars(t, &mut vars);
            let kinds: Vec<String> = vars
                .iter()
                .filter_map(|v| kctx.get(v).map(|k| format!("{v}: {k}")))
                .collect();
            if kinds.is_empty() {
                t.to_string()
            } else {
                format!("{t} ({})", kinds.join(", "))
            }
        }
    }
}

/// Pushes the type variables of `t` onto `out`, in order of appearance, without repeats.
fn type_vars(t: &CTyp, out: &mut Vec<Tid>) {
    let mut push = |v: &Tid| {
        if !out.contains(v) {
            out.push(v.clone());
        }
    };
    match t {
        CTyp::Base(v) | CTyp::Poly(v, _, _) => push(v),
        CTyp::Vec(t, _) => type_vars(t, out),
        CTyp::Record(fields) => {
            for (_, t) in fields.iter() {
                type_vars(t, out);
            }
        }
        CTyp::Fin(_) | CTyp::Unit | CTyp::Bool => {}
    }
}

/// [`kinded`] for each of `ts`, comma-separated.
fn kinded_list(ts: &CTyps, kctx: &Ctx<Tid, CKind>) -> String {
    ts.iter()
        .map(|t| kinded(t, kctx))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The statement keyword of a `verify`/`assert` condition error.
fn condition_keyword(e: &CExp) -> &'static str {
    if matches!(e, CExp::Assert(_)) {
        "assert"
    } else {
        "verify"
    }
}

/// Message for a `fun` over `vars` variables whose body has type `t`.
fn fun_body_message(vars: usize, t: &str) -> String {
    if vars == 1 {
        format!(
            "A `fun` of one variable must evaluate to a field element or a polynomial in it, but its body has type {t}"
        )
    } else {
        format!(
            "A `fun` of several variables must evaluate to a field element, but its body has type {t}"
        )
    }
}

/// Message for the indexing expression `e` into a vector of type `ta` with an index of type
/// `tb`.
fn index_message(e: &CExp, ta: &CTyp, tb: &CTyp, kctx: &Ctx<Tid, CKind>) -> String {
    let i = ram_index_text(e);
    match (ta, tb) {
        (CTyp::Vec(_, n), CTyp::Fin(_) | CTyp::Vec(..)) => {
            format!("Index `{i}` is out of bounds for a vector of length {n}")
        }
        (_, CTyp::Fin(_)) => format!("Index `{i}` is out of bounds for {}", kinded(ta, kctx)),
        _ => format!(
            "Index `{i}` must be a compile-time integer, but has type {}",
            kinded(tb, kctx)
        ),
    }
}

/// The vector and index of the indexing expression `e` (`a[i]`).
fn ram_parts(e: &CExp) -> (&Spanned<CExp>, &Spanned<CExp>) {
    let CExp::Ram(a, i) = e else {
        unreachable!("index errors are only raised for indexing expressions")
    };
    (a, i)
}

/// The index of the indexing expression `e`, as shown in messages.
fn ram_index_text(e: &CExp) -> String {
    format!("{:.MESSAGE_DEPTH$}", ram_parts(e).1.node)
}

/// Message for a call to `id` with arguments of types `ts` that no declaration accepts.
fn func_not_found_message(
    fctx: &Set<CSig>,
    id: &Spanned<Vid>,
    ts: &CTyps,
    kctx: &Ctx<Tid, CKind>,
) -> String {
    if candidates(fctx, id).is_empty() {
        format!("No function named `{id}`")
    } else {
        format!(
            "No definition of `{id}` accepts arguments of type {}",
            kinded_list(ts, kctx)
        )
    }
}

/// How a function body of type `r` fails to be a value of the declared return type.
fn body_result(r: &CTyp, kctx: &Ctx<Tid, CKind>) -> String {
    match r {
        CTyp::Unit => "its body does not produce a value".to_string(),
        _ => format!("its body has type {}", kinded(r, kctx)),
    }
}

/// How many levels of an expression a message shows; deeper parts print as `…` (see the
/// precision on [`CExp`]'s `Display`).
const MESSAGE_DEPTH: usize = 3;
