use crate::ast::BinOp;
use crate::ast::range::{Range, RangeError};
use crate::ast::sig::{CSig, SigError};
use crate::ast::spanned::Spanned;
use crate::diagnostic::{Applicability, Diagnostic, Phase};
use crate::id::{Tid, Vid};
use crate::semantic::levenshtein;
use crate::typ::lub::{LubError, describe_bin};
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, CTyps};
use share::{Ctx, Set};
use thiserror::Error;

/// What draws a sample: `random<T>` or `challenge<T>`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sampler {
    /// `random<T>`, a prover's private randomness.
    Random,
    /// `challenge<T>`, a Fiat-Shamir challenge.
    Challenge,
}

impl std::fmt::Display for Sampler {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Sampler::Random => "random",
            Sampler::Challenge => "challenge",
        })
    }
}

/// User-facing failure of source-level type inference over a concretized module.
///
/// One variant exists per surface construct that carries a bespoke typing rule. `Display` is
/// the one-line message shown to users: the wrappers (`Decl`, `Located`) display their cause,
/// and no message repeats the offending expression, which a diagnostic's span shows. A variant
/// holds what its message and labels print: types, with the kind context (`Ctx<Tid, CKind>`)
/// their kinds come from, names, and the spans of the parts it labels. This is the
/// `lang`-level, user-directed error channel; shape violations discovered later in the IR are
/// invariants and panic instead.
#[derive(Error, PartialEq, Debug)]
pub enum TypeError {
    /// Wraps an inner error with the declaration whose body failed to type-check.
    #[error("{1}")]
    Decl(Vid, Box<TypeError>),

    /// Attaches the source span of the expression whose inference failed. Only the innermost
    /// spanned expression on the failing path is recorded; `Display` is unchanged.
    #[error("{1}")]
    Located(std::ops::Range<usize>, Box<TypeError>),

    /// A specification relation referenced transcript or randomness, so it is not a pure
    /// predicate over the statement and witness.
    #[error("A `where` clause cannot use the transcript or randomness")]
    NotPureRel,

    /// A `where` clause inferred to something other than `Bool`.
    #[error("A `where` clause must be a boolean condition, but this has type {}", kinded(.1, .0))]
    RelationNotBool(Ctx<Tid, CKind>, CTyp),

    /// A source type has no `ATyp` image, i.e. it cannot be lowered to an `arkworks` runtime
    /// type under the current kind context.
    #[error("Type {} is not supported by the arkworks backend", kinded(.1, .0))]
    Ark(Ctx<Tid, CKind>, CTyp),

    /// Generic inference failure for an expression with no more specific variant.
    #[error("Ill-typed expression")]
    IllTyped,

    /// A binary operator was applied to operand types it is not defined on; the operand types
    /// are spanned at the operands.
    #[error("{}", describe_bin(*.1, &kinded(.2, .0), &kinded(.3, .0)))]
    Bin(Ctx<Tid, CKind>, BinOp, Spanned<CTyp>, Spanned<CTyp>),

    /// The condition of a `verify` is not a boolean.
    #[error("`verify` expects a boolean condition, but this has type {}", kinded(.1, .0))]
    Condition(Ctx<Tid, CKind>, CTyp),

    /// The body of a `fun` has a type its variables cannot make into a polynomial; carries the
    /// number of variables and the body's type.
    #[error("{}", fun_body_message(*.1, &kinded(.2, .0)))]
    FunBody(Ctx<Tid, CKind>, usize, CTyp),

    /// An empty vector literal has no element type to infer from.
    #[error("Cannot infer the element type of an empty vector")]
    VecEmpty,

    /// Two elements of a vector literal have no common type: an element, and the first one.
    #[error("Vector elements must all have the same type, but found {} and {}", kinded(.2, .0), kinded(.1, .0))]
    Vec(Ctx<Tid, CKind>, Spanned<CTyp>, Spanned<CTyp>),

    /// The argument list of `interpolate` was not a pair of field vectors.
    #[error("`interpolate` expects vectors of field elements")]
    Interpolate,

    /// The single argument of the one-argument `interpolate` form was not a field vector.
    #[error("`interpolate` expects a vector of field elements")]
    InterpolateUnary,

    /// Unary `interpolate` lowers to an inverse FFT, so its input vector length must be a power
    /// of two; carries the offending length.
    #[error("`interpolate` needs a vector whose length is a power of two, but this has length {0}")]
    InterpolateUnaryNotPow2(usize),

    /// `poly` was applied to something other than a vector of field elements.
    #[error("`poly` expects a vector of field elements")]
    Poly,

    /// Polynomial evaluation received operands that are not a polynomial applied to a scalar
    /// point or a vector of scalar points.
    #[error("A polynomial can only be evaluated at a scalar or a vector of scalars")]
    Evaluate,

    /// A univariate polynomial was applied to a vector of points; univariate evaluation takes a
    /// single scalar, and batching must be written as an explicit comprehension.
    #[error(
        "A univariate polynomial cannot be evaluated at a vector of points; evaluate at one point with `p(x)`, or write `[p(x) for x in points]`"
    )]
    EvaluateUnivariateVector,

    /// Partial evaluation `eval<range>` was given a bad selector: the free range must be a
    /// nonempty contiguous window inside the polynomial's variables, and the remaining
    /// variables must each receive exactly one fixed scalar.
    #[error(
        "`eval<{0}>` needs a polynomial, a non-empty contiguous range of its variables, and one fixed scalar for each remaining variable"
    )]
    SelectedEvaluate(Range<usize>),

    /// Internal invariant breach: a selected-evaluation node survived parser conversion without
    /// the explicit point and fixed-value arguments that lowering requires.
    #[error("Internal compiler error: `eval<{0}>` lost its point arguments during parsing")]
    EvaluateSelectorWithoutPoints(Range<usize>),

    /// A multilinear extension was applied to more points than it has variables.
    #[error("Too many evaluation points for this multilinear extension")]
    EvaluateMleTooManyArguments,

    /// `coef` was applied to a non-polynomial; only polynomials expose a coefficient vector.
    #[error("`coef` expects a polynomial")]
    Coef,

    /// `mle` requires a vector whose length is a power of two, since the multilinear encoding
    /// stores `2^n` evaluation slots.
    #[error("`mle` expects a vector whose length is a power of two")]
    Mle,

    /// The source of a `for` comprehension did not infer to a non-empty vector type; carries
    /// the type actually inferred.
    #[error("A `for` comprehension must range over a non-empty vector, but this has type {}", kinded(.1, .0))]
    Map(Ctx<Tid, CKind>, CTyp),

    /// `reduce` was applied to an expression that is not a vector.
    #[error("`reduce` expects a vector, but got {}", kinded(.1, .0))]
    Reduce(Ctx<Tid, CKind>, CTyp),

    /// The reduction operator is not closed over the element type: `lub_op` of the element type
    /// with itself produced a different type, so the accumulator has no fixed point.
    #[error("`reduce` with `{op}` needs `{op}` to keep the element type {elem}, but it gives {res}", op = .1, elem = kinded(.2, .0), res = kinded(.3, .0))]
    ReduceAcc(Ctx<Tid, CKind>, BinOp, CTyp, CTyp),

    /// A variable that is not a polynomial was applied. A variable hides every function of its
    /// name, so the application calls none.
    #[error("`{}` is a variable of type {}, which cannot be applied", .1.node, kinded(.2, .0))]
    NotApplicable(Ctx<Tid, CKind>, Spanned<Vid>, CTyp),

    /// A polynomial was applied to other than one point.
    #[error("Polynomial `{1}` takes one point, but got {}", kinded_list(.2, .0))]
    PolyApp(Ctx<Tid, CKind>, Vid, CTyps),

    /// A `random` or `challenge` was asked to produce a non-field value; both draw from a
    /// scalar field only.
    #[error("`{0}` draws field elements, but {1} has kind {2}")]
    Sample(Sampler, Tid, CKind),

    /// A sample of `t` excludes values that are not a vector of `t`.
    #[error("A sample of {1} can exclude only a vector of {1}, but got {}", kinded(.2, .0))]
    ExclusionType(Ctx<Tid, CKind>, Tid, CTyp),

    /// A sample excludes `roots_of_unity(0)`, every value of its type.
    #[error("`roots_of_unity(0)` excludes every {0}, so nothing is left to sample")]
    ExcludesAll(Tid),

    /// A variable occurrence has no binding in the variable context.
    #[error("Variable `{0}` is not defined")]
    VarNotFound(Vid),

    /// A range expression is ill-formed; the wrapped `RangeError` states why.
    #[error("Invalid range {0}: {1}")]
    Range(Range<usize>, RangeError),

    /// Unary `eval` (evaluation over the full FFT/boolean grid) was applied to a value that is
    /// neither a univariate polynomial nor a multilinear extension.
    #[error("`eval` expects a univariate polynomial or a multilinear extension, but got {}", kinded(.1, .0))]
    EvaluateGrid(Ctx<Tid, CKind>, CTyp),

    /// Unary `eval` lowers to a forward FFT, so a univariate operand must have a power-of-two
    /// coefficient count `m + 1`; carries the offending `max_degree`.
    #[error(
        "`eval` needs a polynomial with a power-of-two number of coefficients, but this has degree {0}"
    )]
    EvaluateGridNotPow2(usize),

    /// A vector index is not a `Fin` type bounded by the vector's length, so the access cannot
    /// be proven in range; carries the vector's and the index's types, at their spans.
    #[error("{}", index_message(.1, .2, .0))]
    Ram(Ctx<Tid, CKind>, Spanned<CTyp>, Spanned<CTyp>),

    /// A vector index depends on runtime data; indices must be compile-time literals or ranges
    /// because the DAG is statically shaped.
    #[error("The index must be a compile-time constant, but has type {}", kinded(.2, .0))]
    RamDynamicIndex(Ctx<Tid, CKind>, Spanned<CTyp>, Spanned<CTyp>),

    /// A vector index is an integer outside the finite-index range; it is never reduced
    /// modulo a field prime to make it fit.
    #[error("An integer outside the finite-index range cannot index a vector")]
    FiniteIndexOverflow,

    /// Several signatures fit the call's argument types (spanned at the arguments) and none is
    /// at least as specific as all the others; carries the ones no other is more specific than.
    #[error("Call to `{2}` is ambiguous: several definitions accept arguments of type {}", kinded_list(.3, .0))]
    AppMultiple(Ctx<Tid, CKind>, Vec<CSig>, Spanned<Vid>, CTyps),

    /// Overload resolution found no signature matching the call's argument types (spanned at
    /// the arguments). The last field holds the declarations that fit the arguments but whose
    /// type parameters could not all be solved, with the reason.
    #[error("{}", func_not_found_message(.1, .2, .3, .0))]
    FuncNotFound(
        Ctx<Tid, CKind>,
        Set<CSig>,
        Spanned<Vid>,
        CTyps,
        Vec<(CSig, SigError)>,
    ),

    /// The only declaration that fits a call's arguments leaves a type parameter unsolved or
    /// violates a kind.
    #[error("{}", call_message(.0, .1))]
    Call(Spanned<Vid>, Box<SigError>),

    /// A protocol body ended in an expression that is not unit-typed; carries its type.
    #[error("A protocol body must end in a statement such as `verify(...)`, but this has type {}", kinded(.1, .0))]
    Unit(Ctx<Tid, CKind>, CTyp),

    /// A function body's inferred type disagrees with its declared return type: the function,
    /// the declared type and the inferred one.
    #[error("Function `{1}` must return {}, but {}", kinded(.2, .0), body_result(.3, .0))]
    FuncRet(Ctx<Tid, CKind>, Vid, Spanned<CTyp>, CTyp),

    /// `pair` was applied to operands that are not a `G1`/`G2` pair of a pairing-friendly curve
    /// declared in the kind context.
    #[error("`pair` expects the two groups of a pairing-friendly curve, but got {} and {}", kinded(.1, .0), kinded(.2, .0))]
    Pair(Ctx<Tid, CKind>, CTyp, CTyp),

    /// A record projection named a field the record type does not declare.
    #[error("Record has no field `{0}`")]
    FieldNotFound(String),

    /// A record update's new value does not fit the field's type; carries the field, the
    /// field's type and the value's type.
    #[error("Field `{1}` has type {}, but the new value has type {}", kinded(.2, .0), kinded(.3, .0))]
    FieldUpdate(Ctx<Tid, CKind>, String, CTyp, CTyp),

    /// A field projection was applied to an expression whose type is not a record.
    #[error("Expected a record, but got {}", kinded(.1, .0))]
    NotARecord(Ctx<Tid, CKind>, CTyp),

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
            TypeError::Decl(_, e) => e.span(),
            _ => None,
        }
    }
    /// The error itself, without the location and declaration wrappers.
    pub fn cause(&self) -> &TypeError {
        match self {
            TypeError::Located(_, e) | TypeError::Decl(_, e) => e.cause(),
            _ => self,
        }
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
        E::NotPureRel => "uses the transcript or randomness".to_string(),
        E::RelationNotBool(kctx, t)
        | E::Ark(kctx, t)
        | E::Condition(kctx, t)
        | E::EvaluateGrid(kctx, t)
        | E::NotARecord(kctx, t)
        | E::Unit(kctx, t)
        | E::FunBody(kctx, _, t)
        | E::NotApplicable(kctx, _, t)
        | E::FuncRet(kctx, _, _, t) => match (cause, t) {
            (E::FuncRet(..), CTyp::Unit) => "produces no value".to_string(),
            _ => has_type(t, kctx),
        },
        E::IllTyped => "cannot be typed".to_string(),
        E::VecEmpty => "this vector is empty".to_string(),
        E::Map(kctx, t) => format!("ranges over {}", kinded(t, kctx)),
        E::Reduce(kctx, t) => format!("reduces over {}", kinded(t, kctx)),
        E::ReduceAcc(kctx, op, elem, res) => format!(
            "`{}` on {} gives {}",
            op,
            kinded(elem, kctx),
            kinded(res, kctx)
        ),
        E::PolyApp(kctx, _, ts) => {
            format!("applied to {}", kinded_list(ts, kctx))
        }
        E::Sample(_, t, k) => format!("{t} has kind {k}"),
        E::ExclusionType(kctx, _, t) => has_type(t, kctx),
        E::ExcludesAll(_) => "excludes every value".to_string(),
        E::VarNotFound(v) => format!("`{v}` is not defined here"),
        E::Range(r, _) => format!("range {r}"),
        E::InterpolateUnaryNotPow2(n) => format!("has length {n}"),
        E::EvaluateGridNotPow2(n) => format!("has degree {n}"),
        E::Interpolate => "arguments are not vectors of field elements".to_string(),
        E::InterpolateUnary | E::Poly => "argument is not a vector of field elements".to_string(),
        E::Coef => "argument is not a polynomial".to_string(),
        E::Mle => "argument's length is not a power of two".to_string(),
        E::Evaluate => "cannot be evaluated at these points".to_string(),
        E::EvaluateUnivariateVector => "evaluated at a vector of points".to_string(),
        E::SelectedEvaluate(_) => "invalid selector or points".to_string(),
        E::EvaluateSelectorWithoutPoints(_) => "internal compiler error".to_string(),
        E::EvaluateMleTooManyArguments => "too many evaluation points".to_string(),
        E::Pair(kctx, a, b) => format!("pairs {} with {}", kinded(a, kctx), kinded(b, kctx)),
        E::FieldNotFound(f) => format!("no field `{f}`"),
        E::FieldUpdate(kctx, _, _, t) => has_type(t, kctx),
        E::Call(_, e) => match e.as_ref() {
            SigError::Uninferable {
                param,
                kind,
                reason,
            } => {
                format!("`{param}` ({kind}) {reason}")
            }
            _ => e.to_string(),
        },
        E::Unify(_) | E::Lub(_) => "types do not match here".to_string(),
        E::FiniteIndexOverflow => "exceeds the finite-index range".to_string(),
        // Labelled by `decorate`, which knows the parts of the expression.
        E::Bin(..)
        | E::Vec(..)
        | E::Ram(..)
        | E::RamDynamicIndex(..)
        | E::AppMultiple(..)
        | E::FuncNotFound(..) => String::new(),
        E::Decl(..) | E::Located(..) => unreachable!("skipped by `cause`"),
    }
}

/// Labels the parts of the failing expression with their types, and adds the notes and
/// suggestions specific to `cause`.
fn decorate(cause: &TypeError, mut d: Diagnostic) -> Diagnostic {
    // "has type F (Field)", under the expression that has it.
    let has_type = |d: Diagnostic, span: &std::ops::Range<usize>, t: String| {
        if span.is_empty() {
            d
        } else {
            d.secondary_label(span.clone(), &format!("has type {t}"))
        }
    };
    match cause {
        TypeError::Bin(kctx, op, a, b) => {
            // Point at the operator: the source between the two operands.
            if !a.span.is_empty() && !b.span.is_empty() && a.span.end <= b.span.start {
                d.span = a.span.end..b.span.start;
            }
            d.primary_label = format!("`{}` is not defined for these operands", op);
            d = has_type(d, &a.span, kinded(a, kctx));
            has_type(d, &b.span, kinded(b, kctx))
        }
        TypeError::Vec(kctx, elem, first) => {
            d.primary_label = "in this vector".to_string();
            d = has_type(d, &first.span, kinded(first, kctx));
            has_type(d, &elem.span, kinded(elem, kctx))
        }
        TypeError::Ram(kctx, ta, tb) | TypeError::RamDynamicIndex(kctx, ta, tb) => {
            // The caret goes on the index; the vector gets its own label.
            if !tb.span.is_empty() {
                d.span = tb.span.clone();
            }
            if matches!(cause, TypeError::RamDynamicIndex(..)) {
                d.primary_label = format!("has type {}", kinded(tb, kctx));
                return d;
            }
            d.primary_label = if matches!(tb.node, CTyp::Vec(..)) {
                "these indices"
            } else {
                "this index"
            }
            .to_string();
            if ta.span.is_empty() {
                return d;
            }
            let vector = match &ta.node {
                CTyp::Vec(_, n) => format!("has length {n}"),
                _ => format!("has type {}", kinded(ta, kctx)),
            };
            d.secondary_label(ta.span.clone(), &vector)
        }
        TypeError::FuncRet(kctx, id, declared, _) => {
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
        TypeError::FuncNotFound(..) | TypeError::AppMultiple(..) => {
            // The declarations to list: every one of the name, or only the tied ones.
            let (kctx, fctx, id, ts, defined) = match cause {
                TypeError::FuncNotFound(kctx, fctx, id, ts, _) => {
                    let named = fctx.iter().filter(|sig| sig.name.node == id.node);
                    (kctx, Some(fctx), id, ts, candidates(named))
                }
                TypeError::AppMultiple(kctx, tied, id, ts) => {
                    (kctx, None, id, ts, candidates(tied.iter()))
                }
                _ => unreachable!("matched above"),
            };
            if !defined.is_empty() {
                d.primary_label = if matches!(cause, TypeError::FuncNotFound(..)) {
                    "no definition takes these argument types"
                } else {
                    "several definitions take these argument types"
                }
                .to_string();
                for t in ts.iter() {
                    d = has_type(d, &t.span, kinded(t, kctx));
                }
            } else {
                // No declaration has this name: point at the name, like an undefined variable.
                if !id.span.is_empty() {
                    d.span = id.span.clone();
                }
                d.primary_label = format!("`{id}` is not defined in this scope");
                let mut similar: Vec<&str> = fctx
                    .into_iter()
                    .flat_map(|fctx| fctx.iter())
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
            if let TypeError::FuncNotFound(.., unresolved) = cause {
                for (sig, e) in unresolved {
                    d = d.note(&format!("`{sig}` does not fit: {e}"));
                }
            }
            d
        }
        TypeError::NotApplicable(_, var, _) => {
            // The caret goes on the applied name, which has the type.
            if !var.span.is_empty() {
                d.span = var.span.clone();
            }
            d.note(
                "only functions and polynomials can be applied; a variable hides every function \
                 of its name",
            )
        }
        _ => d,
    }
}

/// The distinct argument lists of `sigs`, each type with its kind in that declaration.
fn candidates<'a>(sigs: impl Iterator<Item = &'a CSig>) -> Vec<String> {
    let mut args: Vec<String> = sigs
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
        CTyp::FieldLiteral => "a field-only integer".to_string(),
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
        CTyp::Fin(_) | CTyp::Unit | CTyp::Bool | CTyp::FieldLiteral => {}
    }
}

/// [`kinded`] for each of `ts`, comma-separated.
fn kinded_list(ts: &CTyps, kctx: &Ctx<Tid, CKind>) -> String {
    ts.iter()
        .map(|t| kinded(t, kctx))
        .collect::<Vec<_>>()
        .join(", ")
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

/// Message for indexing a vector of type `ta` with an index of type `tb`.
fn index_message(ta: &CTyp, tb: &CTyp, kctx: &Ctx<Tid, CKind>) -> String {
    match (ta, tb) {
        (CTyp::Vec(_, n), CTyp::Fin(_) | CTyp::Vec(..)) => {
            format!("The index is out of bounds for a vector of length {n}")
        }
        (_, CTyp::Fin(_)) => format!("The index is out of bounds for {}", kinded(ta, kctx)),
        _ => format!(
            "The index must be a compile-time integer, but has type {}",
            kinded(tb, kctx)
        ),
    }
}

/// Message for a call to `id` with arguments of types `ts` that no declaration accepts.
fn func_not_found_message(
    fctx: &Set<CSig>,
    id: &Spanned<Vid>,
    ts: &CTyps,
    kctx: &Ctx<Tid, CKind>,
) -> String {
    if !fctx.iter().any(|sig| sig.name.node == id.node) {
        format!("No function named `{id}`")
    } else {
        format!(
            "No definition of `{id}` accepts arguments of type {}",
            kinded_list(ts, kctx)
        )
    }
}

/// Message for a call to `id` that fits one declaration's arguments but fails with `e`.
fn call_message(id: &Spanned<Vid>, e: &SigError) -> String {
    match e {
        SigError::Uninferable { param, .. } => {
            format!("Cannot infer type parameter `{param}` of `{id}`")
        }
        _ => format!("Cannot call `{id}`: {e}"),
    }
}

/// How a function body of type `r` fails to be a value of the declared return type.
fn body_result(r: &CTyp, kctx: &Ctx<Tid, CKind>) -> String {
    match r {
        CTyp::Unit => "its body does not produce a value".to_string(),
        _ => format!("its body has type {}", kinded(r, kctx)),
    }
}
