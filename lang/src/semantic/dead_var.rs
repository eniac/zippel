//! Dead variable and dead computation detection.
//!
//! Warns about:
//! - Unused function arguments
//! - Unused `let` bindings
//! - Dead computations (`let _ = pure_expr; body`)
//! - Unused comprehension/lambda variables
//!
//! Variables prefixed with `_` are treated as intentionally unused (Rust convention).
//!
//! ## Implementation
//!
//! Uses a single iterative AST walk with an explicit work stack (no recursion,
//! so no stack overflow on deeply nested expressions). A scope stack tracks
//! bindings; when a `Var` reference is encountered, the innermost matching
//! binding is marked used. This correctly handles shadowing — a reference to
//! `x` resolves to the innermost `let x = ...`, not an outer one.

use std::ops::Range;

use crate::ast::decl::{Body, UDecl};
use crate::ast::spanned::Spanned;
use crate::ast::{Exp, UExp};
use crate::diagnostic::Diagnostic;
use crate::id::Vid;
use lang_derive::Diagnostic as DiagnosticDerive;

/// W0001: A variable is bound but never used.
#[derive(DiagnosticDerive)]
#[diag("unused variable `{$name}`", code = "W0001", warning, Semantic)]
struct UnusedVariable {
    name: Vid,
    #[span(label = "`{$name}` is bound but never used")]
    #[suggestion(
        "if this is intentional, prefix it with an underscore",
        replacement = "_{$name}",
        applicability = "maybe-incorrect"
    )]
    span: Range<usize>,
}

/// W0001: A pure computation is discarded.
#[derive(DiagnosticDerive)]
#[diag("unused computation", code = "W0001", warning, Semantic)]
struct DeadComputation {
    #[span(label = "this expression is computed but its result is discarded")]
    span: Range<usize>,
    #[note("the expression has no side effects; remove it or bind the result")]
    _note: (),
}

// ── Scope tracking ──────────────────────────────────────────────────────

/// A single binding: name, span, and whether it's been referenced.
struct Binding {
    name: Vid,
    span: Range<usize>,
    used: bool,
}

/// Check if a variable name starts with `_` (intentionally unused).
fn is_intentionally_unused(name: &Vid) -> bool {
    name.0.starts_with('_')
}

/// Scope stack: tracks bindings across nested scopes.
///
/// When we encounter `Var(x)`, we search from the innermost scope outward
/// and mark the first matching binding as used. This correctly handles
/// shadowing — an inner `let x = ...` shadows an outer `let x = ...`,
/// so a reference to `x` marks the inner binding, not the outer one.
struct Scopes(Vec<Vec<Binding>>);

impl Scopes {
    fn new() -> Self {
        Self(Vec::new())
    }

    /// Push a new scope with the given bindings (all initially unused).
    fn push_scope(&mut self, bindings: Vec<(Vid, Range<usize>)>) {
        self.0.push(
            bindings
                .into_iter()
                .map(|(name, span)| Binding {
                    name,
                    span,
                    used: false,
                })
                .collect(),
        );
    }

    /// Pop the innermost scope, emitting warnings for any unused bindings.
    fn pop_scope(&mut self, out: &mut Vec<Diagnostic>) {
        let scope = self.0.pop().expect("scope stack underflow");
        for b in scope {
            if !b.used && !is_intentionally_unused(&b.name) {
                out.push(
                    UnusedVariable {
                        name: b.name,
                        span: b.span,
                    }
                    .build(),
                );
            }
        }
    }

    /// Mark the innermost binding of `name` as used.
    /// If no binding matches, the variable is free (not our concern).
    fn mark_used(&mut self, name: &Vid) {
        for scope in self.0.iter_mut().rev() {
            for b in scope.iter_mut() {
                if &b.name == name {
                    b.used = true;
                    return;
                }
            }
        }
    }
}

// ── Iterative walk ──────────────────────────────────────────────────────

/// Work item for the iterative AST walk.
enum Work<'a> {
    /// Visit this expression.
    Expr(&'a Spanned<UExp>),
    /// Push a new scope with the given bindings.
    PushScope(Vec<(Vid, Range<usize>)>),
    /// Pop the current scope and check for unused bindings.
    PopScope,
}

/// Walk an expression iteratively, tracking variable usage through scopes.
///
/// `scopes` should already have the argument scope pushed (if any).
fn walk(expr: &Spanned<UExp>, scopes: &mut Scopes, out: &mut Vec<Diagnostic>) {
    let mut stack: Vec<Work> = vec![Work::Expr(expr)];

    while let Some(item) = stack.pop() {
        match item {
            Work::PushScope(bindings) => scopes.push_scope(bindings),
            Work::PopScope => scopes.pop_scope(out),
            Work::Expr(e) => visit(e, &mut stack, scopes, out),
        }
    }
}

/// Process a single expression, pushing child work items onto the stack.
fn visit<'a>(
    e: &'a Spanned<UExp>,
    stack: &mut Vec<Work<'a>>,
    scopes: &mut Scopes,
    out: &mut Vec<Diagnostic>,
) {
    match &e.node {
        // ── Variable reference: mark used ───────────────────────────────
        Exp::Var(id) => scopes.mark_used(&id.node),

        // ── Let: binding scope ──────────────────────────────────────────
        // `let x = val; body` — x is in scope for body, not val.
        // `let _ = val; body` — no binding, val is discarded (dead computation?).
        Exp::Let(var, val, cont) => match var {
            Some(x) => {
                // Execution order: val → push scope → body → pop scope.
                if let Some(body) = cont {
                    stack.push(Work::PopScope);
                    stack.push(Work::Expr(body));
                    stack.push(Work::PushScope(vec![(x.node.clone(), x.span.clone())]));
                }
                stack.push(Work::Expr(val));
            }
            None => {
                // Sequencing: `val; body` — val is discarded in favor of body.
                // `val` alone (no continuation) is the return value, not dead.
                if let Some(body) = cont {
                    if is_pure_no_app(val) {
                        out.push(
                            DeadComputation {
                                span: val.span.clone(),
                                _note: (),
                            }
                            .build(),
                        );
                    }
                    stack.push(Work::Expr(body));
                }
                stack.push(Work::Expr(val));
            }
        },

        // ── Log: binding scope (same as Let) ────────────────────────────
        // `x <- val; body` — x is in scope for body, not val.
        // Log always has a side effect (transcript), so the binding is never
        // a dead computation. But x might be unused in body.
        Exp::Log(x, val, cont) => {
            // Execution order: val → push scope → body → pop scope.
            if let Some(body) = cont {
                stack.push(Work::PopScope);
                stack.push(Work::Expr(body));
                stack.push(Work::PushScope(vec![(x.node.clone(), x.span.clone())]));
            }
            stack.push(Work::Expr(val));
        }

        // ── Map: comprehension variable scope ───────────────────────────
        // `[body for x in iter]` — x is in scope for body, not iter.
        Exp::Map(body, var, iter) => {
            // Execution order: iter → push scope → body → pop scope.
            stack.push(Work::PopScope);
            stack.push(Work::Expr(body));
            stack.push(Work::PushScope(vec![(var.node.clone(), var.span.clone())]));
            stack.push(Work::Expr(iter));
        }

        // ── Fun: lambda parameter scope ─────────────────────────────────
        // `fun(x, y) body` — x, y in scope for body.
        Exp::Fun(vars, body) => {
            // Execution order: push scope → body → pop scope.
            stack.push(Work::PopScope);
            stack.push(Work::Expr(body));
            stack.push(Work::PushScope(
                vars.iter()
                    .map(|v| (v.node.clone(), v.span.clone()))
                    .collect(),
            ));
        }

        // ── Binary sub-expressions ──────────────────────────────────────
        Exp::Assert(a) | Exp::Verify(a) => {
            stack.push(Work::Expr(a));
        }
        Exp::Bin(_, a, b) => {
            stack.push(Work::Expr(b));
            stack.push(Work::Expr(a));
        }
        Exp::Pair(a, b) => {
            stack.push(Work::Expr(b));
            stack.push(Work::Expr(a));
        }
        Exp::Ram(a, b) => {
            stack.push(Work::Expr(b));
            stack.push(Work::Expr(a));
        }
        Exp::SetRecord(r, _, v) => {
            stack.push(Work::Expr(v));
            stack.push(Work::Expr(r));
        }

        // ── Unary sub-expressions ───────────────────────────────────────
        Exp::Neg(a) | Exp::Coef(a) | Exp::Poly(a) | Exp::Mle(a) => {
            stack.push(Work::Expr(a));
        }
        Exp::Reduce(_, a) => stack.push(Work::Expr(a)),
        Exp::Proj(a, _) => stack.push(Work::Expr(a)),

        // ── Optional second sub-expression ──────────────────────────────
        Exp::Interpolate(None, e) => stack.push(Work::Expr(e)),
        Exp::Interpolate(Some(p), e) => {
            stack.push(Work::Expr(e));
            stack.push(Work::Expr(p));
        }
        Exp::Evaluate(p, _, None) => stack.push(Work::Expr(p)),
        Exp::Evaluate(p, _, Some(x)) => {
            stack.push(Work::Expr(x));
            stack.push(Work::Expr(p));
        }

        // ── Vector / record: iterate children ───────────────────────────
        Exp::Vec(v) => {
            for child in v.0.iter().rev() {
                stack.push(Work::Expr(child));
            }
        }
        Exp::Record(fields) => {
            for (_, child) in fields.iter().rev() {
                stack.push(Work::Expr(child));
            }
        }

        // ── App: function name is a variable reference ──────────────────
        Exp::App(fid, args) => {
            scopes.mark_used(&fid.node);
            for child in args.0.iter().rev() {
                stack.push(Work::Expr(child));
            }
        }

        // ── Leaves: no sub-expressions ──────────────────────────────────
        Exp::Lit(_) | Exp::Unit | Exp::Range(_) | Exp::Challenge(_, _) | Exp::Random(_, _) => {}
    }
}

// ── Purity check (iterative) ────────────────────────────────────────────

/// Like `is_pure()` but also returns false if any sub-expression is `Exp::App`.
/// Conservative: `is_pure()` treats `App` as pure when args are pure, but the
/// called function may have side effects. Without a call graph we can't know.
///
/// Iterative to avoid stack overflow on deeply nested expressions.
fn is_pure_no_app(exp: &Spanned<UExp>) -> bool {
    let mut stack = vec![exp];
    while let Some(e) = stack.pop() {
        match &e.node {
            Exp::App(_, _) => return false,
            // Impure constructs
            Exp::Log(_, _, _)
            | Exp::Challenge(_, _)
            | Exp::Random(_, _)
            | Exp::Assert(_)
            | Exp::Verify(_) => return false,
            // Pure leaves
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => {}
            // Unary
            Exp::Neg(a)
            | Exp::Coef(a)
            | Exp::Poly(a)
            | Exp::Mle(a)
            | Exp::Reduce(_, a)
            | Exp::Proj(a, _) => stack.push(a),
            // Interpolate
            Exp::Interpolate(None, e) => stack.push(e),
            Exp::Interpolate(Some(p), e) => {
                stack.push(e);
                stack.push(p);
            }
            // Evaluate
            Exp::Evaluate(p, _, None) => stack.push(p),
            Exp::Evaluate(p, _, Some(x)) => {
                stack.push(x);
                stack.push(p);
            }
            // Binary
            Exp::Bin(_, a, b) | Exp::Pair(a, b) | Exp::Ram(a, b) | Exp::SetRecord(a, _, b) => {
                stack.push(b);
                stack.push(a);
            }
            // Let: val is pure if both val and cont are pure
            Exp::Let(_, a, None) => stack.push(a),
            Exp::Let(_, a, Some(b)) => {
                stack.push(b);
                stack.push(a);
            }
            // Map: both body and iter must be pure
            Exp::Map(a, _, b) => {
                stack.push(b);
                stack.push(a);
            }
            // Fun: body must be pure
            Exp::Fun(_, body) => stack.push(body),
            // Vec / record: all children pure
            Exp::Vec(v) => stack.extend(v.0.iter()),
            Exp::Record(fields) => stack.extend(fields.iter().map(|(_, e)| e)),
        }
    }
    true
}

// ── Entry point ─────────────────────────────────────────────────────────

/// Check a declaration for dead variables and dead computations.
///
/// For `Body::Proto`, both the relation (`where ...`) and the body (`{ ... }`)
/// are checked. Function arguments are in scope for both.
pub fn check_dead_variables(decl: &UDecl) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let mut scopes = Scopes::new();

    // For TypeAlias there's nothing to check.
    let (relation, body) = match &decl.body {
        Body::Proto { relation, body } => (Some(relation), body.as_ref()),
        Body::Func { body } => (None, body.as_ref()),
        Body::TypeAlias => return out,
    };

    // Push arg scope — args are in scope for both relation and body.
    let arg_bindings: Vec<(Vid, Range<usize>)> = decl
        .sig
        .args
        .node
        .0
        .iter()
        .map(|arg| (arg.node.id.node.clone(), arg.node.id.span.clone()))
        .collect();
    scopes.push_scope(arg_bindings);

    // Walk the relation first (let bindings in `where` clause).
    if let Some(relation) = relation {
        walk(relation, &mut scopes, &mut out);
    }

    // Then walk the body.
    if let Some(body) = body {
        walk(body, &mut scopes, &mut out);
    }

    // Pop arg scope — emits warnings for unused args.
    scopes.pop_scope(&mut out);

    out
}
