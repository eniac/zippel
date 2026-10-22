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
//! One [`ExpRef::walk`](crate::ast::ExpRef::walk) per tree (iterative, so deep nesting
//! cannot overflow the stack). The walk says which binding a `Var` resolves to, so
//! shadowing is handled: a reference to `x` marks the innermost `let x = ...` used, not an
//! outer one. A binding left unused when the walk leaves the node that binds it is reported.

use std::collections::HashSet;
use std::ops::Range;

use crate::ast::decl::{Body, UDecl};
use crate::ast::spanned::Spanned;
use crate::ast::{Exp, ExpId, InScope, Stmt, URef, Visit};
use crate::diagnostic::Diagnostic;
use crate::id::{Tid, Vid};
use lang_derive::Diagnostic as DiagnosticDerive;

/// W0001: A variable is never used.
#[derive(DiagnosticDerive)]
#[diag("unused variable `{$name}`", code = "W0001", warning, Semantic)]
struct UnusedVariable {
    name: Vid,
    #[span(label = "`{$name}` is never used")]
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

// ── The walk ────────────────────────────────────────────────────────────

/// A variable binding, and whether anything reads it.
struct Binding {
    name: Vid,
    span: Range<usize>,
    used: bool,
}

impl Binding {
    fn new(name: &Spanned<Vid>) -> Self {
        Self {
            name: name.node.clone(),
            span: name.span.clone(),
            used: false,
        }
    }

    /// Reports the binding if it is unused and not marked intentionally unused (`_x`).
    fn report(self, out: &mut Vec<Diagnostic>) {
        if !self.used && !self.name.0.starts_with('_') {
            out.push(
                UnusedVariable {
                    name: self.name,
                    span: self.span,
                }
                .build(),
            );
        }
    }
}

/// Checks one tree, with `args` (the declaration's arguments) in scope around it.
fn check_tree(exp: URef<'_>, args: &mut [Binding], sizes: &[&Tid], out: &mut Vec<Diagnostic>) {
    // The bindings in scope, each reported when its scope ends if nothing used it.
    let mut in_scope: InScope<'_, Binding> = InScope::new();
    // Statement values whose result is discarded, reported when the walk reaches them.
    let mut dead: HashSet<ExpId> = HashSet::new();
    for visit in exp.walk() {
        let mut mark_used = |name: &Vid| match in_scope.get_mut(name) {
            Some(binding) => binding.used = true,
            None => {
                if let Some(arg) = args.iter_mut().find(|a| &a.name == name) {
                    arg.used = true;
                }
            }
        };
        match visit {
            Visit::Enter(e) => {
                if dead.remove(&e.id()) {
                    out.push(
                        DeadComputation {
                            span: e.span().clone(),
                            _note: (),
                        }
                        .build(),
                    );
                }
                match e.node() {
                    Exp::Var(x) => mark_used(&x.node),
                    // A value in a range bound is an error (E0014), not an unused variable.
                    Exp::Range(range) | Exp::Evaluate(_, Some(range), _) => {
                        for (name, _) in super::values_in_range(range, sizes) {
                            mark_used(&name);
                        }
                    }
                    // A call of a polynomial variable reads it.
                    Exp::App(f, _) => mark_used(&f.node),
                    // `e;` with something after it discards a pure `e`: dead computation. A
                    // block's value, and a `<-`, are never dead.
                    Exp::Block(block) => {
                        for (i, stmt) in block.stmts.iter().enumerate() {
                            if let Stmt::Discard(v) = &stmt.node
                                && block.is_followed(i)
                                && is_pure_no_app(e.at(*v))
                            {
                                dead.insert(*v);
                            }
                        }
                    }
                    _ => {}
                }
            }
            Visit::Bind(x, _) => in_scope.bind(x, Binding::new(x)),
            Visit::Unbind(x) => in_scope.unbind(x).report(out),
            Visit::EnterStmt(_) | Visit::LeaveStmt(_) | Visit::Leave(_) => {}
        }
    }
}

// ── Purity check (iterative) ────────────────────────────────────────────

/// Like `is_pure()` but also returns false if any sub-expression is `Exp::App`.
/// Conservative: `is_pure()` treats `App` as pure when args are pure, but the
/// called function may have side effects. Without a call graph we can't know.
fn is_pure_no_app(exp: URef<'_>) -> bool {
    exp.is_pure() && !exp.subexps().any(|e| matches!(e.node(), Exp::App(..)))
}

// ── Entry point ─────────────────────────────────────────────────────────

/// Check a declaration for dead variables and dead computations.
///
/// For `Body::Proto`, both the relation (`where ...`) and the body (`{ ... }`)
/// are checked. Function arguments are in scope for both.
pub fn check_dead_variables(decl: &UDecl) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    let (relation, body) = match &decl.body {
        Body::Proto { relation, body } => (Some(relation), body.as_ref()),
        Body::Func { body } => (None, body.as_ref()),
        Body::TypeAlias => return out,
    };
    // The arguments are in scope in both the relation and the body.
    let mut args: Vec<Binding> = decl
        .sig
        .args
        .node
        .0
        .iter()
        .map(|arg| Binding::new(&arg.node.id))
        .collect();
    let sizes = super::size_params(decl);
    for tree in relation.into_iter().chain(body) {
        check_tree(tree.root(), &mut args, &sizes, &mut out);
    }
    for arg in args {
        arg.report(&mut out);
    }
    out
}
