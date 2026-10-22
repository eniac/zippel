//! Unused functions: a function no call anywhere in the module names.
//!
//! Overloads are chosen by sizes, so whether one overload is called depends on the sizes; whether
//! any overload of a name is called does not. A function is therefore reported when nothing calls
//! its name. A call is an application whose name is not a variable in scope (`p(x)` on a
//! polynomial variable `p` is not a call). Calls from functions that are themselves unused, and
//! recursive calls, count. Functions prefixed with `_` are treated as intentionally unused.

use std::collections::HashSet;
use std::ops::Range;

use crate::ast::decl::{Body, UDecl};
use crate::ast::spanned::Spanned;
use crate::ast::{Exp, InScope, URef, Visit};
use crate::diagnostic::Diagnostic;
use crate::id::Vid;
use lang_derive::Diagnostic as DiagnosticDerive;

/// W0002: A function is never called.
#[derive(DiagnosticDerive)]
#[diag(
    "function `{$name}` is never called",
    code = "W0002",
    warning,
    Semantic
)]
struct UnusedFunction {
    name: String,
    #[span(label = "no call in this file names `{$name}`")]
    span: Range<usize>,
    #[note("if this is intentional, prefix the name with an underscore")]
    _note: (),
}

/// Adds to `called` the names `exp` calls, where `args` are the declaration's arguments.
fn collect_calls<'a>(exp: URef<'a>, args: &[&Vid], called: &mut HashSet<&'a Vid>) {
    let mut in_scope = InScope::new();
    for visit in exp.walk() {
        match visit {
            Visit::Bind(x, _) => in_scope.bind(x, ()),
            Visit::Unbind(x) => in_scope.unbind(x),
            Visit::Enter(e) => {
                if let Exp::App(f, _) = e.node()
                    && in_scope.get(&f.node).is_none()
                    && !args.contains(&&f.node)
                {
                    called.insert(&f.node);
                }
            }
            Visit::EnterStmt(_) | Visit::LeaveStmt(_) | Visit::Leave(_) => {}
        }
    }
}

/// Warn about every function whose name no call in `decls` names.
pub fn check_unused_functions(decls: &[Spanned<UDecl>]) -> Vec<Diagnostic> {
    let mut called = HashSet::new();
    for decl in decls {
        let args: Vec<&Vid> = decl
            .node
            .sig
            .args
            .node
            .0
            .iter()
            .map(|a| &a.node.id.node)
            .collect();
        let trees = match &decl.node.body {
            Body::Proto { relation, body } => vec![Some(relation), body.as_ref()],
            Body::Func { body } => vec![body.as_ref()],
            Body::TypeAlias => vec![],
        };
        for tree in trees.into_iter().flatten() {
            collect_calls(tree.root(), &args, &mut called);
        }
    }
    decls
        .iter()
        .filter(|d| d.node.body.is_func())
        .filter(|d| {
            let name = &d.node.sig.name.node;
            !name.0.starts_with('_') && !called.contains(name)
        })
        .map(|d| {
            UnusedFunction {
                name: d.node.sig.name.node.0.clone(),
                span: d.node.sig.name.span.clone(),
                _note: (),
            }
            .build()
        })
        .collect()
}
