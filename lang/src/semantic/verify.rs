//! Verify requirement — a proto must reach at least one `verify` check, either in
//! its own body or in a function it calls.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use crate::ast::decl::{Body, UDecl};
use crate::ast::spanned::Spanned;
use crate::ast::{Exp, UExp};
use crate::diagnostic::Diagnostic;
use lang_derive::Diagnostic as DiagnosticDerive;

/// E0013: A proto never reaches a `verify` check.
#[derive(DiagnosticDerive)]
#[diag(
    "proto `{$name}` has no `verify` check",
    code = "E0013",
    error,
    Semantic
)]
struct ProtoWithoutVerify {
    #[span(label = "no `verify(...)` in this proto or in the functions it calls")]
    span: Range<usize>,
    name: String,
    #[note("the verifier's job is to run the proto's `verify` checks; add at least one")]
    _note: (),
}

/// What one declaration body contributes: whether it contains `verify` itself, and the
/// names it applies (functions, or polynomial variables, which never match a declaration).
#[derive(Default)]
struct BodyFacts {
    verifies: bool,
    calls: HashSet<String>,
}

fn collect(exp: &Spanned<UExp>, facts: &mut BodyFacts) {
    match &exp.node {
        Exp::Verify(_) => facts.verifies = true,
        Exp::App(id, _) => {
            facts.calls.insert(id.node.0.clone());
        }
        _ => {}
    }
    for child in exp.node.children() {
        collect(child, facts);
    }
}

/// Check that every proto reaches a `verify`, directly or through the functions it calls.
///
/// Calls are resolved by name without overload resolution: a call counts as verifying if
/// any declaration with that name does. This can only miss errors, never report a proto
/// that does reach a `verify`.
pub fn check_proto_verify(decls: &[Spanned<UDecl>]) -> Vec<Diagnostic> {
    let facts = |body: &Body<crate::ast::Size>| {
        let mut f = BodyFacts::default();
        if let Body::Proto { body: Some(b), .. } | Body::Func { body: Some(b) } = body {
            collect(b, &mut f);
        }
        f
    };

    let mut funcs: HashMap<&str, Vec<BodyFacts>> = HashMap::new();
    for d in decls.iter().filter(|d| d.node.body.is_func()) {
        funcs
            .entry(d.node.sig.name.node.0.as_str())
            .or_default()
            .push(facts(&d.node.body));
    }
    // Fixpoint: a function name verifies if any overload verifies directly or calls one that does.
    let mut verifying: HashSet<&str> = HashSet::new();
    loop {
        let before = verifying.len();
        for (name, overloads) in &funcs {
            if overloads
                .iter()
                .any(|f| f.verifies || f.calls.iter().any(|c| verifying.contains(c.as_str())))
            {
                verifying.insert(name);
            }
        }
        if verifying.len() == before {
            break;
        }
    }

    decls
        .iter()
        .filter(|d| d.node.body.is_proto())
        .filter(|d| {
            let f = facts(&d.node.body);
            !f.verifies && !f.calls.iter().any(|c| verifying.contains(c.as_str()))
        })
        .map(|d| {
            ProtoWithoutVerify {
                span: d.node.sig.name.span.clone(),
                name: d.node.sig.name.node.0.clone(),
                _note: (),
            }
            .build()
        })
        .collect()
}
