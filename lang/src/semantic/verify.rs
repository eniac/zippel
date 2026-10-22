//! Verify requirement: a proto must reach at least one `verify` check, either in its own body
//! or in a function it calls.
//!
//! Calls are followed to the declarations inference resolved them to, so the check sees the
//! overloads the module's sizes select. It runs on concrete instances after type checking.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::ast::decl::{Body, BodyTypes, CBody};
use crate::ast::sig::CSig;
use crate::ast::{CExp, CRef};
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

/// The E0013 diagnostic for the proto `sig`.
fn proto_without_verify(sig: &CSig) -> Diagnostic {
    ProtoWithoutVerify {
        span: sig.name.span.clone(),
        name: sig.name.node.0.clone(),
        _note: (),
    }
    .build()
}

fn has_verify(exp: CRef<'_>) -> bool {
    exp.subexps().any(|e| matches!(e.node(), CExp::Verify(_)))
}

/// The protos among `instances` that reach no `verify`, directly or through the declarations
/// their body's calls resolve to. Every instance must have type-checked, so that each call has
/// a resolution. A `where` clause is a relation for the analyses, never run, so only bodies count.
fn protos_without_verify<'a>(
    instances: impl IntoIterator<Item = (&'a CSig, &'a CBody, &'a BodyTypes)>,
) -> Vec<&'a CSig> {
    // Per instance: whether its body verifies, and the instances its body calls.
    let mut graph: BTreeMap<&CSig, (bool, Vec<&CSig>)> = BTreeMap::new();
    let mut protos = Vec::new();
    for (sig, body, types) in instances {
        let tree = match body {
            Body::Proto { body, .. } | Body::Func { body } => body.as_ref(),
            Body::TypeAlias => None,
        };
        let verifies = tree.is_some_and(|t| has_verify(t.root()));
        let callees = types
            .body
            .calls()
            .map(|(_, call)| &call.declaration)
            .collect();
        graph.insert(sig, (verifies, callees));
        if body.is_proto() {
            protos.push(sig);
        }
    }
    let reaches_verify = |proto: &'a CSig| {
        let mut seen = BTreeSet::from([proto]);
        let mut todo = vec![proto];
        while let Some(sig) = todo.pop() {
            let (verifies, callees) = &graph[sig];
            if *verifies {
                return true;
            }
            todo.extend(callees.iter().copied().filter(|c| seen.insert(*c)));
        }
        false
    };
    protos.into_iter().filter(|p| !reaches_verify(p)).collect()
}

/// E0013 for every proto among `instances` that reaches no `verify`, with the proto.
pub(super) fn check_proto_verify<'a>(
    instances: impl IntoIterator<Item = (&'a CSig, &'a CBody, &'a BodyTypes)>,
) -> Vec<(&'a CSig, Diagnostic)> {
    protos_without_verify(instances)
        .into_iter()
        .map(|sig| (sig, proto_without_verify(sig)))
        .collect()
}
