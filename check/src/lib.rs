//! The checks behind `zippel-check`: everything `ZippelHandler::compile` does short of running
//! the protocol.
//!
//! [`lang::check::check_source`] parses, runs the semantic checks, concretizes sizes, and
//! type-checks. [`check`] then builds the Graph IR and projects the prover and verifier, which
//! is where errors such as the verifier depending on a witness surface.

use std::collections::HashSet;

use backend::ArkBls12_381;
use graph::{GraphError, PrivateValue, UDag, UDags};
use lang::ast::CModule;
use lang::check::{CheckReport, Finding, binding_span, check_source, type_error_finding};
use lang::diagnostic::{Diagnostic, Phase};
use lang::id::Tid;
use share::Ctx;

/// Graph construction and projection are curve-independent; this backend just has to support
/// every operation, including pairings.
type Backend = ArkBls12_381;

/// Check `src` under `sizes`: [`check_source`], then Graph IR construction and the
/// prover/verifier projection when type checking succeeded.
pub fn check(src: &str, sizes: &Ctx<Tid, usize>) -> CheckReport {
    let mut report = check_source(src, sizes);
    if let Some(module) = &report.module {
        let findings = lower(module);
        report.findings.extend(findings);
        report.findings.sort_by(|a, b| {
            (a.diagnostic.span.start, a.diagnostic.severity)
                .cmp(&(b.diagnostic.span.start, b.diagnostic.severity))
        });
    }
    report
}

fn lower(module: &CModule) -> Vec<Finding> {
    let dags = match UDags::<Backend>::from_module(module.clone()) {
        Ok(dags) => dags,
        Err(e) => return vec![graph_finding(module, None, &e)],
    };
    let mut findings = Vec::new();
    let mut seen = HashSet::new();
    for proto in dags.protocols() {
        // Same steps, in the same order, as `ZippelHandler::compile`.
        let renamed = proto.clone().rename_inner_nodes();
        let _ = renamed.get_prover();
        if let Err(e) = renamed.get_verifier() {
            let finding = graph_finding(module, Some(proto), &e);
            let d = &finding.diagnostic;
            if seen.insert((d.span.clone(), d.summary.clone())) {
                findings.push(finding);
            }
        }
    }
    findings
}

fn graph_finding(module: &CModule, proto: Option<&UDag<Backend>>, e: &GraphError) -> Finding {
    let proto_span = || {
        let name = proto.map(UDag::name);
        module
            .iter()
            .find(|(sig, body)| {
                body.is_proto() && name.as_ref().is_none_or(|n| *n == sig.name.node)
            })
            .map_or(0..0, |(sig, _)| sig.name.span.clone())
    };
    match e {
        GraphError::Type(te) => type_error_finding(te, proto_span()),
        GraphError::NonPolynomialFun(reason, span) => Finding {
            diagnostic: Diagnostic::error(Phase::Type, span.clone(), "`fun` body is not a polynomial")
                .primary_label(reason)
                .note("a `fun` body may only add, subtract, multiply, and negate its parameters and constants"),
            detail: None,
        },
        GraphError::PrivateValueInVerifier { kind, name, node } => {
            // `get_verifier` ran on the renamed DAG, whose let-binding names are mangled; the
            // original DAG has the same node indices and the source names.
            let name = match kind {
                PrivateValue::Arg(_) => name.clone(),
                PrivateValue::Random => proto.and_then(|p| {
                    p.vctx
                        .iter()
                        .find(|(n, _)| n.index() == *node)
                        .map(|(_, v)| v.clone())
                }),
            };
            let random = matches!(kind, PrivateValue::Random);
            let span = binding_span(module, name.as_ref(), random).unwrap_or_else(proto_span);
            let summary = GraphError::PrivateValueInVerifier {
                kind: *kind,
                name: name.clone(),
                node: *node,
            }
            .to_string()
            .replacen("The verifier", "the verifier", 1);
            let label = if random {
                "sampled by the prover; the verifier would draw its own, different value"
            } else {
                "the verifier never receives this"
            };
            Finding {
                diagnostic: Diagnostic::error(Phase::Type, span, &summary)
                    .primary_label(label)
                    .note(
                        "a `verify` check may only use `instance` arguments, challenges, and values \
                         the prover sends with `<-` (directly or through `let`s)",
                    ),
                detail: None,
            }
        }
        other => Finding {
            diagnostic: Diagnostic::error(
                Phase::Type,
                proto_span(),
                &other.to_string().split_whitespace().collect::<Vec<_>>().join(" "),
            )
            .primary_label("while building the protocol graph"),
            detail: Some(other.to_string()),
        },
    }
}
