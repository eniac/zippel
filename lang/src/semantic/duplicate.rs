//! Duplicate declaration check — two declarations with the same signature.

use std::ops::Range;

use crate::ast::decl::UDecl;
use crate::ast::sig::Sig;
use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::diagnostic::Diagnostic;
use lang_derive::Diagnostic as DiagnosticDerive;

/// E0010: Two declarations share the same signature.
#[derive(DiagnosticDerive)]
#[diag("duplicate declaration: {$name}", code = "E0010", error, Semantic)]
struct DuplicateDeclaration {
    #[span(label = "{$name} declared a second time here")]
    second_span: Range<usize>,
    name: String,
    #[secondary_label("{$name} first defined here")]
    first_span: Range<usize>,
}

/// Check for duplicate declarations across a list of declarations.
pub fn check_duplicate_declarations(decls: &[Spanned<UDecl>]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let mut seen: Vec<(Sig<Size>, Range<usize>)> = Vec::new();

    for d in decls {
        if d.node.body.is_type_alias() {
            continue;
        }
        if let Some((_, orig_span)) = seen.iter().find(|(s, _)| *s == d.node.sig) {
            let kind = if d.node.body.is_proto() {
                "proto"
            } else {
                "fn"
            };
            let name = format!(
                "{kind} {}({})",
                d.node.sig.name.node.0, d.node.sig.args.node
            );
            errors.push(
                DuplicateDeclaration {
                    name,
                    first_span: orig_span.clone(),
                    second_span: d.span.clone(),
                }
                .build(),
            );
        }
        seen.push((d.node.sig.clone(), d.span.clone()));
    }
    errors
}
