//! Proto declaration requirement — every file should have exactly one proto.

use std::ops::Range;

use crate::ast::decl::UDecl;
use crate::ast::spanned::Spanned;
use crate::diagnostic::Diagnostic;
use lang_derive::Diagnostic as DiagnosticDerive;

/// E0001: No proto declaration in the file.
#[derive(DiagnosticDerive)]
#[diag("no proto declaration found", code = "E0001", error, Semantic)]
struct NoProtoDeclaration {
    #[span(label = "every file must contain exactly one proto declaration")]
    file_span: Range<usize>,
    #[note("add a `proto` declaration to this file")]
    _note: (),
}

/// E0002: Multiple proto declarations in the file.
#[derive(DiagnosticDerive)]
#[diag("multiple proto declarations", code = "E0002", error, Semantic)]
struct MultipleProtoDeclarations {
    #[span(label = "a file must contain exactly one proto declaration")]
    second_span: Range<usize>,
    #[secondary_label("first proto declared here")]
    first_span: Range<usize>,
}

/// Check that exactly one proto declaration exists.
pub fn check_proto_requirement(
    decls: &[Spanned<UDecl>],
    file_span: Range<usize>,
) -> Vec<Diagnostic> {
    let proto_spans: Vec<Range<usize>> = decls
        .iter()
        .filter(|d| d.node.body.is_proto())
        .map(|d| d.span.clone())
        .collect();

    match proto_spans.len() {
        0 => vec![
            NoProtoDeclaration {
                file_span,
                _note: (),
            }
            .build(),
        ],
        1 => vec![],
        _ => {
            let mut spans = proto_spans.into_iter();
            let first_span = spans.next().unwrap();
            let second_span = spans.next().unwrap();
            vec![
                MultipleProtoDeclarations {
                    first_span,
                    second_span,
                }
                .build(),
            ]
        }
    }
}
