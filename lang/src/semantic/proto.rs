//! Proto declaration requirement — every file should have exactly one proto.

use std::ops::Range;

use crate::ast::decl::UDecl;
use crate::ast::spanned::Spanned;

use super::SemanticError;

/// Check that exactly one proto declaration exists.
pub fn check_proto_requirement(
    decls: &[Spanned<UDecl>],
    file_span: Range<usize>,
) -> Vec<SemanticError> {
    let proto_spans: Vec<Range<usize>> = decls
        .iter()
        .filter(|d| d.node.body.is_proto())
        .map(|d| d.span.clone())
        .collect();

    match proto_spans.len() {
        0 => vec![SemanticError::NoProtoDeclaration { file_span }],
        1 => vec![],
        _ => {
            let mut spans = proto_spans.into_iter();
            let first_span = spans.next().unwrap();
            let second_span = spans.next().unwrap();
            vec![SemanticError::MultipleProtoDeclarations {
                first_span,
                second_span,
            }]
        }
    }
}
