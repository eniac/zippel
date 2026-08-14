//! Integration tests for the lang-derive proc macro.

use lang::diagnostic::{Applicability, Phase, Severity};
use lang_derive::Diagnostic;

#[derive(Diagnostic)]
#[diag("unbound size variable `{$name}`", code = "E0003", error, Semantic)]
struct UnboundSizeVar {
    #[span(label = "`{$name}` is not declared as a type variable")]
    use_span: std::ops::Range<usize>,
    name: String,
    #[suggestion(
        "add `{$name}: Size` to the type variable list",
        replacement = "{$replacement}",
        applicability = "machine-applicable"
    )]
    typevar_span: std::ops::Range<usize>,
    replacement: String,
}

#[derive(Diagnostic)]
#[diag("no proto declaration found", code = "E0001", error, Semantic)]
struct NoProtoDeclaration {
    #[span(label = "module must contain at least one proto declaration")]
    file_span: std::ops::Range<usize>,
}

#[derive(Diagnostic)]
#[diag("duplicate declaration `{$name}`", code = "E0008", error, Semantic)]
struct DuplicateDeclaration {
    #[span(label = "declared here")]
    span: std::ops::Range<usize>,
    name: String,
    #[secondary_label("first declared here")]
    prev_span: std::ops::Range<usize>,
}

#[derive(Diagnostic)]
#[diag("impure relation", code = "E0012", warning, Semantic)]
struct ImpureRelation {
    #[span(label = "relation is not pure")]
    span: std::ops::Range<usize>,
    #[note("relations must be deterministic")]
    _phantom: (),
}

#[test]
fn test_simple_derive() {
    let d = UnboundSizeVar {
        use_span: 10..15,
        name: "N".to_string(),
        typevar_span: 5..10,
        replacement: "N: Size, ".to_string(),
    }
    .build();

    assert_eq!(d.summary, "unbound size variable `N`");
    assert_eq!(d.code.as_deref(), Some("E0003"));
    assert_eq!(d.severity, Severity::Error);
    assert_eq!(d.phase, Phase::Semantic);
    assert_eq!(d.span, 10..15);
    assert_eq!(d.primary_label, "`N` is not declared as a type variable");
    assert_eq!(d.suggestions.len(), 1);
    assert_eq!(
        d.suggestions[0].message,
        "add `N: Size` to the type variable list"
    );
    assert_eq!(d.suggestions[0].replacement, "N: Size, ");
    assert_eq!(d.suggestions[0].span, 5..10);
    assert!(matches!(
        d.suggestions[0].applicability,
        Applicability::MachineApplicable
    ));
}

#[test]
fn test_no_suggestion() {
    let d = NoProtoDeclaration { file_span: 0..100 }.build();

    assert_eq!(d.summary, "no proto declaration found");
    assert_eq!(d.code.as_deref(), Some("E0001"));
    assert_eq!(d.suggestions.len(), 0);
    assert_eq!(d.notes.len(), 0);
}

#[test]
fn test_secondary_label() {
    let d = DuplicateDeclaration {
        span: 10..15,
        name: "foo".to_string(),
        prev_span: 20..25,
    }
    .build();

    assert_eq!(d.summary, "duplicate declaration `foo`");
    assert_eq!(d.secondary_labels.len(), 1);
    assert_eq!(d.secondary_labels[0].span, 20..25);
}

#[test]
fn test_warning_with_note() {
    let d = ImpureRelation {
        span: 10..15,
        _phantom: (),
    }
    .build();

    assert_eq!(d.severity, Severity::Warning);
    assert_eq!(d.notes.len(), 1);
    assert_eq!(d.notes[0].message, "relations must be deterministic");
}
