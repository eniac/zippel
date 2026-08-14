//! Parser error tests.

use super::super::parse_decls;
use crate::diagnostic::render_diagnostic;

// ── Render tests ───────────────────────────────────────────────────

#[test]
fn render_shows_line_col() {
    let src = "fn f<F: Field>(instance a: F) -> F {\n    a +\n}\n";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let rendered = render_diagnostic(&errors[0], "test.zippel", src);
    eprintln!("--- error render ---\n{}", rendered);
    // Error points to `}` on line 3 — the parser expected
    // an expression after `+` but found `}`.
    assert!(rendered.contains("3:"), "rendered: {}", rendered);
    assert!(rendered.contains("}"), "rendered: {}", rendered);
    assert!(rendered.contains("found"), "rendered: {}", rendered);
    assert!(rendered.contains("expected"), "rendered: {}", rendered);
    assert!(rendered.contains("error:"), "rendered: {}", rendered);
    // Should have a context label from chumsky.
    assert!(rendered.contains("while parsing"), "rendered: {}", rendered);
}

#[test]
fn render_missing_rparen() {
    let src = "fn f<F: Field>(instance a: F -> F { a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let rendered = render_diagnostic(&errors[0], "test.zippel", src);
    eprintln!("--- error render ---\n{}", rendered);
    // Should show `->` as found, and `,` `)` as expected
    assert!(rendered.contains("->"), "rendered: {}", rendered);
    assert!(rendered.contains("expected"), "rendered: {}", rendered);
    assert!(rendered.contains("')'"), "rendered: {}", rendered);
    assert!(rendered.contains("','"), "rendered: {}", rendered);
}

#[test]
fn render_duplicate_decl() {
    use crate::ast::module::UModule;
    use crate::diagnostic::render_diagnostic;
    let src = "fn f<F: Field>(instance a: F) -> F { a }\nfn f<F: Field>(instance a: F) -> F { a }";
    let (_, diags) = UModule::parse(src);
    let diag = diags
        .iter()
        .find(|d| d.summary.contains("duplicate"))
        .expect("should find duplicate declaration diagnostic");
    let rendered = render_diagnostic(diag, "test.zippel", src);
    eprintln!("--- error render ---\n{}", rendered);
    // Error should point to the second declaration (line 2)
    assert!(rendered.contains("2:"), "rendered: {}", rendered);
    assert!(rendered.contains("duplicate"), "rendered: {}", rendered);
    assert!(rendered.contains("first defined"), "rendered: {}", rendered);
    // Should show user-friendly declaration description
    assert!(rendered.contains("fn f("), "rendered: {}", rendered);
}

#[test]
fn context_label_shows_innermost() {
    // Error inside a declaration should show a context label
    // from chumsky's native context stack.
    let src = "fn f<F: Field>(instance a: F) -> F { [a fro x in 0..N] }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let rendered = render_diagnostic(&errors[0], "test.zp", src);
    assert!(
        rendered.contains("while parsing"),
        "should show context label: {rendered}"
    );
}

// ── Native behavior assertions ─────────────────────────────────────

#[test]
fn boundary_error_shows_label_not_raw_tokens() {
    // Expression boundary failure: `;` at start of expression.
    // Chumsky's label_with replaces the expression sub-parser's expected
    // with the "expression" label. The declaration body parser also
    // expects `let`, `identifier`, `}`, so the label appears alongside
    // those tokens in the merged expected list.
    let src = "fn f<F: Field>(instance a: F) -> F { ; }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let e = &errors[0];
    // The "expression" label from chumsky's label_with should appear.
    assert!(
        e.summary.contains("expression"),
        "summary should contain 'expression' label: {}",
        e.summary
    );
    assert!(
        e.primary_label.contains("expression"),
        "primary label should contain 'expression' label: {}",
        e.primary_label
    );
}

#[test]
fn interior_error_retains_raw_expected() {
    // Expression interior failure: `a +` then `}`.
    // Chumsky preserves raw expected patterns from the expression atom parser.
    // The pratt parser's error handling means the expression context may not
    // appear on the context stack — only the declaration context does.
    // This is native chumsky behavior.
    let src = "fn f<F: Field>(instance a: F) -> F { a + }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let e = &errors[0];
    // Should have found '}'
    assert!(
        e.summary.contains("found '}'"),
        "summary should contain found '}}': {}",
        e.summary
    );
    // Should have raw expected patterns (not replaced with a single label)
    assert!(
        e.primary_label.contains("one of"),
        "primary label should list multiple expected patterns: {}",
        e.primary_label
    );
}

#[test]
fn type_boundary_error_shows_label() {
    // Type boundary failure: `)` where a type is expected.
    // Chumsky's label_with replaces expected with "type".
    let src = "fn f<F: Field>(instance a: ) -> F { a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let e = &errors[0];
    assert!(
        e.summary.contains("expected type"),
        "summary should contain 'expected type': {}",
        e.summary
    );
    assert!(
        e.primary_label.contains("expected type"),
        "primary label should contain 'expected type': {}",
        e.primary_label
    );
}

#[test]
fn no_suggestions_or_notes_on_generic_errors() {
    // Generic parse errors should have no suggestions or notes.
    let src = "fn f<F: Field>(instance a: F) -> F {\n    a +\n}\n";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            e.suggestions.is_empty() && e.notes.is_empty(),
            "unexpected suggestions: {:?}, notes: {:?}",
            e.suggestions,
            e.notes
        );
    }
}

#[test]
fn no_errors_for_valid_parse() {
    let src = "fn f<F: Field>(instance a: F) -> F { a }";
    let (_, errors) = parse_decls(src);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
}
