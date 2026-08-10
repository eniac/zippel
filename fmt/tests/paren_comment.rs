//! Tests for comments around redundant parentheses in binops and relations.
//!
//! The parser strips parens from the AST, so the formatter never sees
//! them — comments around dropped parens are merged into the
//! surrounding gap by the cursor's `advance_to_token`.

use fmt::format_source;

fn fmt(src: &str) -> String {
    format_source(src).expect("parse error")
}

fn assert_idempotent(src: &str) {
    let out = fmt(src);
    assert_eq!(fmt(&out), out, "not idempotent");
}

#[test]
fn redundant_paren_around_subexpr_in_complex_binop() {
    // (a + b) * c — parens needed for precedence, kept by formatter
    assert_idempotent(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a + b) * c }",
    );
}

#[test]
fn redundant_paren_around_rhs_in_complex_binop() {
    // a + (b * c) — parens redundant (same precedence, left-assoc)
    assert_idempotent(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { a + (b * c) }",
    );
}

#[test]
fn redundant_paren_around_rhs_with_comment() {
    // a + (/* c */ b * c) — comment inside redundant parens
    let out = fmt(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { a + (/* c */ b * c) }",
    );
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {\n    a + /* c */ b * c\n}\n"
    );
}

#[test]
fn three_op_chain_with_paren_on_first() {
    // (a + b) + c — parens redundant (same op, left-assoc)
    assert_idempotent(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a + b) + c }",
    );
}

#[test]
fn redundant_paren_around_subexpr_with_comment() {
    // (/* c */ a + b) * c — parens kept (precedence), comment before a
    let out = fmt(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (/* c */ a + b) * c }",
    );
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {\n    /* c */\n    (a + b) * c\n}\n"
    );
}

#[test]
fn three_op_chain_with_paren_on_first_with_comment() {
    // (/* c */ a + b) + c — parens dropped, comment before a
    let out = fmt(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (/* c */ a + b) + c }",
    );
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {\n    /* c */\n    a + b + c\n}\n"
    );
}

#[test]
fn nested_redundant_parens_with_comments() {
    // Multiple comments around nested redundant parens
    let out = fmt(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F { /* A */ ( /* B */ (a + b) /* C */ ) + /* D */ (c * d) }",
    );
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {\n    /* A */\n    /* B */\n    a + b /* C */ + /* D */ c * d\n}\n"
    );
}

#[test]
fn comment_both_sides_of_paren_simple() {
    // /* before */ ( /* after */ a + b) — both comments merge when paren dropped
    let out = fmt(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { /* before */ ( /* after */ a + b) }",
    );
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F, instance b: F) -> F {\n    /* before */ /* after */\n    a + b\n}\n"
    );
    assert_idempotent(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { /* before */ ( /* after */ a + b) }",
    );
}

#[test]
fn comment_both_sides_of_paren_complex() {
    let out = fmt(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { /* before */ ( /* after */ a + b * c) }",
    );
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {\n    /* before */ /* after */\n    a + b * c\n}\n"
    );
    assert_idempotent(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { /* before */ ( /* after */ a + b * c) }",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Relations (where clause)
// ══════════════════════════════════════════════════════════════════

#[test]
fn relation_fallback_paren_comment() {
    // where (/* c */ a + b) == c — hits the _ => fallback
    let out = fmt(
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F) where (/* c */ a + b) == c { a }",
    );
    assert_eq!(
        out,
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F) where /* c */ a + b == c {\n    a\n}\n"
    );
    assert_eq!(fmt(&out), out, "not idempotent");
}

#[test]
fn relation_let_paren_comment() {
    // where let x = (/* c */ a + b); x == c
    let out = fmt(
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) where let x = (/* c */ a + b); x == c { a }",
    );
    assert_eq!(fmt(&out), out, "not idempotent");
}
