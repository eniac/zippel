//! Comment preservation tests.
//!
//! Verifies that comments are preserved in the correct positions after
//! formatting, and that formatting is idempotent (comments don't move
//! on the second pass).

use fmt::{Style, format_source, format_source_with_style};

fn fmt(src: &str) -> String {
    format_source(src).expect("parse error")
}

#[test]
fn file_leading_comment() {
    let src = "// file header\nfn f<F: Field>(instance a: F) -> F { a }";
    let out = fmt(src);
    assert!(out.starts_with("// file header\n"), "output: {}", out);
}

#[test]
fn comment_between_decls() {
    let src = "\
fn f<F: Field>(instance a: F) -> F { a }

// second function
fn g<F: Field>(instance a: F) -> F { a }";
    let out = fmt(src);
    assert!(out.contains("// second function"), "output: {}", out);
    // Idempotent.
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn body_leading_comment() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    // comment before return
    a
}";
    let out = fmt(src);
    assert!(out.contains("// comment before return"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn trailing_comment() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;  // trailing
    a
}";
    let out = fmt(src);
    assert!(out.contains("// trailing"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn multiple_leading_comments() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    // first comment
    // second comment
    a
}";
    let out = fmt(src);
    assert!(out.contains("// first comment"), "output: {}", out);
    assert!(out.contains("// second comment"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn block_comment() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    /* block comment */
    a
}";
    let out = fmt(src);
    assert!(out.contains("/* block comment */"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn comment_at_start_of_body() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    // first thing
    let x = a;
    a
}";
    let out = fmt(src);
    assert!(out.contains("// first thing"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn no_comments_unchanged() {
    let src = "fn f<F: Field>(instance a: F) -> F { a }";
    let out = fmt(src);
    // Should not introduce any comments.
    assert!(!out.contains("//"), "output: {}", out);
}

#[test]
fn arg_trailing_comment() {
    let src = "\
fn f<F: Field>(
    instance a: F, // first arg
    instance b: F  // second arg
) -> F { a }";
    let out = fmt(src);
    assert!(out.contains("// first arg"), "output: {}", out);
    assert!(out.contains("// second arg"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn arg_leading_comment() {
    let src = "\
fn f<F: Field>(
    // first arg
    instance a: F,
    // second arg
    instance b: F
) -> F { a }";
    let out = fmt(src);
    assert!(out.contains("// first arg"), "output: {}", out);
    assert!(out.contains("// second arg"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn arg_comment_with_pairing_type() {
    // Test that commas inside angle brackets (Pairing<G1, G2>) don't
    // confuse the arg boundary detection.
    let src = "\
proto p<G1: Group, G2: Group, GT: Pairing<G1, G2>>(
    instance a: G1, // first
    instance b: G2  // second
) where a == b { a }";
    let out = fmt(src);
    assert!(out.contains("// first"), "output: {}", out);
    assert!(out.contains("// second"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn arg_inline_block_comments() {
    let src = "\
fn f<F: Field>(instance /*comment A*/ a /*comment B*/: /*comment C*/ F) -> F { a }";
    let out = fmt(src);
    assert!(out.contains("/*comment A*/"), "output: {}", out);
    assert!(out.contains("/*comment B*/"), "output: {}", out);
    assert!(out.contains("/*comment C*/"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn exp_inline_comment_binop() {
    let src = "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* between */ + b
}";
    let out = fmt(src);
    assert!(out.contains("/* between */"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn exp_inline_comment_app() {
    let src = "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    foo(a /* arg1 */, b /* arg2 */)
}";
    let out = fmt(src);
    assert!(out.contains("/* arg1 */"), "output: {}", out);
    assert!(out.contains("/* arg2 */"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn exp_inline_comment_let() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    let x /* bind */ = a /* val */;
    x
}";
    let out = fmt(src);
    assert!(out.contains("/* bind */"), "output: {}", out);
    assert!(out.contains("/* val */"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn exp_inline_comment_typ() {
    let src = "\
type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;";
    let out = fmt(src);
    assert!(out.contains("/* base */"), "output: {}", out);
    assert!(out.contains("/* m */"), "output: {}", out);
    assert!(out.contains("/* n */"), "output: {}", out);
    let out2 = fmt(&out);
    assert_eq!(out, out2, "not idempotent");
}

#[test]
fn strips_redundant_expression_parens() {
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a + b)) }";
    let out = fmt(src);
    assert!(out.contains("    a + b\n}"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn preserves_comments_near_necessary_parens() {
    let src = "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a + b) /* after */ * c }";
    let out = fmt(src);
    assert!(out.contains("(a + b)"), "output: {}", out);
    assert!(out.contains("/* after */"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn preserves_comments_inside_redundant_parens() {
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a /* inner */ + b)) }";
    let out = fmt(src);
    assert!(out.contains("/* inner */"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn preserves_size_expression_precedence() {
    let src = "fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] { x }";
    let out = fmt(src);
    assert!(out.contains("[F; (M - 1) / 2]"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn line_comment_after_arg() {
    let src = "\
fn f<F: Field>(
    instance a: F, // first
    instance b: F, // second
) -> F {
    a
}";
    let out = fmt(src);
    assert!(out.contains("// first"), "output: {}", out);
    assert!(out.contains("// second"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn line_comment_after_expr() {
    let src = "\
fn f<F: Field>(instance a: F) -> F {
    verify(a == a) // check
}";
    let out = fmt(src);
    assert!(out.contains("// check"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn block_comment_in_call_args() {
    let src = "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    foo(a /* arg1 */, b /* arg2 */)
}";
    let out = fmt(src);
    assert!(out.contains("a, /* arg1 */ b"), "output: {}", out);
    assert!(out.contains("b /* arg2 */"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

fn assert_formatted(src: &str, expected: &str) {
    let out = fmt(src);
    assert_eq!(out, expected);
    assert_eq!(fmt(&out), out, "not idempotent");
}

#[test]
fn moves_comments_before_delimiters_after_them() {
    assert_formatted(
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a // note\n    ;\n    x\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a; // note\n    x\n}\n",
    );
}

#[test]
fn keeps_line_comments_after_commas() {
    assert_formatted(
        "fn f<F: Field>(instance a: F, // first\ninstance b: F) -> F { a }",
        "fn f<F: Field>(\n    instance a: F, // first\n    instance b: F,\n) -> F {\n    a\n}\n",
    );
}

#[test]
fn blank_line_comments_lead_the_next_statement_block() {
    assert_formatted(
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a;\n\n    // explains y\n    let y = x;\n    y\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a;\n\n    // explains y\n    let y = x;\n    y\n}\n",
    );
}

#[test]
fn style_caps_body_and_top_level_blank_lines() {
    let src = "fn f<F: Field>(instance a: F) -> F {\n    let x = a;\n\n\n    x\n}\n\nfn g<F: Field>(instance a: F) -> F { a }";
    let style = Style {
        max_blank_lines: 0,
        ..Style::default()
    };
    let out = format_source_with_style(src, &style).expect("parse error");
    assert_eq!(
        out,
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a;\n    x\n}\nfn g<F: Field>(instance a: F) -> F {\n    a\n}\n"
    );
    assert_eq!(format_source_with_style(&out, &style).unwrap(), out);
}

#[test]
fn line_comment_at_line_start_in_args() {
    let src = "\
fn f<F: Field>(
    // first arg
    instance a: F,
    // second arg
    instance b: F,
) -> F {
    a
}";
    let out = fmt(src);
    assert!(out.contains("// first arg"), "output: {}", out);
    assert!(out.contains("// second arg"), "output: {}", out);
    assert_eq!(out, fmt(&out), "not idempotent");
}

#[test]
fn trailing_comment_before_blank_line_preserves_blank_line() {
    assert_formatted(
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a; // note\n\n    let y = x;\n    y\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    let x = a; // note\n\n    let y = x;\n    y\n}\n",
    );
}
