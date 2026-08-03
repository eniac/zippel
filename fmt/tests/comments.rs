//! Comment preservation tests.
//!
//! Verifies that comments are preserved in the correct positions after
//! formatting, and that formatting is idempotent (comments don't move
//! on the second pass).

use fmt::format_source;

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
