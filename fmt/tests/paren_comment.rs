//! Tests for comments around redundant parentheses in binops and relations.
//!
//! The parser strips parens from the AST, so the formatter never sees
//! them — comments around dropped parens are merged into the
//! surrounding gap by the cursor's `advance_to_token`.

mod common;

use common::assert_ok;

#[test]
fn redundant_paren_around_subexpr_in_complex_binop() {
    // (a + b) * c — parens needed for precedence, kept by formatter
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a + b) * c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    (a + b) * c
}
",
    );
}

#[test]
fn redundant_paren_around_rhs_in_complex_binop() {
    // a + (b * c) — parens redundant (same precedence, left-assoc)
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { a + (b * c) }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + b * c
}
",
    );
}

#[test]
fn redundant_paren_around_rhs_with_comment() {
    // a + (/* c */ b * c) — comment inside redundant parens
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { a + (/* c */ b * c) }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + /* c */ b * c
}
",
    );
}

#[test]
fn three_op_chain_with_paren_on_first() {
    // (a + b) + c — parens redundant (same op, left-assoc)
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a + b) + c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + b + c
}
",
    );
}

#[test]
fn redundant_paren_around_subexpr_with_comment() {
    // (/* c */ a + b) * c — parens kept (precedence), comment before a
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (/* c */ a + b) * c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    /* c */
    (a + b) * c
}
",
    );
}

#[test]
fn three_op_chain_with_paren_on_first_with_comment() {
    // (/* c */ a + b) + c — parens dropped, comment before a
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (/* c */ a + b) + c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    /* c */
    a + b + c
}
",
    );
}

#[test]
fn nested_redundant_parens_with_comments() {
    // Multiple comments around nested redundant parens
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F { /* A */ ( /* B */ (a + b) /* C */ ) + /* D */ (c * d) }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    /* A */
    /* B */
    a + b /* C */ + /* D */ c * d
}
",
    );
}

#[test]
fn comment_both_sides_of_paren_simple() {
    // /* before */ ( /* after */ a + b) — both comments merge when paren dropped
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { /* before */ ( /* after */ a + b) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    /* before */ /* after */
    a + b
}
",
    );
}

#[test]
fn comment_both_sides_of_paren_complex() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { /* before */ ( /* after */ a + b * c) }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    /* before */ /* after */
    a + b * c
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Relations (where clause)
// ══════════════════════════════════════════════════════════════════

#[test]
fn relation_fallback_paren_comment() {
    // where (/* c */ a + b) == c — hits the _ => fallback
    assert_ok(
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F) where (/* c */ a + b) == c { a }",
        "\
proto p<F: Field>(instance a: F, instance b: F, instance c: F) where /* c */ a + b == c {
    a
}
",
    );
}

#[test]
fn relation_let_paren_comment() {
    // where let x = (/* c */ a + b); x == c
    assert_ok(
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) where let x = (/* c */ a + b); x == c { a }",
        "\
proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) where
    let x = /* c */ a + b;
    x == c
{
    a
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Comments in broken binop chains
// ══════════════════════════════════════════════════════════════════

#[test]
fn long_chain_inline_comment_before_op() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb /* c */ + c
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb /* c */ + c
}
",
    );
}

#[test]
fn long_chain_line_comment_after_operand() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb // c
    + c
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a
        + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb // c
        + c
}
",
    );
}

#[test]
fn long_chain_comment_inside_rhs_call() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    a + gate_identity(bbbbbbbbbbbbb, /* mid */ ccccccccccccc, ddddddddddddd) + eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
}
",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
        + gate_identity(bbbbbbbbbbbbb, /* mid */ ccccccccccccc, ddddddddddddd)
        + eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
}
",
    );
}

#[test]
fn long_mul_chain_inline_comment_between_operands() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    a * bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb /* c */ * cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
}
",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
        * bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb /* c */
        * cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
}
",
    );
}

#[test]
fn long_chain_comment_after_op() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + /* x */ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb + c
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        + /* x */ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
        + c
}
",
    );
}

#[test]
fn nested_mul_in_long_add_chain_with_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    a + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb * /* x */ cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc + d
}
",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
        + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
            * /* x */ cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
        + d
}
",
    );
}

#[test]
fn broken_chain_redundant_paren_around_rhs() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + (b * c) + dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        + b * c
        + dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
    );
}

#[test]
fn broken_chain_comment_inside_redundant_paren() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + (/* x */ b * c) + dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        + /* x */ b * c
        + dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
    );
}

#[test]
fn broken_chain_precedence_paren() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + (b + c) * dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        + (b + c) * dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
    );
}

#[test]
fn broken_chain_comment_around_precedence_paren() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + (/* x */ b + c) * dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        + /* x */ (b + c) * dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
}
",
    );
}

#[test]
fn short_chain_line_comment_forces_break() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a + b // force break
    + c
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a
        + b // force break
        + c
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Comments in every position of add+mul chains
// ══════════════════════════════════════════════════════════════════

#[test]
fn block_comments_everywhere_flat_chain() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    /* before a */ a /* after a */ + /* before b */ b /* after b */ * /* before c */ c /* after c */ + /* before d */ d /* after d */
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    /* before a */
    a /* after a */
        + /* before b */ b /* after b */ * /* before c */ c /* after c */
        + /* before d */ d /* after d */
}
",
    );
}

#[test]
fn block_comments_everywhere_broken_chain() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    /* before a */ aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa /* after a */ + /* before b */ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb /* after b */ * /* before c */ cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc /* after c */ + /* before d */ dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd /* after d */
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    /* before a */
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa /* after a */
        + /* before b */ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb /* after b */
            * /* before c */ cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc /* after c */
        + /* before d */ dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd /* after d */
}
",
    );
}

#[test]
fn line_comments_everywhere_short_chain() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    // before a
    a // after a
    // before +
    + // after +
    b // after b
    // before *
    * // after *
    c // after c
    // before +
    + // after +
    d // after d
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    // before a
    a // after a
        // before +
        + // after +
        b // after b
            // before *
            * // after *
            c // after c
        // before +
        + // after +
        d // after d
}
",
    );
}

#[test]
fn mixed_line_block_comments_in_add_mul_chain() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    // before a
    a /* after a */ + /* before b */ b // after b
    // before *
    * /* after star */ c // after c
    + d
}
",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) -> F {
    // before a
    a /* after a */
        + /* before b */ b // after b
            // before *
            * /* after star */ c // after c
        + d
}
",
    );
}
