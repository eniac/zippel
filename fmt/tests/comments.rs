//! Comment preservation tests.
//!
//! Verifies that comments are preserved in the correct positions after
//! formatting, and that formatting is idempotent (comments don't move
//! on the second pass).

mod common;

use common::{assert_ok, assert_ok_with_style};
use fmt::Style;

#[test]
fn file_leading_comment() {
    assert_ok(
        "\
// file header
fn f<F: Field>(instance a: F) -> F { a }",
        "\
// file header
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn comment_between_decls() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a }

// second function
fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}

// second function
fn g<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn body_leading_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    // comment before return
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    // comment before return
    a
}
",
    );
}

#[test]
fn trailing_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;  // trailing
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; // trailing
    a
}
",
    );
}

#[test]
fn multiple_leading_comments() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    // first comment
    // second comment
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    // first comment
    // second comment
    a
}
",
    );
}

#[test]
fn block_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    /* block comment */
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    /* block comment */
    a
}
",
    );
}

#[test]
fn multiline_block_comment_preserves_indent() {
    // Multiline block comment inline between two statements.
    // Inner lines should be indented to match the surrounding context.
    // `gap_hard` (statement boundary) always emits a hardline after
    // the gap, so `let y` goes on a new line even though source had
    // `*/ let y` on the same line.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { let x = a; /*
    hello world
*/ let y = a; y }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; /*
    hello world
    */
    let y = a;
    y
}
",
    );
}

#[test]
fn comment_at_start_of_body() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    // first thing
    let x = a;
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    // first thing
    let x = a;
    a
}
",
    );
}

#[test]
fn comment_before_let_in_comprehension() {
    // A comment leading a `let` body inside `[ ... for ... ]` must not gain
    // a blank line after `[` (previously one more on every pass).
    assert_ok(
        "\
fn f<F: Field, N: Size>(instance x: [F; N]) -> [F; N] {
    [
        // comment
        let y = x[i];
        y
        for i in 0..N
    ]
}",
        "\
fn f<F: Field, N: Size>(instance x: [F; N]) -> [F; N] {
    [
        // comment
        let y = x[i];
        y
        for i in 0..N
    ]
}
",
    );
}

#[test]
fn blank_lines_after_comprehension_open_dropped() {
    assert_ok(
        "\
fn f<F: Field, N: Size>(instance x: [F; N]) -> [F; N] {
    [

        // comment
        let y = x[i];
        y
        for i in 0..N
    ]
}",
        "\
fn f<F: Field, N: Size>(instance x: [F; N]) -> [F; N] {
    [
        // comment
        let y = x[i];
        y
        for i in 0..N
    ]
}
",
    );
}

#[test]
fn no_comments_unchanged() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn arg_comments() {
    for (src, expected) in [
        (
            "\
fn f<F: Field>(
    instance a: F, // first arg
    instance b: F  // second arg
) -> F { a }",
            "\
fn f<F: Field>(
    instance a: F, // first arg
    instance b: F, // second arg
) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field>(
    // first arg
    instance a: F,
    // second arg
    instance b: F
) -> F { a }",
            "\
fn f<F: Field>(
    // first arg
    instance a: F,
    // second arg
    instance b: F,
) -> F {
    a
}
",
        ),
        (
            "\
proto p<G1: Group, G2: Group, GT: Pairing<G1, G2>>(
    instance a: G1, // first
    instance b: G2  // second
) where a == b { a }",
            "\
proto p<G1: Group, G2: Group, GT: Pairing<G1, G2>>(
    instance a: G1, // first
    instance b: G2, // second
) where a == b {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance /*comment A*/ a /*comment B*/ : /*comment C*/ F) -> F { a }",
            "\
fn f<F: Field>(instance /*comment A*/ a /*comment B*/ : /*comment C*/ F) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn exp_inline_comments() {
    for (src, expected) in [
        (
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* between */ + b
}",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* between */ + b
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    foo(a /* arg1 */, b /* arg2 */)
}",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    foo(a /* arg1 */, b /* arg2 */)
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F) -> F {
    let x /* bind */ = a /* val */;
    x
}",
            "\
fn f<F: Field>(instance a: F) -> F {
    let x /* bind */ = a /* val */;
    x
}
",
        ),
        (
            "type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;",
            "\
type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn preserves_comments_near_necessary_parens() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a + b) /* after */ * c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    (a + b) /* after */ * c
}
",
    );
}

#[test]
fn preserves_comments_inside_redundant_parens() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a /* inner */ + b)) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* inner */ + b
}
",
    );
}

#[test]
fn line_comment_after_arg() {
    assert_ok(
        "\
fn f<F: Field>(
    instance a: F, // first
    instance b: F, // second
) -> F {
    a
}",
        "\
fn f<F: Field>(
    instance a: F, // first
    instance b: F, // second
) -> F {
    a
}
",
    );
}

#[test]
fn line_comment_after_expr() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(a == a) // check
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(a == a) // check
}
",
    );
}

#[test]
fn block_comment_in_call_args() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    foo(a /* arg1 */, b /* arg2 */)
}",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    foo(a /* arg1 */, b /* arg2 */)
}
",
    );
}

#[test]
fn moves_comments_before_delimiters_after_them() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a // note
    ;
    x
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a // note
    ;
    x
}
",
    );
}

#[test]
fn keeps_line_comments_after_commas() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F, // first
instance b: F) -> F { a }",
        "\
fn f<F: Field>(
    instance a: F, // first
    instance b: F,
) -> F {
    a
}
",
    );
}

#[test]
fn blank_line_comments_lead_the_next_statement_block() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;

    // explains y
    let y = x;
    y
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;

    // explains y
    let y = x;
    y
}
",
    );
}

#[test]
fn style_caps_body_and_top_level_blank_lines() {
    assert_ok_with_style(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;


    x
}

fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    x
}
fn g<F: Field>(instance a: F) -> F {
    a
}
",
        &Style {
            max_blank_lines: 0,
            ..Style::default()
        },
    );
}

#[test]
fn line_comment_at_line_start_in_args() {
    assert_ok(
        "\
fn f<F: Field>(
    // first arg
    instance a: F,
    // second arg
    instance b: F,
) -> F {
    a
}",
        "\
fn f<F: Field>(
    // first arg
    instance a: F,
    // second arg
    instance b: F,
) -> F {
    a
}
",
    );
}

#[test]
fn trailing_comment_before_blank_line_preserves_blank_line() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; // note

    let y = x;
    y
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; // note

    let y = x;
    y
}
",
    );
}

#[test]
fn blank_lines_between_comment_blocks_in_body() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; // block 0

    // block 1

    // block 2

    let y = x;
    y
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; // block 0

    // block 1

    // block 2

    let y = x;
    y
}
",
    );
}

#[test]
fn blank_lines_between_comment_blocks_at_top_level() {
    assert_ok(
        "\
// block 0

// block 1

// block 2

fn f<F: Field>(instance a: F) -> F { a }",
        "\
// block 0

// block 1

// block 2

fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn blank_lines_between_decls_preserved() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a }


fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}

fn g<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn blank_lines_between_decls_with_comments_preserved() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a }

// comment

fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}

// comment

fn g<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn no_blank_line_between_decls_guaranteed() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a }
fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}

fn g<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn structural_positions_strip_blank_lines() {
    // Leading blank lines after `{` and trailing blank lines before `}` are
    // stripped; body-level blank lines and inter-comment blank lines are
    // preserved. Blank line after `)` before `->` is stripped. Leading blank
    // lines before `where`, after `where`, after `{`, and trailing blank lines
    // before `}` are stripped.
    for (src, expected) in [
        (
            "\
fn f<F: Field>(instance a: F) -> F {

    // first

    // second

    let x = a;

    x

}",
            "\
fn f<F: Field>(instance a: F) -> F {
    // first

    // second

    let x = a;

    x
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F)

-> F {
    a
}",
            "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
proto Foo<G: Group, F: Scalar<G>>(
    witness a: F,
    instance b: F,
)

where

    // first

    // second

    a == b
{

    let x = a;

    x

}",
            "\
proto Foo<G: Group, F: Scalar<G>>(witness a: F, instance b: F) where
    // first

    // second

    a == b
{
    let x = a;

    x
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn short_pairing_stays_on_one_line() {
    assert_ok(
        "\
proto p<G1: Group, G2: Group, GT: Pairing<G1, G2>>(instance a: G1) where a == a { a }",
        "\
proto p<G1: Group, G2: Group, GT: Pairing<G1, G2>>(instance a: G1) where a == a {
    a
}
",
    );
}

#[test]
fn poly_type_sugar() {
    // Poly<F, 1, N> → Uni<F, N>; Poly<F, N, 1> → Mle<F, N>;
    // Poly<F, M, N> with M != 1 and N != 1 stays as Poly.
    for (src, expected) in [
        (
            "\
fn f<F: Field, N: Size>(instance a: Poly<F, 1, N>) -> F { a }",
            "\
fn f<F: Field, N: Size>(instance a: Uni<F, N>) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field, N: Size>(instance a: Poly<F, N, 1>) -> F { a }",
            "\
fn f<F: Field, N: Size>(instance a: Mle<F, N>) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field, M: Size, N: Size>(instance a: Poly<F, M, N>) -> F { a }",
            "\
fn f<F: Field, M: Size, N: Size>(instance a: Poly<F, M, N>) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn poly_with_comments_not_sugared() {
    // Comments on the skipped arg → fall back to Poly to preserve them
    assert_ok(
        "type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;",
        "\
type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;
",
    );
}

#[test]
fn proto_signature_comments() {
    // Comments between the last where-relation and `{` must be indented
    // to match the where body, not left at column 0. A blank line between
    // the last relation and a comment before `{` should be preserved. A
    // comment between `)` and `where` should go on its own line, and
    // `where` should follow on the next line without a leading space.
    for (src, expected) in [
        (
            "\
proto p<F: Field>(instance a: F) where a == a
// trailing comment
{ a }",
            "\
proto p<F: Field>(instance a: F) where
    a == a
    // trailing comment
{
    a
}
",
        ),
        (
            "\
proto p<F: Field>(instance a: F) where a == a

// trailing comment
{ a }",
            "\
proto p<F: Field>(instance a: F) where
    a == a

    // trailing comment
{
    a
}
",
        ),
        (
            "\
proto p<F: Field>(instance a: F) // comment before where
where a == a { a }",
            "\
proto p<F: Field>(instance a: F)
// comment before where
where a == a {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn inline_line_comment_before_token_gets_space() {
    // An inline `//` comment before a token must get a space, not glue
    // to the preceding token.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) // inline comment
-> F { a }",
        "\
fn f<F: Field>(
    instance a: F,
) // inline comment
-> F {
    a
}
",
    );
}

#[test]
fn inline_line_comment_between_decls_no_leading_space() {
    // A trailing `//` comment after `}` sticks to `}`, and a blank line
    // is guaranteed between the comment and the next decl.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a } // trailing
fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
} // trailing

fn g<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn inline_block_comment_before_token_gets_space() {
    // An inline `/* */` comment before a token must get a space.
    assert_ok(
        "fn f<F: Field>(instance a: F) /* inline block */ -> F { a }",
        "\
fn f<F: Field>(instance a: F) /* inline block */ -> F {
    a
}
",
    );
}

#[test]
fn line_comment_before_operator_forces_break() {
    // A line comment before a binary operator must force a line break
    // — the operator goes on the next line, not glued to the comment.
    // A line comment before `==` in an assertion or where clause must
    // force a break.
    for (src, expected) in [
        (
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a // comment
    + b
}",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a // comment
        + b
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F) -> F {
    verify(a // comment
    == a)
}",
            "\
fn f<F: Field>(instance a: F) -> F {
    verify(
        a // comment
            == a,
    )
}
",
        ),
        (
            "\
proto p<F: Field>(instance a: F) where a // comment
== a { a }",
            "\
proto p<F: Field>(instance a: F) where
    a // comment
        == a
{
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn inline_block_comment_before_binop_stays_flat() {
    // An inline block comment before a binary operator stays flat
    // — `line()` provides the space, no forced break.
    assert_ok(
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* c */ + b
}",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* c */ + b
}
",
    );
}

#[test]
fn inline_block_comment_before_eqeq_in_assert_stays_flat() {
    // An inline block comment before `==` stays flat.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(a /* c */ == a)
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(a /* c */ == a)
}
",
    );
}
