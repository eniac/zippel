//! Comment preservation tests.
//!
//! Verifies that comments are preserved in the correct positions after
//! formatting, and that formatting is idempotent (comments don't move
//! on the second pass).

use fmt::{Style, format_source, format_source_with_style};

fn fmt(src: &str) -> String {
    format_source(src).expect("parse error")
}

fn assert_formatted(src: &str, expected: &str) {
    let out = fmt(src);
    assert_eq!(out, expected);
    assert_eq!(fmt(&out), out, "not idempotent");
}

fn assert_formatted_with_style(src: &str, expected: &str, style: &Style) {
    let out = format_source_with_style(src, style).expect("parse error");
    assert_eq!(out, expected);
    assert_eq!(
        format_source_with_style(&out, style).unwrap(),
        out,
        "not idempotent"
    );
}

#[test]
fn file_leading_comment() {
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
fn comment_at_start_of_body() {
    assert_formatted(
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
fn no_comments_unchanged() {
    assert_formatted(
        "fn f<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn arg_trailing_comment() {
    assert_formatted(
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
    );
}

#[test]
fn arg_leading_comment() {
    assert_formatted(
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
    );
}

#[test]
fn arg_comment_with_pairing_type() {
    // Test that commas inside angle brackets (Pairing<G1, G2>) don't
    // confuse the arg boundary detection.
    assert_formatted(
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
    );
}

#[test]
fn arg_inline_block_comments() {
    assert_formatted(
        "fn f<F: Field>(instance /*comment A*/ a /*comment B*/ : /*comment C*/ F) -> F { a }",
        "\
fn f<F: Field>(instance /*comment A*/ a /*comment B*/ : /*comment C*/ F) -> F {
    a
}
",
    );
}

#[test]
fn exp_inline_comment_binop() {
    assert_formatted(
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* between */ + b
}",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* between */ + b
}
",
    );
}

#[test]
fn exp_inline_comment_app() {
    assert_formatted(
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
fn exp_inline_comment_let() {
    assert_formatted(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x /* bind */ = a /* val */;
    x
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x /* bind */ = a; /* val */
    x
}
",
    );
}

#[test]
fn exp_inline_comment_typ() {
    assert_formatted(
        "type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;",
        "type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;\n",
    );
}

#[test]
fn strips_redundant_expression_parens() {
    assert_formatted(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a + b)) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a + b
}
",
    );
}

#[test]
fn preserves_comments_near_necessary_parens() {
    assert_formatted(
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
    assert_formatted(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a /* inner */ + b)) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* inner */ + b
}
",
    );
}

#[test]
fn preserves_size_expression_precedence() {
    assert_formatted(
        "fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] { x }",
        "\
fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] {
    x
}
",
    );
}

#[test]
fn line_comment_after_arg() {
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a // note
    ;
    x
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; // note
    x
}
",
    );
}

#[test]
fn keeps_line_comments_after_commas() {
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted_with_style(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
    assert_formatted(
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
fn structural_positions_strip_blank_lines_fn() {
    // Leading blank lines after `{` and trailing blank lines before `}` are
    // stripped; body-level blank lines and inter-comment blank lines are
    // preserved.
    assert_formatted(
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
    );
}

#[test]
fn structural_positions_strip_blank_lines_fn_args() {
    // Blank line after `)` before `->` is stripped.
    assert_formatted(
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
    );
}

#[test]
fn structural_positions_strip_blank_lines_proto() {
    // Leading blank lines before `where`, after `where`, after `{`, and
    // trailing blank lines before `}` are stripped; body-level and
    // inter-comment blank lines are preserved.
    assert_formatted(
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
    );
}

#[test]
fn short_comprehension_stays_on_one_line() {
    assert_formatted(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = [a for i in 0..N];
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = [a for i in 0..N];
    a
}
",
    );
}

#[test]
fn comprehension_in_long_assertion_stays_flat() {
    // The == breaks, but the short comprehension stays on one line.
    assert_formatted(
        "\
proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F)
where gate_identity(a, b, c, d, e) == [a for i in 0..N]
{ a }",
        "\
proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) where
    gate_identity(a, b, c, d, e) == [a for i in 0..N]
{
    a
}
",
    );
}

#[test]
fn long_assertion_breaks_before_eq() {
    // The == in the relation breaks, putting RHS on a new indented line.
    // The LHS fits on one line so stays flat; the RHS breaks with * aligned.
    assert_formatted(
        "\
proto p<F: Field>(instance a: F, instance b: F)
where reduce(*, [a[i] + y * b[i] + x for i in 0..N]) * reduce(*, [a[i] + y * b[i] + x for i in 0..N]) == reduce(*, [b[i] + y * a[i] + x for i in 0..N]) * reduce(*, [b[i] + y * a[i] + x for i in 0..N])
{ a }",
        "\
proto p<F: Field>(instance a: F, instance b: F) where
    reduce(*, [a[i] + y * b[i] + x for i in 0..N]) * reduce(*, [a[i] + y * b[i] + x for i in 0..N])
        == reduce(*, [b[i] + y * a[i] + x for i in 0..N])
            * reduce(*, [b[i] + y * a[i] + x for i in 0..N])
{
    a
}
",
    );
}

#[test]
fn short_assert_stays_on_one_line() {
    assert_formatted(
        "\
fn f<F: Field>(instance a: F) -> F {
    assert(a == a);
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    assert(a == a);
    a
}
",
    );
}

#[test]
fn long_assert_breaks_before_eq() {
    // The == inside assert(...) breaks, putting RHS on a new indented line.
    assert_formatted(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {
    assert(gate_identity_function(a, b, c, d, e, a, b) == gate_identity_function2(a, b, c, d, e, a, b));
    a
}",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {
    assert(
        gate_identity_function(a, b, c, d, e, a, b) == gate_identity_function2(a, b, c, d, e, a, b),
    );
    a
}
",
    );
}

#[test]
fn short_reduce_stays_on_one_line() {
    assert_formatted(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = reduce(+, [a, a, a]);
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = reduce(+, [a, a, a]);
    a
}
",
    );
}

#[test]
fn long_reduce_breaks_args() {
    // reduce(+, [...]) breaks: each arg on its own line, comprehension
    // brackets get their own lines.
    assert_formatted(
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = reduce(+, [eval<0>(p_poly, tail) for tail in [[i / 2 ^ j % 2 * one for j in 0..S - 1] for i in 0..2 ^ (S - 1)]]);
    a
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = reduce(
        +,
        [
            eval<0>(p_poly, tail)
            for tail in [[i / 2 ^ j % 2 * one for j in 0..S - 1] for i in 0..2 ^ (S - 1)]
        ],
    );
    a
}
",
    );
}

#[test]
fn long_comprehension_breaks_with_brackets_on_own_lines() {
    // When the comprehension doesn't fit, [ and ] get their own lines,
    // body on its own line, for-clause on its own line.
    assert_formatted(
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {
    let x = [some_very_long_function_name_here_that_is_super_duper_long(a, b, c, d, e) for i in 0..N];
    a
}",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {
    let x = [
        some_very_long_function_name_here_that_is_super_duper_long(a, b, c, d, e)
        for i in 0..N
    ];
    a
}
",
    );
}

#[test]
fn short_pairing_stays_on_one_line() {
    assert_formatted(
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
fn poly_uni_sugar_emitted() {
    // Poly<F, 1, N> → Uni<F, N>
    assert_formatted(
        "\
fn f<F: Field, N: Size>(instance a: Poly<F, 1, N>) -> F { a }",
        "\
fn f<F: Field, N: Size>(instance a: Uni<F, N>) -> F {
    a
}
",
    );
}

#[test]
fn poly_mle_sugar_emitted() {
    // Poly<F, N, 1> → Mle<F, N>
    assert_formatted(
        "\
fn f<F: Field, N: Size>(instance a: Poly<F, N, 1>) -> F { a }",
        "\
fn f<F: Field, N: Size>(instance a: Mle<F, N>) -> F {
    a
}
",
    );
}

#[test]
fn poly_general_stays_poly() {
    // Poly<F, M, N> with M != 1 and N != 1 stays as Poly
    assert_formatted(
        "\
fn f<F: Field, M: Size, N: Size>(instance a: Poly<F, M, N>) -> F { a }",
        "\
fn f<F: Field, M: Size, N: Size>(instance a: Poly<F, M, N>) -> F {
    a
}
",
    );
}

#[test]
fn poly_with_comments_not_sugared() {
    // Comments on the skipped arg → fall back to Poly to preserve them
    assert_formatted(
        "type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;",
        "type T = Poly<F /* base */, 1 /* m */, 2 /* n */>;\n",
    );
}

#[test]
fn comment_before_brace_in_proto_is_indented() {
    // Comments between the last where-relation and `{` must be indented
    // to match the where body, not left at column 0.
    assert_formatted(
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
    );
}

#[test]
fn blank_line_before_comment_before_brace_preserved() {
    // A blank line between the last relation and a comment before `{`
    // should be preserved.
    assert_formatted(
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
    );
}

#[test]
fn comment_between_sig_and_where() {
    // A comment between `)` and `where` should go on its own line, and
    // `where` should follow on the next line without a leading space.
    assert_formatted(
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
    );
}

#[test]
fn inline_line_comment_before_token_gets_space() {
    // An inline `//` comment before a token must get a space, not glue
    // to the preceding token.
    assert_formatted(
        "fn f<F: Field>(instance a: F) // inline comment
-> F { a }",
        "\
fn f<F: Field>(instance a: F) // inline comment
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
    assert_formatted(
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
    assert_formatted(
        "fn f<F: Field>(instance a: F) /* inline block */ -> F { a }",
        "\
fn f<F: Field>(instance a: F) /* inline block */ -> F {
    a
}
",
    );
}
