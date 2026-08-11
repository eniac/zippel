//! Expression formatting tests.
//!
//! Tests for expression layout: parenthesization, line breaking,
//! comprehensions, asserts, reduces, records, and ranges.

mod common;

use common::assert_ok;

// ══════════════════════════════════════════════════════════════════
// Section: Parenthesization
// ══════════════════════════════════════════════════════════════════

#[test]
fn strips_redundant_expression_parens() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a + b)) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a + b
}
",
    );
}

#[test]
fn preserves_size_expression_precedence() {
    assert_ok(
        "fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] { x }",
        "\
fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] {
    x
}
",
    );
}

#[test]
fn pow_chain_right_assoc_no_paren() {
    // a ^ b ^ c parses as Pow(a, Pow(b, c)) (right-associative).
    // No parentheses needed — the text re-parses to the same AST.
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { a ^ b ^ c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    a ^ b ^ c
}
",
    );
}

#[test]
fn pow_left_grouped_keeps_parens() {
    // (a ^ b) ^ c parses as Pow(Pow(a, b), c) (left-grouped via parens).
    // Parentheses must be preserved — without them, `a ^ b ^ c` would
    // re-parse as Pow(a, Pow(b, c)) (right-associative).
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F { (a ^ b) ^ c }",
        "\
fn f<F: Field>(instance a: F, instance b: F, instance c: F) -> F {
    (a ^ b) ^ c
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Range
// ══════════════════════════════════════════════════════════════════

#[test]
fn range_concat_no_paren() {
    // 0..3 ++ 0..2 — Concat is not a size_ty operator, so the range
    // parser stops at ++ and the Bin applies correctly. No parens needed.
    assert_ok(
        "fn f<F: Field>(instance a: [F; 4]) -> F { (0..3) ++ (0..2) }",
        "\
fn f<F: Field>(instance a: [F; 4]) -> F {
    0..3 ++ 0..2
}
",
    );
}

#[test]
fn range_add_needs_paren() {
    // (0..3) + (0..2) — vec + vec via Concat lowering
    assert_ok(
        "fn f<F: Field>(instance a: [F; 4]) -> F { (0..3) + (0..2) }",
        "\
fn f<F: Field>(instance a: [F; 4]) -> F {
    (0..3) + (0..2)
}
",
    );
}

#[test]
fn range_mul_needs_paren() {
    // (0..3) * (0..2) — vec * vec
    assert_ok(
        "fn f<F: Field>(instance a: [F; 4]) -> F { (0..3) * (0..2) }",
        "\
fn f<F: Field>(instance a: [F; 4]) -> F {
    (0..3) * (0..2)
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Comprehension
// ══════════════════════════════════════════════════════════════════

#[test]
fn short_comprehension_stays_on_one_line() {
    assert_ok(
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
    assert_ok(
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
fn long_comprehension_breaks_with_brackets_on_own_lines() {
    // When the comprehension doesn't fit, [ and ] get their own lines,
    // body on its own line, for-clause on its own line.
    assert_ok(
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

// ══════════════════════════════════════════════════════════════════
// Section: Assert
// ══════════════════════════════════════════════════════════════════

#[test]
fn short_assert_stays_on_one_line() {
    assert_ok(
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
    assert_ok(
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

// ══════════════════════════════════════════════════════════════════
// Section: Assert in where clause
// ══════════════════════════════════════════════════════════════════

#[test]
fn long_assertion_breaks_before_eq() {
    // The == in the relation breaks, putting RHS on a new indented line.
    // The LHS fits on one line so stays flat; the RHS breaks with * aligned.
    assert_ok(
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

// ══════════════════════════════════════════════════════════════════
// Section: Reduce
// ══════════════════════════════════════════════════════════════════

#[test]
fn short_reduce_stays_on_one_line() {
    assert_ok(
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
    assert_ok(
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

// ══════════════════════════════════════════════════════════════════
// Section: Record
// ══════════════════════════════════════════════════════════════════

#[test]
fn record_literal_preserves_source_order() {
    // Fields stored in Ctx (OrdMap, key-sorted) but formatter must
    // output in source order: zebra, apple, mango.
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { {| zebra: a, apple: a, mango: a |} }",
        "\
fn f<F: Field>(instance a: F) -> F {
    {|zebra: a, apple: a, mango: a|}
}
",
    );
}

#[test]
fn record_type_preserves_source_order() {
    // Type fields also stored in Ctx but must output in source order.
    assert_ok(
        "type T = { zebra: F, apple: F, mango: F };",
        "\
type T = {zebra: F, apple: F, mango: F};
",
    );
}

#[test]
fn record_literal_preserves_source_order_with_comment() {
    // Comment between fields must stay with the right field.
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { {| zebra: a, /* about apple */ apple: a |} }",
        "\
fn f<F: Field>(instance a: F) -> F {
    {|zebra: a, /* about apple */ apple: a|}
}
",
    );
}

#[test]
fn binop_with_wide_function_call_no_double_nest() {
    // When both the binop chain and the function call args break,
    // the args should NOT be double-nested. The wide chain puts each
    // operator on a continuation line.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    gate_identity(aaaaaaaaaaaaa, bbbbbbbbbbbbb, ccccccccccccc, dddddddddddd, eeeeeeeeeeee, fffffffffffff) + 1 + 2 + 3
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    gate_identity(
        aaaaaaaaaaaaa,
        bbbbbbbbbbbbb,
        ccccccccccccc,
        dddddddddddd,
        eeeeeeeeeeee,
        fffffffffffff,
    )
        + 1
        + 2
        + 3
}
",
    );
}

#[test]
fn assertion_with_wide_function_call_no_double_nest() {
    // When both verify() and gate_identity() break, the args
    // should NOT be double-nested. `) == 1 + 2` stays on one line
    // because the `==` group independently fits.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(gate_identity(aaaaaaaaaaaaa, bbbbbbbbbbbbb, ccccccccccccc, dddddddddddd, eeeeeeeeeeee, fffffffffffff) == 1 + 2)
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(
        gate_identity(
            aaaaaaaaaaaaa,
            bbbbbbbbbbbbb,
            ccccccccccccc,
            dddddddddddd,
            eeeeeeeeeeee,
            fffffffffffff,
        ) == 1 + 2,
    )
}
",
    );
}

#[test]
fn long_binop_chain_breaks_every_operator() {
    assert_ok(
        "\
fn f<F: Field>(instance c1: F) -> F {
    let c1_prime = c1 + rho_inv * c2 + rho * c3 + gamma_pair_ipp + alpha_sq * log_vl + alpha_inv_sq * log_vr + alpha_inv_sq * log_vr;
    c1
}",
        "\
fn f<F: Field>(instance c1: F) -> F {
    let c1_prime = c1
        + rho_inv * c2
        + rho * c3
        + gamma_pair_ipp
        + alpha_sq * log_vl
        + alpha_inv_sq * log_vr
        + alpha_inv_sq * log_vr;
    c1
}
",
    );
}

#[test]
fn broken_binop_nests_rhs_call_args() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + dot(very_long_g_vec_w, [w[i * 2 ^ (M - 1 - (M - 1) / 2) + j] for j in 0..2 ^ (M - 1 - (M - 1) / 2)])
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
        + dot(
            very_long_g_vec_w,
            [w[i * 2 ^ (M - 1 - (M - 1) / 2) + j] for j in 0..2 ^ (M - 1 - (M - 1) / 2)],
        )
}
",
    );
}

#[test]
fn assertion_with_wide_call_and_comprehension_rhs() {
    assert_ok(
        "\
fn f<F: Field>(instance a_evs: F, instance b_evs: F, instance c_evs: F, instance q_l_evs: F, instance q_r_evs: F, instance q_o_evs: F, instance q_m_evs: F, instance q_c_evs: F) -> F {
    verify(gate_identity(a_evs, b_evs, c_evs, q_l_evs, q_r_evs, q_o_evs, q_m_evs, q_c_evs) == [zero_f for i in 0..N])
}",
        "\
fn f<F: Field>(
    instance a_evs: F,
    instance b_evs: F,
    instance c_evs: F,
    instance q_l_evs: F,
    instance q_r_evs: F,
    instance q_o_evs: F,
    instance q_m_evs: F,
    instance q_c_evs: F,
) -> F {
    verify(
        gate_identity(a_evs, b_evs, c_evs, q_l_evs, q_r_evs, q_o_evs, q_m_evs, q_c_evs)
            == [zero_f for i in 0..N],
    )
}
",
    );
}

#[test]
fn long_add_chain_with_long_mul_subchain() {
    // The outer + group breaks (chain too wide), and the inner *
    // group also breaks (mul chain too wide). The * operators nest
    // under their + operator, while sibling + operands stay aligned.
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {
    a + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb * cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc * dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd + e
}
",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
        + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
            * cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
            * dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
        + e
}
",
    );
}
