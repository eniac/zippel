//! Expression formatting tests.
//!
//! Tests for expression layout: parenthesization, line breaking,
//! comprehensions, asserts, reduces, records, and ranges.

use fmt::format_source;

fn fmt(src: &str) -> String {
    format_source(src).expect("parse error")
}

fn assert_ok(src: &str, expected: &str) {
    let out = fmt(src);
    assert_eq!(out, expected, "first format mismatch");
    assert_eq!(fmt(&out), out, "not idempotent");
}

// ══════════════════════════════════════════════════════════════════
// Section: Parenthesization
// ══════════════════════════════════════════════════════════════════

#[test]
fn strips_redundant_expression_parens() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { ((a + b)) }",
        "fn f<F: Field>(instance a: F, instance b: F) -> F {\n    a + b\n}\n",
    );
}

#[test]
fn preserves_size_expression_precedence() {
    assert_ok(
        "fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] { x }",
        "fn f<M: Size, F: Field>(instance x: [F; (M - 1) / 2]) -> [F; (M - 1) / 2] {\n    x\n}\n",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Range
// ══════════════════════════════════════════════════════════════════

#[test]
fn range_concat_needs_paren() {
    // (0..3) ++ (0..2) must keep parens or it re-parses as 0..(3 ++ (0..2))
    assert_ok(
        "fn f<F: Field>(instance a: [F; 4]) -> F { (0..3) ++ (0..2) }",
        "fn f<F: Field>(instance a: [F; 4]) -> F {\n    (0..3) ++ (0..2)\n}\n",
    );
}

#[test]
fn range_add_needs_paren() {
    // (0..3) + (0..2) — vec + vec via Concat lowering
    assert_ok(
        "fn f<F: Field>(instance a: [F; 4]) -> F { (0..3) + (0..2) }",
        "fn f<F: Field>(instance a: [F; 4]) -> F {\n    (0..3) + (0..2)\n}\n",
    );
}

#[test]
fn range_mul_needs_paren() {
    // (0..3) * (0..2) — vec * vec
    assert_ok(
        "fn f<F: Field>(instance a: [F; 4]) -> F { (0..3) * (0..2) }",
        "fn f<F: Field>(instance a: [F; 4]) -> F {\n    (0..3) * (0..2)\n}\n",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Comprehension
// ══════════════════════════════════════════════════════════════════

#[test]
fn short_comprehension_stays_on_one_line() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F {\n    let x = [a for i in 0..N];\n    a\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    let x = [a for i in 0..N];\n    a\n}\n",
    );
}

#[test]
fn comprehension_in_long_assertion_stays_flat() {
    // The == breaks, but the short comprehension stays on one line.
    assert_ok(
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F)\nwhere gate_identity(a, b, c, d, e) == [a for i in 0..N]\n{ a }",
        "proto p<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) where\n    gate_identity(a, b, c, d, e) == [a for i in 0..N]\n{\n    a\n}\n",
    );
}

#[test]
fn long_comprehension_breaks_with_brackets_on_own_lines() {
    // When the comprehension doesn't fit, [ and ] get their own lines,
    // body on its own line, for-clause on its own line.
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {\n    let x = [some_very_long_function_name_here_that_is_super_duper_long(a, b, c, d, e) for i in 0..N];\n    a\n}",
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {\n    let x = [\n        some_very_long_function_name_here_that_is_super_duper_long(a, b, c, d, e)\n        for i in 0..N\n    ];\n    a\n}\n",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Assert
// ══════════════════════════════════════════════════════════════════

#[test]
fn short_assert_stays_on_one_line() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F {\n    assert(a == a);\n    a\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    assert(a == a);\n    a\n}\n",
    );
}

#[test]
fn long_assert_breaks_before_eq() {
    // The == inside assert(...) breaks, putting RHS on a new indented line.
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {\n    assert(gate_identity_function(a, b, c, d, e, a, b) == gate_identity_function2(a, b, c, d, e, a, b));\n    a\n}",
        "fn f<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F, instance e: F) -> F {\n    assert(\n        gate_identity_function(a, b, c, d, e, a, b) == gate_identity_function2(a, b, c, d, e, a, b),\n    );\n    a\n}\n",
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
        "proto p<F: Field>(instance a: F, instance b: F)\nwhere reduce(*, [a[i] + y * b[i] + x for i in 0..N]) * reduce(*, [a[i] + y * b[i] + x for i in 0..N]) == reduce(*, [b[i] + y * a[i] + x for i in 0..N]) * reduce(*, [b[i] + y * a[i] + x for i in 0..N])\n{ a }",
        "proto p<F: Field>(instance a: F, instance b: F) where\n    reduce(*, [a[i] + y * b[i] + x for i in 0..N]) * reduce(*, [a[i] + y * b[i] + x for i in 0..N])\n        == reduce(*, [b[i] + y * a[i] + x for i in 0..N])\n            * reduce(*, [b[i] + y * a[i] + x for i in 0..N])\n{\n    a\n}\n",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section: Reduce
// ══════════════════════════════════════════════════════════════════

#[test]
fn short_reduce_stays_on_one_line() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F {\n    let x = reduce(+, [a, a, a]);\n    a\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    let x = reduce(+, [a, a, a]);\n    a\n}\n",
    );
}

#[test]
fn long_reduce_breaks_args() {
    // reduce(+, [...]) breaks: each arg on its own line, comprehension
    // brackets get their own lines.
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F {\n    let x = reduce(+, [eval<0>(p_poly, tail) for tail in [[i / 2 ^ j % 2 * one for j in 0..S - 1] for i in 0..2 ^ (S - 1)]]);\n    a\n}",
        "fn f<F: Field>(instance a: F) -> F {\n    let x = reduce(\n        +,\n        [\n            eval<0>(p_poly, tail)\n            for tail in [[i / 2 ^ j % 2 * one for j in 0..S - 1] for i in 0..2 ^ (S - 1)]\n        ],\n    );\n    a\n}\n",
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
        "fn f<F: Field>(instance a: F) -> F {\n    {|zebra: a, apple: a, mango: a|}\n}\n",
    );
}

#[test]
fn record_type_preserves_source_order() {
    // Type fields also stored in Ctx but must output in source order.
    assert_ok(
        "type T = { zebra: F, apple: F, mango: F };",
        "type T = {zebra: F, apple: F, mango: F};\n",
    );
}

#[test]
fn record_literal_preserves_source_order_with_comment() {
    // Comment between fields must stay with the right field.
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { {| zebra: a, /* about apple */ apple: a |} }",
        "fn f<F: Field>(instance a: F) -> F {\n    {|zebra: a, /* about apple */ apple: a|}\n}\n",
    );
}
