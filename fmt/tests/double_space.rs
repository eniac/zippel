//! Comprehensive comment-placement and double-space regression tests.
//!
//! Tests every position where a comment can appear, using both
//! block comments (`/* c */`) and inline comments (`// c`).
//! Verifies no double spaces, correct single spaces, and idempotency.
//!
//! Also includes regression tests for double-space bugs caused by
//! embedded spaces in literals stacking with gap auto-open spaces,
//! and blank-line stripping/preservation around intra-expression tokens.

mod common;

use common::assert_ok;

// ══════════════════════════════════════════════════════════════════
// Section A: Comments around type-variable bounds `<F: Field>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_typevar_bounds() {
    for (src, expected) in [
        (
            "fn f /* c */ <F: Field>(instance a: F) -> F { a }",
            "\
fn f /* c */ <F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f< /* c */ F: Field>(instance a: F) -> F { a }",
            "\
fn f</* c */ F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F /* c */ : Field>(instance a: F) -> F { a }",
            "\
fn f<F /* c */ : Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: /* c */ Field>(instance a: F) -> F { a }",
            "\
fn f<F: /* c */ Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field /* c */ , G: Group>(instance a: F) -> F { a }",
            "\
fn f<F: Field /* c */, G: Group>(instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field, /* c */ G: Group>(instance a: F) -> F { a }",
            "\
fn f<F: Field, /* c */ G: Group>(instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field /* c */ >(instance a: F) -> F { a }",
            "\
fn f<F: Field /* c */>(instance a: F) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section B: Comments around args `(instance a: F)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_args() {
    for (src, expected) in [
        (
            "fn f<F: Field> /* c */ (instance a: F) -> F { a }",
            "\
fn f<F: Field> /* c */ (instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>( /* c */ instance a: F) -> F { a }",
            "\
fn f<F: Field>(/* c */ instance a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance /* c */ uniform a: F) -> F { a }",
            "\
fn f<F: Field>(instance /* c */ uniform a: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a /* c */ : F) -> F { a }",
            "\
fn f<F: Field>(instance a /* c */ : F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: /* c */ F) -> F { a }",
            "\
fn f<F: Field>(instance a: /* c */ F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F /* c */ , instance b: F) -> F { a }",
            "\
fn f<F: Field>(instance a: F /* c */, instance b: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, /* c */ instance b: F) -> F { a }",
            "\
fn f<F: Field>(instance a: F, /* c */ instance b: F) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F /* c */ ) -> F { a }",
            "\
fn f<F: Field>(instance a: F /* c */) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section C: Comments around return type `-> F`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_arrow_and_ret_type() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> /* c */ F { a }",
        "\
fn f<F: Field>(instance a: F) -> /* c */ F {
    a
}
",
    );
}

#[test]
fn comment_after_ret_type_before_brace() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F /* c */ { a }",
        "\
fn f<F: Field>(instance a: F) -> F /* c */ {
    a
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section D: Comments around type alias `type T = F;`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_type_alias() {
    for (src, expected) in [
        (
            "type T /* c */ = F;",
            "\
type T /* c */ = F;
",
        ),
        (
            "type T = /* c */ F;",
            "\
type T = /* c */ F;
",
        ),
        (
            "type T = F /* c */ ;",
            "\
type T = F /* c */ ;
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section E: Comments around let in body
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_let_in_body() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { let x /* c */ = a; x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    let x /* c */ = a;
    x
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { let x = /* c */ a; x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    let x = /* c */ a;
    x
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { let x = a /* c */ ; x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    let x = a /* c */;
    x
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { let x = a; /* c */ x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    let x = a; /* c */
    x
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn let_no_double_semicolon() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { let x = a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    x
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section F: Comments around log `<-`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_log_name_and_larrow() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { x /* c */ <- a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    x /* c */ <- a;
    x
}
",
    );
}

#[test]
fn comment_between_larrow_and_value_in_log() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { x <- /* c */ a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    x <- /* c */ a;
    x
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section G: Comments around function application `f(a, b)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_function_application() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { g /* c */ (a, b) }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    g /* c */ (a, b)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { g( /* c */ a, b) }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    g(/* c */ a, b)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { g(a /* c */ , b) }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    g(a /* c */, b)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { g(a, /* c */ b) }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    g(a, /* c */ b)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { g(a, b /* c */) }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    g(a, b /* c */)
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section H: Comments around vec literal `[a, b]`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_vec_literal() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { [ /* c */ a, b] }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    [/* c */ a, b]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { [a /* c */ , b] }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    [a /* c */, b]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { [a, /* c */ b] }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    [a, /* c */ b]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F) -> F { [a, b /* c */] }",
            "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    [a, b /* c */]
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section I: Comments around comprehension `[expr for x in range]`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_comprehension() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { [ /* c */ a for x in 0..1] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [/* c */ a for x in 0..1]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { [a /* c */ for x in 0..1] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a /* c */ for x in 0..1]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { [a for /* c */ x in 0..1] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a for /* c */ x in 0..1]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { [a for x /* c */ in 0..1] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a for x /* c */ in 0..1]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { [a for x in /* c */ 0..1] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a for x in /* c */ 0..1]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { [a for x in 0..1 /* c */] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a for x in 0..1 /* c */ ]
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section J: Comments around fun `fun x => body`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_fun() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { (fun(x /* c */) => x + a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    fun (x /* c */) => x + a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { (fun(x) => /* c */ x + a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    fun (x) => /* c */ x + a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { (fun(x /* c */ , y) => x + a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    fun (x /* c */, y) => x + a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section K: Comments around range `a..b` and `a, c..b`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_before_dotdot_in_range() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { [a for x in 0 /* c */ .. 1] }",
        "\
fn f<F: Field>(instance a: F) -> F {
    [a for x in 0 /* c */ ..1]
}
",
    );
}

#[test]
fn comment_after_dotdot_in_range() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { [a for x in 0.. /* c */ 1] }",
        "\
fn f<F: Field>(instance a: F) -> F {
    [a for x in 0.. /* c */ 1]
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section L: Comments around projection `base.field`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_base_and_dot_in_proj() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { a /* c */ .field }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a /* c */ .field
}
",
    );
}

#[test]
fn comment_between_dot_and_field_in_proj() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { a. /* c */ field }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a. /* c */ field
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section M: Comments around indexing `base[index]`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_indexing() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { a /* c */ [0] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a /* c */ [0]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { a[ /* c */ 0] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a[/* c */ 0]
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { a[0 /* c */] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a[0 /* c */]
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section N: Comments around unary calls `poly(x)`, `interpolate(a, b)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_poly_unary() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { poly /* c */ (a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    poly /* c */ (a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { poly( /* c */ a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    poly(/* c */ a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { poly(a /* c */) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    poly(a /* c */)
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section O: Comments around reduce `reduce(+, expr)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_reduce() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { reduce /* c */ (+, a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    reduce /* c */ (+, a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { reduce( /* c */ +, a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    reduce(/* c */ +, a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { reduce(+ /* c */ , a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    reduce(+ /* c */, a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { reduce(+, /* c */ a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    reduce(+, /* c */ a)
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section P: Comments around random/challenge `random<F>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_random() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { x <- random /* c */ <F>; x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    x <- random /* c */ <F>;
    x
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { x <- random< /* c */ F>; x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    x <- random</* c */ F>;
    x
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { x <- random<F /* c */>; x }",
            "\
fn f<F: Field>(instance a: F) -> F {
    x <- random<F /* c */>;
    x
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section Q: Comments around eval `eval<range>(poly)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_eval() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { eval /* c */ <0..1>(a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    eval /* c */ (a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { eval< /* c */ 0..1>(a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    eval /* c */ (a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { eval<0..1 /* c */>(a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    eval /* c */ (a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { eval<0..1> /* c */ (a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    eval /* c */ (a)
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section R: Comments around vec type `[F; N]`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_vec_type() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: [ /* c */ F; 2]) -> F { a[0] }",
            "\
fn f<F: Field>(instance a: [/* c */ F; 2]) -> F {
    a[0]
}
",
        ),
        (
            "fn f<F: Field>(instance a: [F /* c */ ; 2]) -> F { a[0] }",
            "\
fn f<F: Field>(instance a: [F /* c */; 2]) -> F {
    a[0]
}
",
        ),
        (
            "fn f<F: Field>(instance a: [F; /* c */ 2]) -> F { a[0] }",
            "\
fn f<F: Field>(instance a: [F; /* c */ 2]) -> F {
    a[0]
}
",
        ),
        (
            "fn f<F: Field>(instance a: [F; 2 /* c */ ]) -> F { a[0] }",
            "\
fn f<F: Field>(instance a: [F; 2 /* c */]) -> F {
    a[0]
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section S: Comments around Poly/Uni/Mle types `Poly<F, 1, N>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_poly_uni_mle_types() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: Poly /* c */ <F, 1, 2>) -> F { a }",
            "\
fn f<F: Field>(instance a: Uni /* c */ <F, 2>) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: Poly< /* c */ F, 1, 2>) -> F { a }",
            "\
fn f<F: Field>(instance a: Uni</* c */ F, 2>) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: Poly<F /* c */ , 1, 2>) -> F { a }",
            "\
fn f<F: Field>(instance a: Uni<F /* c */, 2>) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: Poly<F, /* c */ 1, 2>) -> F { a }",
            "\
fn f<F: Field>(instance a: Poly<F, /* c */ 1, 2>) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: Poly<F, 1, 2 /* c */ >) -> F { a }",
            "\
fn f<F: Field>(instance a: Uni<F, 2 /* c */>) -> F {
    a
}
",
        ),
        // Uni<F, /*A*/ N> must stay Uni, not become Poly<F, /*A*/ 1, N>.
        // The comment belongs to N, not to the implicit M=1.
        (
            "fn f<F: Field>(instance a: Uni<F, /*A*/ 2>) -> F { a }",
            "\
fn f<F: Field>(instance a: Uni<F, /*A*/ 2>) -> F {
    a
}
",
        ),
        // Mle<F, /*A*/ N> must stay Mle, not become Poly<F, N, /*A*/ 1>.
        (
            "fn f<F: Field>(instance a: Mle<F, /*A*/ 2>) -> F { a }",
            "\
fn f<F: Field>(instance a: Mle<F, /*A*/ 2>) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section T: Comments around Fin type `Fin<0..N>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_fin_type() {
    for (src, expected) in [
        (
            "fn f<N: 2>(instance a: Fin /* c */ <0..N>) -> F { a }",
            "\
fn f<N: 2>(instance a: Fin /* c */ <0..N>) -> F {
    a
}
",
        ),
        (
            "fn f<N: 2>(instance a: Fin< /* c */ 0..N>) -> F { a }",
            "\
fn f<N: 2>(instance a: Fin</* c */ 0..N>) -> F {
    a
}
",
        ),
        (
            "fn f<N: 2>(instance a: Fin<0..N /* c */ >) -> F { a }",
            "\
fn f<N: 2>(instance a: Fin<0..N /* c */>) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section U: Comments around Scalar kind `Scalar<G1, G2>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_scalar_kind() {
    for (src, expected) in [
        (
            "fn f<G: Scalar /* c */ <G1, G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Scalar /* c */ <G1, G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Scalar< /* c */ G1, G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Scalar</* c */ G1, G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Scalar<G1 /* c */ , G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Scalar<G1 /* c */, G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Scalar<G1, /* c */ G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Scalar<G1, /* c */ G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Scalar<G1, G2 /* c */ >>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Scalar<G1, G2 /* c */>>(instance a: G1) -> G1 {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section V: Comments around Pairing kind `Pairing<G1, G2>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_pairing_kind() {
    for (src, expected) in [
        (
            "fn f<G: Pairing /* c */ <G1, G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Pairing /* c */ <G1, G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Pairing< /* c */ G1, G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Pairing</* c */ G1, G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Pairing<G1 /* c */ , G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Pairing<G1 /* c */, G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
        (
            "fn f<G: Pairing<G1, /* c */ G2>>(instance a: G1) -> G1 { a }",
            "\
fn f<G: Pairing<G1, /* c */ G2>>(instance a: G1) -> G1 {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section W: Comments around record type `{ field: T }`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_record_type() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: { /* c */ x: F }) -> F { a.x }",
            "\
fn f<F: Field>(instance a: {/* c */ x: F}) -> F {
    a.x
}
",
        ),
        (
            "fn f<F: Field>(instance a: { x /* c */ : F }) -> F { a.x }",
            "\
fn f<F: Field>(instance a: {x /* c */ : F}) -> F {
    a.x
}
",
        ),
        (
            "fn f<F: Field>(instance a: { x: /* c */ F }) -> F { a.x }",
            "\
fn f<F: Field>(instance a: {x: /* c */ F}) -> F {
    a.x
}
",
        ),
        (
            "fn f<F: Field>(instance a: { x: F /* c */ }) -> F { a.x }",
            "\
fn f<F: Field>(instance a: {x: F /* c */}) -> F {
    a.x
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section X: Comments around record literal `{| field: val |}`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_record_literal() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { {| /* c */ x: a |} }",
            "\
fn f<F: Field>(instance a: F) -> F {
    {|/* c */ x: a|}
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { {| x /* c */ : a |} }",
            "\
fn f<F: Field>(instance a: F) -> F {
    {|x /* c */ : a|}
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { {| x: /* c */ a |} }",
            "\
fn f<F: Field>(instance a: F) -> F {
    {|x: /* c */ a|}
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { {| x: a /* c */ |} }",
            "\
fn f<F: Field>(instance a: F) -> F {
    {|x: a /* c */|}
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section Y: Comments around set_record `base.set(field, value)`
// ══════════════════════════════════════════════════════════════════

// NOTE: comment_between_base_and_dot_in_set_record, comment_between_dot_and_set_in_set_record,
// and comment_between_set_and_open_paren removed — parser doesn't support
// comments in those positions within set-record expressions.

// ══════════════════════════════════════════════════════════════════
// Section Z: Comments around assert/verify `assert(a == b)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_assert() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { assert /* c */ (a == a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    assert /* c */ (a == a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { assert( /* c */ a == a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    assert(/* c */ a == a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { assert(a /* c */ == a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    assert(a /* c */ == a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { assert(a == /* c */ a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    assert(a == /* c */ a)
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { assert(a == a /* c */) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    assert(a == a /* c */)
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section AA: Comments around where clause in proto
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_where_clause() {
    for (src, expected) in [
        (
            "proto p<F: Field>(instance a: F) /* c */ where a == a { a }",
            "\
proto p<F: Field>(instance a: F)
/* c */
where a == a {
    a
}
",
        ),
        // Already tested in where_clause_inline_comment_before_relation
        (
            "proto p<F: Field>(instance a: F) where /* c */ a == a { a }",
            "\
proto p<F: Field>(instance a: F) where /* c */ a == a {
    a
}
",
        ),
        (
            "proto p<F: Field>(instance a: F) where a == a /* c */ { a }",
            "\
proto p<F: Field>(instance a: F) where a == a /* c */ {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section AB: Comments around body braces `{ ... }`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_body_braces() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F) -> F { /* c */ a }",
            "\
fn f<F: Field>(instance a: F) -> F {
    /* c */
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F) -> F { a /* c */ }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a /* c */
}
",
        ),
        (
            "proto p<F: Field>(instance a: F) where a == a { /* c */ a }",
            "\
proto p<F: Field>(instance a: F) where a == a {
    /* c */
    a
}
",
        ),
        (
            "proto p<F: Field>(instance a: F) where a == a { a /* c */ }",
            "\
proto p<F: Field>(instance a: F) where a == a {
    a /* c */
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section AC: Comments around negation `-a`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_minus_and_operand() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { - /* c */ a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    - /* c */ a
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AD: Comments around size binary ops `M + 1`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comments_around_size_binops() {
    for (src, expected) in [
        (
            "fn f<M: 2>(instance a: [F; M /* c */ + 1]) -> F { a[0] }",
            "\
fn f<M: 2>(instance a: [F; M /* c */ + 1]) -> F {
    a[0]
}
",
        ),
        (
            "fn f<M: 2>(instance a: [F; M + /* c */ 1]) -> F { a[0] }",
            "\
fn f<M: 2>(instance a: [F; M + /* c */ 1]) -> F {
    a[0]
}
",
        ),
        (
            "fn f<M: 2>(instance a: [F; 2 /* c */ ^ M]) -> F { a[0] }",
            "\
fn f<M: 2>(instance a: [F; 2 /* c */ ^ M]) -> F {
    a[0]
}
",
        ),
        (
            "fn f<M: 2>(instance a: [F; 2 ^ /* c */ M]) -> F { a[0] }",
            "\
fn f<M: 2>(instance a: [F; 2 ^ /* c */ M]) -> F {
    a[0]
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section AE: Comments around max/min `max(a, b)` in size
// ══════════════════════════════════════════════════════════════════

// NOTE: max/min size tests removed — parser doesn't support max(a, b)
// syntax in size expressions.

// ══════════════════════════════════════════════════════════════════
// Section AF: Comments around interpolate `interpolate(points, evals)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_interpolate_keyword_and_paren() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { interpolate /* c */ (a, b) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    interpolate /* c */ (a, b)
}
",
    );
}

#[test]
fn comment_between_args_in_interpolate_comma() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { interpolate(a /* c */ , b) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    interpolate(a /* c */, b)
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AG: Comments around pair `pair(a, b)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_pair_keyword_and_paren() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { pair /* c */ (a, b) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    pair /* c */ (a, b)
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AH: Comments around dot `dot(a, b)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_dot_keyword_and_paren() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { dot /* c */ (a, b) }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    dot /* c */ (a, b)
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AI: Comments between declarations
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_two_fns() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { a } /* c */ fn g<F: Field>(instance a: F) -> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
} /* c */

fn g<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn comment_between_fn_and_type() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { a } /* c */ type T = F;",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
} /* c */

type T = F;
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AJ: Comments around Unit type and unit literal
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_before_unit_type_keyword() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> /* c */ Unit { a }",
        "\
fn f<F: Field>(instance a: F) -> /* c */ Unit {
    a
}
",
    );
}

#[test]
fn comment_between_parens_in_unit_literal() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> Unit { ( /* c */ ) }",
        "\
fn f<F: Field>(instance a: F) -> Unit {
    ( /* c */)
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AK: Multiple comments in the same gap
// ══════════════════════════════════════════════════════════════════

#[test]
fn two_block_comments_in_same_gap() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { a /* c1 */ /* c2 */ }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a /* c1 */ /* c2 */
}
",
    );
}

#[test]
fn block_comment_then_inline_comment_in_same_gap() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a /* c */ // d
 }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a /* c */ // d
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AL: Comments around challenge `challenge<F>`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_challenge_keyword_and_open_angle() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { x <- challenge /* c */ <F>; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    x <- challenge /* c */ <F>;
    x
}
",
    );
}

#[test]
fn comment_after_open_angle_in_challenge() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { x <- challenge< /* c */ F>; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    x <- challenge</* c */ F>;
    x
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AM: Comments around coef/mle `coef(x)`, `mle(x)`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_coef_keyword_and_paren() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { coef /* c */ (a) }",
        "\
fn f<F: Field>(instance a: F) -> F {
    coef /* c */ (a)
}
",
    );
}

#[test]
fn comment_between_mle_keyword_and_paren() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { mle /* c */ (a) }",
        "\
fn f<F: Field>(instance a: F) -> F {
    mle /* c */ (a)
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AN: Comments around concat `a ++ b`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_before_concat_op() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { a /* c */ ++ b }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* c */ ++ b
}
",
    );
}

#[test]
fn comment_after_concat_op() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { a ++ /* c */ b }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a ++ /* c */ b
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AO: Comments around modulo `a % b`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_before_mod_op() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { a /* c */ % b }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a /* c */ % b
}
",
    );
}

#[test]
fn comment_after_mod_op() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { a % /* c */ b }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a % /* c */ b
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AP: Comments around uniform* `uniform* a: F`
// ══════════════════════════════════════════════════════════════════

#[test]
fn comment_between_uniform_and_star() {
    assert_ok(
        "fn f<F: Field>(uniform /* c */ * a: F) -> F { a }",
        "\
fn f<F: Field>(uniform /* c */ * a: F) -> F {
    a
}
",
    );
}

#[test]
fn comment_between_star_and_name_in_uniform_star() {
    assert_ok(
        "fn f<F: Field>(uniform * /* c */ a: F) -> F { a }",
        "\
fn f<F: Field>(uniform * /* c */ a: F) -> F {
    a
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AQ: Double-space regression tests (from double_space.rs)
//
// When a literal contains an embedded space (e.g. `"fn "`, `" ->"`,
// `"; "`, `" + "`) and an inline comment appears in the gap adjacent
// to that space, the gap's auto-open (a space for inline comments)
// stacks with the literal's embedded space, producing a double space.
//
// Also includes blank-line stripping tests around intra-expression
// tokens and blank-line preservation tests around comments and decls.
// ══════════════════════════════════════════════════════════════════

// ──────────────────────────────────────────────────────────────────
// Category 1: Trailing space in keyword literal
// ──────────────────────────────────────────────────────────────────

#[test]
fn fn_keyword_inline_comment() {
    assert_ok(
        "fn /* c */ f<F: Field>(instance a: F) -> F { a }",
        "\
fn /* c */ f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn type_keyword_inline_comment() {
    assert_ok(
        "type /* c */ Foo = Unit;",
        "\
type /* c */ Foo = Unit;
",
    );
}

#[test]
fn let_keyword_inline_comment_in_body() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { let /* c */ x = a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let /* c */ x = a;
    x
}
",
    );
}

#[test]
fn for_keyword_inline_comment_in_comprehension() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { [a for /* c */ i in 0..N] }",
        "\
fn f<F: Field>(instance a: F) -> F {
    [a for /* c */ i in 0..N]
}
",
    );
}

#[test]
fn fun_keyword_inline_comment() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { (fun /* c */ (x) => x + a) }",
        "\
fn f<F: Field>(instance a: F) -> F {
    fun /* c */ (x) => x + a
}
",
    );
}

#[test]
fn proto_keyword_inline_comment() {
    assert_ok(
        "proto /* c */ p<F: Field>(instance a: F) where a == a { a }",
        "\
proto /* c */ p<F: Field>(instance a: F) where a == a {
    a
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Category 2: Trailing space in separator literal
// ──────────────────────────────────────────────────────────────────

#[test]
fn semicolon_space_inline_comment_in_vec_type() {
    assert_ok(
        "fn f<F: Field>(instance a: [F; /* c */ 2]) -> F { a }",
        "\
fn f<F: Field>(instance a: [F; /* c */ 2]) -> F {
    a
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Category 3: Trailing space in binop literal
// ──────────────────────────────────────────────────────────────────

#[test]
fn binop_inline_comment_flat() {
    assert_ok(
        "fn f<F: Field>(instance a: F, instance b: F) -> F { a + /* c */ b }",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a + /* c */ b
}
",
    );
}

#[test]
fn size_binop_inline_comment() {
    assert_ok(
        "fn f<M: 2>(instance a: [F; M + /* c */ 1]) -> F { a[0] }",
        "\
fn f<M: 2>(instance a: [F; M + /* c */ 1]) -> F {
    a[0]
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Category 4: Literal space between tokens
// ──────────────────────────────────────────────────────────────────

#[test]
fn arg_qualifier_to_name_inline_comment() {
    assert_ok(
        "fn f<F: Field>(instance /* c */ a: F) -> F { a }",
        "\
fn f<F: Field>(instance /* c */ a: F) -> F {
    a
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Category 5: line() + gap open
// ──────────────────────────────────────────────────────────────────

#[test]
fn where_clause_inline_comment_before_relation() {
    assert_ok(
        "proto p<F: Field>(instance a: F) where /* c */ a == a { a }",
        "\
proto p<F: Field>(instance a: F) where /* c */ a == a {
    a
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Category 6: Missing space after inline comment
// (gap_none with sep=nil doesn't provide space after non-breaking
// comment, so the next token glues to the comment)
// ──────────────────────────────────────────────────────────────────

#[test]
fn uniform_to_star_inline_comment_missing_space() {
    assert_ok(
        "fn f<F: Field>(uniform /* c */ * a: F) -> F { a }",
        "\
fn f<F: Field>(uniform /* c */ * a: F) -> F {
    a
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Sanity checks: these cases should NOT have double-space bugs
// (leading space in literal + gap_none before = no overlap)
// ──────────────────────────────────────────────────────────────────

#[test]
fn arrow_inline_comment_no_double_space() {
    // " ->" has leading space; gap before it uses gap_none (sep=nil),
    // so end=nil for non-breaking comments. No double space.
    assert_ok(
        "fn f<F: Field>(instance a: F) /* c */ -> F { a }",
        "\
fn f<F: Field>(instance a: F) /* c */ -> F {
    a
}
",
    );
}

#[test]
fn eq_inline_comment_no_double_space() {
    // " =" has leading space; gap before it uses gap_none (sep=nil).
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { let x /* c */ = a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x /* c */ = a;
    x
}
",
    );
}

#[test]
fn larrow_inline_comment_no_double_space() {
    // " <-" has leading space; gap before it uses gap_none (sep=nil).
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { x /* c */ <- a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    x /* c */ <- a;
    x
}
",
    );
}

#[test]
fn assert_eq_inline_comment_no_double_space() {
    // " ==" has leading space; gap before it uses gap_none (sep=nil).
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { verify(a /* c */ == a) }",
        "\
fn f<F: Field>(instance a: F) -> F {
    verify(a /* c */ == a)
}
",
    );
}

// ──────────────────────────────────────────────────────────────────
// Category 7: Blank lines around tokens (no comment)
//
// Blank lines around intra-expression tokens like `=`, `->`, `==`
// are noise and should be stripped. Blank lines around comments
// are preserved. Blank lines between declarations are preserved.
// ──────────────────────────────────────────────────────────────────

#[test]
fn blank_lines_around_eq_in_let() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { let x

= a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    x
}
",
    );
}

#[test]
fn blank_lines_around_eq_in_type_decl() {
    assert_ok(
        "\
type T

= F;",
        "\
type T = F;
",
    );
}

#[test]
fn blank_lines_around_arrow_in_fn() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F)

-> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn blank_lines_around_eqeq_in_assert() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { assert(a

== a) }",
        "\
fn f<F: Field>(instance a: F) -> F {
    assert(a == a)
}
",
    );
}

#[test]
fn blank_lines_around_arrow_in_log() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { x

<- a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    x <- a;
    x
}
",
    );
}

#[test]
fn blank_lines_preserved_with_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { let x

/* c */
= a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x

    /* c */
    = a;
    x
}
",
    );
}

#[test]
fn blank_lines_preserved_between_decls() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { a }


fn g<F: Field>(instance b: F) -> F { b }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}

fn g<F: Field>(instance b: F) -> F {
    b
}
",
    );
}

#[test]
fn blank_lines_no_space_before_brace() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F

{ a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AR: Blank-line stripping in delimited lists
//
// Blank lines after the open delimiter and before the close delimiter
// are noise (structural positions) and should be stripped, matching
// rustfmt behavior. Comments are preserved.
// ══════════════════════════════════════════════════════════════════

#[test]
fn blank_line_stripping_in_delimited_lists() {
    for (src, expected) in [
        (
            "\
fn f<

F: Field>(instance a: F) -> F { a }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field

>(instance a: F) -> F { a }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field>(

instance a: F) -> F { a }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F

) -> F { a }",
            "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F) -> F { g(

a) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    g(a)
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F) -> F { g(a

) }",
            "\
fn f<F: Field>(instance a: F) -> F {
    g(a)
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F) -> F { [

a, b] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a, b]
}
",
        ),
        (
            "\
fn f<F: Field>(instance a: F) -> F { [a, b

] }",
            "\
fn f<F: Field>(instance a: F) -> F {
    [a, b]
}
",
        ),
        (
            "\
fn f<

F: Field, G: Group

>(instance a: F) -> F { a }",
            "\
fn f<F: Field, G: Group>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
fn f<

/* c */
F: Field>(instance a: F) -> F { a }",
            "\
fn f<
    /* c */
    F: Field,
>(instance a: F) -> F {
    a
}
",
        ),
        (
            "\
fn f<F: Field

/* c */
>(instance a: F) -> F { a }",
            "\
fn f<
    F: Field,

    /* c */
>(instance a: F) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

// ══════════════════════════════════════════════════════════════════
// Section AS: Blank-line stripping around structural tokens
//
// Blank lines around `->`, `;` (trailing), and `=` are noise in
// structural positions and should be stripped (when no comments).
// Blank lines between statements (after `;` with a body) are
// meaningful and preserved.
// ══════════════════════════════════════════════════════════════════

#[test]
fn blank_lines_around_arrow_in_fn_stripped() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F)

-> F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn blank_lines_after_arrow_before_ret_stripped() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) ->

F { a }",
        "\
fn f<F: Field>(instance a: F) -> F {
    a
}
",
    );
}

#[test]
fn blank_lines_before_trailing_semi_stripped() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { let x = a

; }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
}
",
    );
}

#[test]
fn blank_lines_around_eq_in_let_stripped() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { let x

=

a; x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;
    x
}
",
    );
}

#[test]
fn blank_lines_after_semi_with_body_preserved() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { let x = a;

x }",
        "\
fn f<F: Field>(instance a: F) -> F {
    let x = a;

    x
}
",
    );
}

// ══════════════════════════════════════════════════════════════════
// Section AU: Trailing comma with comments
//
// Comments around a trailing comma should not produce double spaces
// or extra spaces before the close delimiter. In broken mode, the
// close delimiter should go on its own line.
// ══════════════════════════════════════════════════════════════════

#[test]
fn trailing_comma_with_comments() {
    for (src, expected) in [
        (
            "fn f<F: Field>(instance a: F, instance b: F /* c */,) -> F { a }",
            "\
fn f<F: Field>(instance a: F, instance b: F /* c */) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F, /* c */) -> F { a }",
            "\
fn f<F: Field>(instance a: F, instance b: F /* c */) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance a: F, instance b: F /* before */, /* after */) -> F { a }",
            "\
fn f<F: Field>(instance a: F, instance b: F /* before */ /* after */) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaa: F, instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F /* c */,) -> F { a }",
            "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaa: F,
    instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F, /* c */
) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaa: F, instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F, /* c */) -> F { a }",
            "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaa: F,
    instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F, /* c */
) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaa: F, instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F /* before */, /* after */) -> F { a }",
            "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaa: F,
    instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F, /* before */ /* after */
) -> F {
    a
}
",
        ),
        (
            "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaa: F, instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F /* c */) -> F { a }",
            "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaa: F,
    instance bbbbbbbbbbbbbbbbbbbbbbbbbbb: F, /* c */
) -> F {
    a
}
",
        ),
    ] {
        assert_ok(src, expected);
    }
}

#[test]
fn empty_body() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F {}",
        "\
fn f<F: Field>(instance a: F) -> F {}
",
    );
}

#[test]
fn empty_body_no_return_type() {
    assert_ok(
        "fn f<F: Field>(instance a: F) {}",
        "\
fn f<F: Field>(instance a: F) {}
",
    );
}

#[test]
fn empty_body_with_block_comment() {
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { /* c */ }",
        "\
fn f<F: Field>(instance a: F) -> F { /* c */ }
",
    );
}

#[test]
fn empty_body_with_line_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { // c
}",
        "\
fn f<F: Field>(instance a: F) -> F {
    // c
}
",
    );
}

#[test]
fn empty_proto_body() {
    assert_ok(
        "proto p<F: Field>(instance a: F) where a == a {}",
        "\
proto p<F: Field>(instance a: F) where a == a {}
",
    );
}

#[test]
fn empty_proto_body_with_block_comment() {
    assert_ok(
        "proto p<F: Field>(instance a: F) where a == a { /* c */ }",
        "\
proto p<F: Field>(instance a: F) where a == a { /* c */ }
",
    );
}

#[test]
fn empty_proto_body_with_line_comment() {
    assert_ok(
        "\
proto p<F: Field>(instance a: F) where a == a { // c
}",
        "\
proto p<F: Field>(instance a: F) where a == a {
    // c
}
",
    );
}

#[test]
fn empty_body_trim_blank_lines_fn() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {

    // c

}",
        "\
fn f<F: Field>(instance a: F) -> F {
    // c
}
",
    );
}

#[test]
fn empty_body_trim_blank_lines_proto() {
    assert_ok(
        "\
proto p<F: Field>(instance a: F) where a == a {

    // c

}",
        "\
proto p<F: Field>(instance a: F) where a == a {
    // c
}
",
    );
}

#[test]
fn empty_body_trim_leading_blank_fn() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F {

    /* c */}",
        "\
fn f<F: Field>(instance a: F) -> F { /* c */ }
",
    );
}

#[test]
fn empty_body_trim_trailing_blank_fn() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F) -> F { /* c */

}",
        "\
fn f<F: Field>(instance a: F) -> F {
    /* c */
}
",
    );
}

#[test]
fn empty_body_trim_truly_inline_block_fn() {
    // Block comment glued to both braces — no line breaks in source.
    // Trim has no blank lines to remove, but verifies inline stays inline.
    assert_ok(
        "fn f<F: Field>(instance a: F) -> F { /* c */ }",
        "\
fn f<F: Field>(instance a: F) -> F { /* c */ }
",
    );
}

#[test]
fn empty_body_trim_blank_lines_block_proto() {
    // Block comment on its own line with surrounding blank lines in proto.
    assert_ok(
        "\
proto p<F: Field>(instance a: F) where a == a {

    /* c */

}",
        "\
proto p<F: Field>(instance a: F) where a == a {
    /* c */
}
",
    );
}

#[test]
fn trim_blank_lines_around_separator_no_comments() {
    assert_ok(
        "\
fn f<F: Field>(

    instance a: F,

    instance b: F,

) -> F {
    a
}",
        "\
fn f<F: Field>(instance a: F, instance b: F) -> F {
    a
}
",
    );
}

#[test]
fn trim_blank_lines_around_separator_with_comments() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F,

    // before b
    instance b: F) -> F {
    a
}",
        "\
fn f<F: Field>(
    instance a: F,

    // before b
    instance b: F,
) -> F {
    a
}
",
    );
}

#[test]
fn trim_blank_lines_before_separator_with_comment() {
    // Blank lines around a block comment make it multiline — the
    // formatter preserves the break. trim_if_clean only trims when
    // there are no comments.
    assert_ok(
        "\
fn f<F: Field>(instance a: F

    /* c */, instance b: F) -> F {
    a
}",
        "\
fn f<F: Field>(
    instance a: F,

    /* c */
    instance b: F,
) -> F {
    a
}
",
    )
}

#[test]
fn trim_blank_lines_after_separator_with_comment() {
    assert_ok(
        "\
fn f<F: Field>(instance a: F,

    /* c */ instance b: F) -> F {
    a
}",
        "\
fn f<F: Field>(
    instance a: F,

    /* c */
    instance b: F,
) -> F {
    a
}
",
    )
}

#[test]
fn trim_blank_lines_around_separator_inline_block_no_blank() {
    // Inline block comment with no blank lines stays inline.
    assert_ok(
        "\
fn f<F: Field>(instance a: F /* c */, instance b: F) -> F {
    a
}",
        "\
fn f<F: Field>(instance a: F /* c */, instance b: F) -> F {
    a
}
",
    )
}

#[test]
fn broken_sep_both_comments() {
    // Case 2: both before_sep and after_sep have comments.
    // Long enough to force broken mode.
    assert_ok(
        "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa: F /*A*/, /*B*/ instance b: F) -> F { a }",
        "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa: F, /*A*/
    /*B*/
    instance b: F,
) -> F {
    a
}
",
    );
}

#[test]
fn broken_sep_before_comment_only() {
    // Case 3: before_sep has comment, after_sep is empty.
    assert_ok(
        "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa: F /*A*/, instance b: F) -> F { a }",
        "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa: F, /*A*/
    instance b: F,
) -> F {
    a
}
",
    );
}

#[test]
fn broken_sep_after_comment_only() {
    // Case 4: before_sep is empty, after_sep has comment.
    assert_ok(
        "fn f<F: Field>(instance aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa: F, /*B*/ instance b: F) -> F { a }",
        "\
fn f<F: Field>(
    instance aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa: F,
    /*B*/
    instance b: F,
) -> F {
    a
}
",
    );
}
