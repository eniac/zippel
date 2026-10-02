//! Type error snapshot tests.
//!
//! Each test parses, concretizes, and type-checks a program via `CModule::typecheck`, renders
//! the resulting diagnostics, and compares them against insta snapshots in
//! `snapshots/typecheck/`.

mod common;

use common::assert_snap;
use lang::ast::module::UModule;
use lang::diagnostic::{Severity, render_diagnostic};
use lang::id::Tid;
use share::Ctx;

const SNAP_DIR: &str = "snapshots/typecheck";

/// Type-check `src` under `sizes` and render every diagnostic.
fn render_type_errors(src: &str, sizes: &[(&str, usize)]) -> String {
    let (module, diags) = UModule::parse(src);
    assert!(
        diags.iter().all(|d| d.severity == Severity::Warning),
        "expected no parse/semantic errors: {diags:?}"
    );
    let mut ctx = Ctx::new();
    for (name, value) in sizes {
        ctx.insert(&Tid::new(name), value);
    }
    let cmodule = module.unwrap().concretize(&ctx).unwrap();
    let diags = cmodule.typecheck();
    assert!(!diags.is_empty(), "expected a type error");
    diags
        .iter()
        .map(|d| render_diagnostic(d, "test.zippel", src))
        .collect::<Vec<_>>()
        .join("\n---\n")
}

#[test]
fn well_typed_module_has_no_type_errors() {
    let src = r"
proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = random<F>;
    u <- g * r;
    c <- challenge<F*>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
";
    let (module, _) = UModule::parse(src);
    let cmodule = module.unwrap().concretize(&Ctx::new()).unwrap();
    assert!(cmodule.typecheck().is_empty());
}

/// A body of higher degree than the declared return type is rejected.
#[test]
fn typecheck_return_of_higher_degree() {
    let src = r"
fn shrink<F: Field>(instance p: Uni<F, 5>) -> Uni<F, 3> {
    p
}
proto t<F: Field>(instance p: Uni<F, 5>, instance x: F) where x == x {
    let q = shrink(p);
    verify(q(x) == p(x))
}
";
    assert_snap!(
        SNAP_DIR,
        "return_of_higher_degree",
        render_type_errors(src, &[])
    );
}

/// Updating a record field with a value of higher degree than the field is rejected.
#[test]
fn typecheck_record_update_of_higher_degree() {
    let src = r"
proto t<F: Field>(instance p: Uni<F, 3>, instance q: Uni<F, 5>, instance x: F) where x == x {
    let r = {| c: p |};
    let s = r.set(c, q);
    let t = s.c;
    verify(t(x) == p(x))
}
";
    assert_snap!(
        SNAP_DIR,
        "record_update_of_higher_degree",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_binop_mismatch() {
    let src = r"
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    u <- g * x;
    verify(x + g == u)
}
";
    assert_snap!(SNAP_DIR, "binop_mismatch", render_type_errors(src, &[]));
}

#[test]
fn typecheck_nested_subexpression() {
    let src = r"
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let y = g * x;
    let z = ((y + x) * x) * x;
    verify(z == h)
}
";
    assert_snap!(
        SNAP_DIR,
        "nested_subexpression",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_long_operand_is_shortened() {
    let src = r"
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance v: [F; 4]) where g == g {
    verify(reduce(+, [v[i] * x + v[i] * x * x for i in 0..4]) + g == g)
}
";
    assert_snap!(SNAP_DIR, "long_operand", render_type_errors(src, &[]));
}

#[test]
fn typecheck_vector_elements_of_different_types() {
    let src = r"
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G) where g == g {
    let v = [x, g];
    verify(g == g)
}
";
    assert_snap!(SNAP_DIR, "vector_mixed_types", render_type_errors(src, &[]));
}

#[test]
fn typecheck_map_over_non_vector() {
    let src = r"
proto p<F: Field>(instance x: F) where x == x {
    let v = [y for y in x];
    verify(x == x)
}
";
    assert_snap!(
        SNAP_DIR,
        "map_over_non_vector",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_index_out_of_bounds() {
    let src = r"
proto p<F: Field>(instance a: [F; 2]) where a[0] == a[0] {
    verify(a[5] == a[0])
}
";
    assert_snap!(
        SNAP_DIR,
        "index_out_of_bounds",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_size_dependent_index() {
    // Well-typed at N = 2, ill-typed at N = 1.
    let src = r"
proto p<F: Field, N: Size>(instance a: [F; N]) where a[1] == a[1] {
    verify(a[1] == a[1])
}
";
    assert_snap!(
        SNAP_DIR,
        "size_dependent_index",
        render_type_errors(src, &[("N", 1)])
    );
}

#[test]
fn typecheck_unknown_function_suggests_similar_names() {
    let src = r"
fn double<F: Field>(instance a: F) -> F { a + a }
proto p<F: Field>(instance a: F) where a == a {
    verify(duble(a) == a)
}
";
    assert_snap!(SNAP_DIR, "unknown_function", render_type_errors(src, &[]));
}

#[test]
fn typecheck_call_with_wrong_argument_types() {
    let src = r"
fn f<G: Group, F: Scalar<G>>(instance x: F) -> F { x }
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G) where g == g {
    verify(f(g) == x)
}
";
    assert_snap!(
        SNAP_DIR,
        "call_wrong_argument_types",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_where_clause_mismatch() {
    let src = r"
proto p<G: Group, F: Scalar<G>>(witness x: F, instance h: G) where h == x {
    verify(h == h)
}
";
    assert_snap!(
        SNAP_DIR,
        "where_clause_mismatch",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_verify_non_boolean() {
    let src = r"
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G) where g == g {
    verify(g * x)
}
";
    assert_snap!(SNAP_DIR, "verify_non_boolean", render_type_errors(src, &[]));
}

#[test]
fn typecheck_protocol_body_ending_in_a_value() {
    let src = r"
proto p<F: Field>(instance a: F) where a == a {
    verify(a == a);
    a
}
";
    assert_snap!(
        SNAP_DIR,
        "protocol_body_ends_in_value",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_func_return_type() {
    let src = r"
fn f<G: Group, F: Scalar<G>>(instance g: G, instance x: F) -> F {
    g * x
}
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G) where g == g {
    verify(f(g, x) == x)
}
";
    assert_snap!(SNAP_DIR, "func_return_type", render_type_errors(src, &[]));
}

#[test]
fn typecheck_function_with_empty_body() {
    let src = r"
fn f<F: Field>(instance a: F) -> F { }
proto p<F: Field>(instance a: F) where a == a {
    verify(f(a) == a)
}
";
    assert_snap!(
        SNAP_DIR,
        "function_empty_body",
        render_type_errors(src, &[])
    );
}

#[test]
fn typecheck_error_in_every_instance_reported_once() {
    let src = r"
fn f<F: Field, G: Group, N: 1..4>(instance a: [F; N], instance g: G) -> F {
    a[0] + g
}
proto p<F: Field, G: Group>(instance a: [F; 3], instance g: G) where a[0] == a[0] {
    verify(f(a, g) == a[0])
}
";
    let rendered = render_type_errors(src, &[]);
    assert_eq!(rendered.matches("error:").count(), 1, "{rendered}");
    assert_snap!(SNAP_DIR, "error_in_every_instance", rendered);
}

#[test]
fn typecheck_errors_in_several_declarations() {
    let src = r"
fn f<G: Group, F: Scalar<G>>(instance g: G, instance x: F) -> F {
    g * x
}
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G) where g == g {
    verify(x + g == g)
}
";
    let rendered = render_type_errors(src, &[]);
    assert_eq!(rendered.matches("error:").count(), 2, "{rendered}");
    assert_snap!(SNAP_DIR, "errors_in_several_declarations", rendered);
}

/// Type-check `src` (no size parameters) and return every diagnostic.
fn type_diagnostics(src: &str) -> Vec<lang::diagnostic::Diagnostic> {
    let (module, diags) = UModule::parse(src);
    assert!(
        diags.iter().all(|d| d.severity == Severity::Warning),
        "expected no parse/semantic errors: {diags:?}"
    );
    module.unwrap().concretize(&Ctx::new()).unwrap().typecheck()
}

/// An integer is a vector index only within the finite-index range; beyond it, or negated,
/// it is a field element, rejected as an index at the index itself and accepted where the
/// field is pinned by a typed operand.
#[test]
fn numeric_literal_finite_index_boundary() {
    const BIG: &str = "34545435435435435435435";
    let max = usize::MAX.to_string();

    let ok = |src: &str| {
        let diags = type_diagnostics(src);
        assert!(diags.is_empty(), "`{src}`: {diags:?}");
    };
    ok("proto p<F: Field>(instance xs: [F; 2]) where xs[1] == xs[1] {}");
    for index in [BIG, max.as_str(), "-1"] {
        let src = format!("proto p<F: Field>(instance xs: [F; 2]) where xs[{index}] == xs[0] {{}}");
        let diags = type_diagnostics(&src);
        let start = src.find(&format!("[{index}]")).unwrap() + 1;
        assert!(
            diags.iter().any(|d| d.span == (start..start + index.len())
                && d.summary == "An integer outside the finite-index range cannot index a vector"),
            "`{src}`: {diags:?}"
        );
    }

    // A big or negated literal is a field element of the declared return type.
    ok(&format!(
        "fn big<F: Field>() -> F {{ {BIG} }}
         fn neg<F: Field>() -> F {{ -1 }}
         proto p<F: Field>(instance a: F) where a == a {{}}"
    ));

    // A typed argument pins a generic field parameter; two literals cannot choose between
    // the caller's fields.
    let first = "fn first<X: Field>(instance x: X, instance y: X) -> X { x }
                 proto p<F: Field>(instance a: F) where a == a {}";
    ok(&format!(
        "{first} fn g<F: Field, K: Field>(instance a: F) -> F {{ first(a, {BIG}) }}"
    ));
    let diags = type_diagnostics(&format!(
        "{first} fn g<F: Field, K: Field>(instance a: F) -> F {{ first({BIG}, 1) }}"
    ));
    assert!(
        diags
            .iter()
            .any(|d| d.summary == "Cannot infer type parameter `X` of `first`"),
        "two literals cannot choose between F and K: {diags:?}"
    );

    // A polynomial pins the field of its points even with two scalar fields in scope.
    ok(&format!(
        "proto t<G: Group, H: Group, F: Scalar<G>, K: Scalar<H>>(
             instance p: Uni<F, 1>, instance m: Mle<F, 2>, instance y: F,
         ) where p({BIG}) == y && eval(m, [{BIG}, 0]) == y {{}}"
    ));
}
