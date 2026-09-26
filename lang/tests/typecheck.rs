//! Type error snapshot tests.
//!
//! Each test parses, concretizes, and type-checks a program via `CModule::typecheck`, renders
//! the resulting diagnostics, and compares them against insta snapshots in
//! `snapshots/typecheck/`.

mod common;

use common::assert_snap;
use lang::ast::module::UModule;
use lang::diagnostic::{render_diagnostic, Severity};
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
