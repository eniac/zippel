//! Resolving calls to generic functions: every callee type parameter must end up bound to a
//! caller type, or be reported at the call.

mod common;

use common::assert_snap;
use lang::ast::module::UModule;
use lang::diagnostic::{Severity, render_diagnostic};
use share::Ctx;

const SNAP_DIR: &str = "snapshots/generic_calls";

/// The rendered type errors of `src`, joined; empty when it type-checks.
fn type_errors(src: &str) -> String {
    let (module, diags) = UModule::parse(src);
    assert!(
        diags.iter().all(|d| d.severity == Severity::Warning),
        "expected no parse/semantic errors: {diags:?}"
    );
    let cmodule = module.unwrap().concretize(&Ctx::new()).unwrap();
    cmodule
        .typecheck()
        .iter()
        .map(|d| render_diagnostic(d, "test.zippel", src))
        .collect::<Vec<_>>()
        .join("\n---\n")
}

fn assert_well_typed(src: &str) {
    let errors = type_errors(src);
    assert!(errors.is_empty(), "{errors}");
}

// ── Resolution ──────────────────────────────────────────────────────────

/// `F` appears only in the return type; its kind `Scalar<G>` determines it from `G`.
#[test]
fn return_only_scalar_is_resolved_from_its_group() {
    assert_well_typed(
        r"
fn sample<G: Group, F: Scalar<G>>(instance g: G) -> F {
    random<F>
}
proto p<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = sample(g);
    verify(g * r == g * r)
}
",
    );
}

/// `GT` appears only in the return type; `Pairing<G1, G2>` determines it from its groups.
#[test]
fn pairing_target_is_resolved_from_its_groups() {
    assert_well_typed(
        r"
fn target<G1: Group, G2: Group, GT: Pairing<G1, G2>>(instance a: G1, instance b: G2) -> GT {
    pair(a, b)
}
proto p<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>>(instance a: G1, instance b: G2, instance t: GT) where t == t {
    verify(target(a, b) == t)
}
",
    );
}

/// The call's type is the caller's `G2`, whatever the callee's parameter is named.
#[test]
fn result_type_is_the_callers_type() {
    for callee in ["G", "A"] {
        assert_well_typed(&format!(
            r"
fn dbl<{callee}: Group>(instance a: {callee}) -> {callee} {{
    a + a
}}
proto p<G1: Group, G2: Group, F: Scalar<G1, G2>>(instance h: G2) where h == h {{
    verify(dbl(h) == h)
}}
"
        ));
    }
}

/// A callee parameter named like a caller type (`G`) and another like a fresh name (`G1`) stay
/// distinct.
#[test]
fn callee_parameter_names_never_clash() {
    assert_well_typed(
        r"
fn second<G: Group, G1: Group>(instance a: G, instance b: G1) -> G1 {
    b
}
proto p<G: Group, H: Group, F: Scalar<G, H>>(instance g: G, instance h: H) where g == g {
    verify(second(g, h) == h)
}
",
    );
}

/// Several overloads fit; the one of lowest degree is the most specific.
#[test]
fn the_most_specific_overload_is_chosen() {
    assert_well_typed(
        r"
fn lead<F: Field>(instance p: Uni<F, 3>) -> F {
    p(0)
}
fn lead<F: Field>(instance p: Uni<F, 5>) -> [F; 1] {
    [p(0)]
}
proto t<F: Field>(instance p: Uni<F, 2>, instance x: F) where x == x {
    verify(lead(p) == x)
}
",
    );
}

// ── Errors ──────────────────────────────────────────────────────────────

/// Both overloads fit and neither is more specific; only the tied ones are listed.
#[test]
fn a_call_with_no_most_specific_overload_is_ambiguous() {
    let src = r"
fn mix<F: Field>(instance p: Uni<F, 3>, instance q: Uni<F, 5>) -> F {
    p(0)
}
fn mix<F: Field>(instance p: Uni<F, 5>, instance q: Uni<F, 3>) -> F {
    q(0)
}
fn mix<F: Field>(instance p: F, instance q: F) -> F {
    p
}
proto t<F: Field>(instance p: Uni<F, 2>, instance x: F) where x == x {
    verify(mix(p, p) == x)
}
";
    assert_snap!(SNAP_DIR, "ambiguous_overload", type_errors(src));
}

/// Two different caller types cannot both be `T`.
#[test]
fn two_caller_types_for_one_parameter_are_rejected() {
    let src = r"
fn same<T: Field>(instance a: T, instance b: T) -> T {
    a
}
proto p<F: Field, K: Field>(instance a: F, instance b: K) where a == a {
    verify(same(a, b) == a)
}
";
    assert_snap!(
        SNAP_DIR,
        "two_caller_types_for_one_parameter",
        type_errors(src)
    );
}

/// A `Field` parameter only in the return type is determined by nothing.
#[test]
fn return_only_field_parameter_cannot_be_inferred() {
    let src = r"
fn zero<G: Group, F: Field>(instance g: G) -> F {
    0
}
proto p<G: Group, F: Scalar<G>>(instance g: G) where g == g {
    verify(zero(g) == zero(g))
}
";
    assert_snap!(SNAP_DIR, "return_only_field_parameter", type_errors(src));
}

/// The caller has no scalar field of `H`.
#[test]
fn missing_scalar_field_is_reported() {
    let src = r"
fn sample<G: Group, F: Scalar<G>>(instance g: G) -> F {
    random<F>
}
proto p<G: Group, H: Group, F: Scalar<G>>(instance g: G, instance h: H) where g == g {
    verify(sample(h) == sample(h))
}
";
    assert_snap!(SNAP_DIR, "missing_scalar_field", type_errors(src));
}

/// The caller declares two scalar fields of `G`.
#[test]
fn ambiguous_scalar_field_is_reported() {
    let src = r"
fn sample<G: Group, F: Scalar<G>>(instance g: G) -> F {
    random<F>
}
proto p<G: Group, F: Scalar<G>, K: Scalar<G>>(instance g: G) where g == g {
    verify(sample(g) == sample(g))
}
";
    assert_snap!(SNAP_DIR, "ambiguous_scalar_field", type_errors(src));
}
