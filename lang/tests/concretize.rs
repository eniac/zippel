//! Size defaulting and size-concretization diagnostics.

mod common;

use common::assert_snap;
use lang::ast::module::UModule;
use lang::diagnostic::{Diagnostic, render_diagnostic};
use lang::id::Tid;
use share::Ctx;

const SNAP_DIR: &str = "snapshots/concretize";

fn minimal_sizes(src: &str, fixed: &[(&str, usize)]) -> Option<Vec<(String, usize)>> {
    let module = UModule::parse(src).0.unwrap();
    let mut ctx = Ctx::new();
    for (name, value) in fixed {
        ctx.insert(&Tid::new(name), value);
    }
    let sizes = module.minimal_sizes(&ctx)?;
    Some(sizes.iter().map(|(k, v)| (k.to_string(), *v)).collect())
}

/// A module whose only content is a proto with the given type variables.
fn with_typevars(typevars: &str) -> String {
    format!(
        "proto p<F: Field, {typevars}>(instance a: F) where a == a {{\n    verify(a == a)\n}}\n"
    )
}

fn sizes(pairs: &[(&str, usize)]) -> Option<Vec<(String, usize)>> {
    Some(pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect())
}

#[test]
fn minimal_sizes_defaults_an_unconstrained_size_to_one() {
    assert_eq!(
        minimal_sizes(&with_typevars("S: Size"), &[]),
        sizes(&[("S", 1)])
    );
}

/// Ranges declared before their `Size` parameter, in another declaration, still constrain it.
#[test]
fn minimal_sizes_sees_ranges_declared_before_their_size() {
    let src = r"
fn foo<F: Field, N: 1..S, S: Size>(a: [F; N]) -> F { a[0] }
proto bar<F: Field, S: Size, M: 2..S+1>(instance x: F) where x == x {
    verify(x == x)
}
";
    // N: 1..S and M: 2..S+1 are both non-empty only from S = 2.
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("S", 2)]));
}

#[test]
fn minimal_sizes_searches_sizes_sharing_a_range_jointly() {
    let expected = sizes(&[("X", 1), ("Y", 2)]);
    assert_eq!(
        minimal_sizes(&with_typevars("X: Size, Y: Size, M: X..Y"), &[]),
        expected
    );
    // Independent of declaration order.
    assert_eq!(
        minimal_sizes(&with_typevars("Y: Size, X: Size, M: X..Y"), &[]),
        expected
    );
}

#[test]
fn minimal_sizes_minimizes_the_sum() {
    // Y < X - 1 needs X >= Y + 2; the smallest sum is X = 3, Y = 1.
    assert_eq!(
        minimal_sizes(&with_typevars("X: Size, Y: Size, M: Y..X-1"), &[]),
        sizes(&[("X", 3), ("Y", 1)])
    );
}

#[test]
fn minimal_sizes_keeps_fixed_values() {
    assert_eq!(
        minimal_sizes(&with_typevars("X: Size, Y: Size, M: X..Y"), &[("X", 5)]),
        sizes(&[("X", 5), ("Y", 6)])
    );
}

#[test]
fn minimal_sizes_is_none_when_no_sizes_fit() {
    assert_eq!(minimal_sizes(&with_typevars("X: Size, M: X..X"), &[]), None);
}

/// A range in a body, over a derived size, inside `reduce`: `0..D` is non-empty only from
/// `D = (B - 1) * N >= 1`.
#[test]
fn minimal_sizes_sees_body_ranges_over_derived_sizes() {
    let src = r"
proto p<F: Field, N: Size, B: Size, D: (B - 1) * N>(instance a: [F; D + 1]) where a[0] == a[0] {
    verify(reduce(&&, [a[i] == a[i] for i in 0..D]))
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("B", 2), ("N", 1)]));
}

/// `L - 1` in a body must not underflow.
#[test]
fn minimal_sizes_avoids_underflow_in_bodies() {
    let src = r"
proto p<F: Field, L: Size>(instance a: [F; L]) where a[0] == a[0] {
    verify(a[L - 1] == a[L - 1])
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("L", 1)]));
    let src = r"
proto p<F: Field, L: Size>(instance a: [F; L + 1]) where a[0] == a[0] {
    let b = a[0..L - 1];
    verify(a[0] == a[0])
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("L", 2)]));
}

#[test]
fn concretize_error_is_reported_at_its_declaration() {
    let src = r"
fn sum<N: 0..3, F: Field>(instance a: [F; N]) -> F {
    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])
}
proto p<F: Field>(instance a: F) where a == a {
    verify(a == a)
}
";
    let module = UModule::parse(src).0.unwrap();
    let sizes = Ctx::new();
    let e = module.concretize(&sizes).unwrap_err();
    let d = Diagnostic::from(e);
    assert_eq!(&src[d.span.clone()], "sum");
    assert_snap!(
        SNAP_DIR,
        "error_at_declaration",
        render_diagnostic(&d, "test.zippel", src)
    );
}

/// Two declarations that differ only in type-variable names and return types tie at every call.
#[test]
fn interchangeable_declarations_are_rejected() {
    let src = r"
fn id<A: Group>(instance x: A) -> A {
    x
}
fn id<B: Group>(instance y: B) -> [B; 1] {
    [y]
}
proto p<G: Group, F: Scalar<G>>(instance g: G) where g == g {
    verify(g == g)
}
";
    let module = UModule::parse(src).0.unwrap();
    let e = module.concretize(&Ctx::new()).unwrap_err();
    let d = Diagnostic::from(e);
    assert_snap!(
        SNAP_DIR,
        "interchangeable_declarations",
        render_diagnostic(&d, "test.zippel", src)
    );
}
