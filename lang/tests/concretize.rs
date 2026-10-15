//! Size defaulting and size-concretization diagnostics.

mod common;

use common::assert_snap;
use lang::ast::{self, SizeRejection, SizeSearchError, UModule};
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
    let sizes = ast::minimal_sizes(&module, &ctx).ok()?;
    Some(sizes.iter().map(|(k, v)| (k.to_string(), *v)).collect())
}

fn exhausted(error: SizeSearchError) -> SizeRejection {
    match error {
        SizeSearchError::Exhausted { rejection, .. } => rejection,
        SizeSearchError::WorkLimit { .. } => {
            panic!("expected completed search exhaustion: {error}")
        }
    }
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
fn minimal_sizes_fails_when_no_sizes_fit() {
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
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("L", 1)]));
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

#[test]
fn a_protocol_with_an_unset_range_variable_is_ambiguous() {
    use lang::ast::module::ModuleError;
    use lang::id::Vid;
    let src = "proto p<F: Field, S: Size, N: 1..S>(instance a: [F; N]) where a == a {\n    verify(a == a)\n}\n";
    let module = UModule::parse(src).0.unwrap();
    let check = |pairs: &[(&str, usize)]| {
        let mut ctx = Ctx::new();
        for (name, value) in pairs {
            ctx.insert(&Tid::new(name), value);
        }
        let cmodule = module.concretize(&ctx).unwrap();
        module
            .check_protocol_instances(&cmodule, &Vid::from("p"), &ctx)
            .err()
    };

    // `N` ranges over 1..4: three instances, and nothing says which to run.
    let Some(e) = check(&[("S", 4)]) else {
        panic!("expected an ambiguous protocol");
    };
    let ModuleError::AmbiguousProtocol {
        ranges, instances, ..
    } = &e
    else {
        panic!("expected an ambiguous protocol, got {e:?}");
    };
    assert_eq!(*instances, 3);
    let [range] = ranges.as_slice() else {
        panic!("expected one expanded range, got {ranges:?}");
    };
    assert_eq!(range.var.node, Tid::new("N"));
    assert_eq!(range.range, "1..S");
    assert_eq!(range.values, [1, 2, 3]);
    assert_snap!(
        SNAP_DIR,
        "ambiguous_protocol",
        render_diagnostic(&Diagnostic::from(&e), "test.zippel", src)
    );
    // A range with one value concretizes to one instance.
    assert!(check(&[("S", 2)]).is_none());
}

#[test]
fn a_size_for_a_range_variable_is_rejected() {
    use lang::ast::module::ModuleError;
    let src = "proto p<F: Field, S: Size, N: 1..S>(instance a: [F; N]) where a == a {\n    verify(a == a)\n}\n";
    let module = UModule::parse(src).0.unwrap();
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &4);
    sizes.insert(&Tid::new("N"), &2);
    let e = module.concretize(&sizes).unwrap_err();
    let ModuleError::SizeForRange { var, range } = &e else {
        panic!("expected a size for a range variable to be rejected, got {e:?}");
    };
    assert_eq!(var.node, Tid::new("N"));
    assert_eq!(range, "1..S");
    assert_snap!(
        SNAP_DIR,
        "size_for_range",
        render_diagnostic(&Diagnostic::from(&e), "test.zippel", src)
    );
}

/// Every range that expands is labelled; a long list of values is shortened.
#[test]
fn an_ambiguous_protocol_labels_each_expanded_range() {
    use lang::id::Vid;
    let src = "proto p<F: Field, N: 2..21, M: 1..3>(instance a: [F; N], instance b: [F; M]) where a == a {\n    verify(a == a)\n}\n";
    let module = UModule::parse(src).0.unwrap();
    let cmodule = module.concretize(&Ctx::new()).unwrap();
    let e = module
        .check_protocol_instances(&cmodule, &Vid::from("p"), &Ctx::new())
        .unwrap_err();
    assert_snap!(
        SNAP_DIR,
        "ambiguous_protocol_two_ranges",
        render_diagnostic(&Diagnostic::from(&e), "test.zippel", src)
    );
}

#[test]
fn a_size_shared_with_a_range_variable_sets_only_the_size() {
    // `N` is a `Size` in the protocol and a range in `f`: the size sets the
    // protocol's `N`, and `f` still has one instance per value of `2..4`.
    let src = concat!(
        "fn f<F: Field, N: 2..4>(a: [F; N]) -> F { a[0] }\n",
        "proto p<F: Field, N: Size>(instance a: [F; N]) where a == a {\n",
        "    verify(a == a)\n",
        "}\n",
    );
    let module = UModule::parse(src).0.unwrap();
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &3);
    let cmodule = module.concretize(&sizes).unwrap();
    let count = |name: &str| {
        cmodule
            .iter()
            .filter(|(sig, _)| sig.name.node.0 == name)
            .count()
    };
    assert_eq!(count("f"), 2);
    assert_eq!(count("p"), 1);
}

#[test]
fn minimal_sizes_matches_dot_lengths() {
    let src = r"
proto p<F: Field, N: Size>(instance a: [F; N], instance b: [F; 3]) where dot(a, b) == dot(a, b) {
    verify(dot(a, b) == dot(a, b))
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 3)]));
}

#[test]
fn minimal_sizes_reaches_recursive_overloads() {
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..5>(instance x: [F; K]) -> F {
    weights(x[0..K-1]) + x[K-1]
}
proto p<F: Field, N: Size>(instance a: [F; N]) where weights(a) == weights(a) {
    verify(weights(a) == weights(a))
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 2)]));
}

#[test]
fn minimal_sizes_respects_fft_lengths() {
    let src = r"
proto p<F: Field, N: Size>(instance a: [F; N+2]) where a == a {
    verify(interpolate(a) == interpolate(a))
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 2)]));
}

#[test]
fn minimal_sizes_does_not_require_coverage_from_unused_helpers() {
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..5>(instance x: [F; K]) -> F {
    weights(x[0..K-1]) + x[K-1]
}
fn unused<F: Field, N: Size>(instance a: [F; N]) -> F { weights(a) }
proto p<F: Field>(instance a: F) where a == a { verify(a == a) }
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 1)]));
}

#[test]
fn minimal_sizes_does_not_count_calls_from_unused_helpers_as_coverage() {
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..5>(instance x: [F; K]) -> F {
    weights(x[0..K-1]) + x[K-1]
}
fn unused<F: Field>(instance x: [F; 2]) -> F { weights(x) }
proto p<F: Field, N: Size>(instance x: [F; N]) where x == x {
    verify(weights(x) == weights(x))
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 2)]));
}

#[test]
fn minimal_sizes_checks_unused_helpers() {
    let src = r"
fn unused<F: Field, N: Size, K: 1..N>(instance a: [F; K]) -> F {
    dot(a, [a[0], a[0]])
}
proto p<F: Field>(instance a: F) where a == a { verify(a == a) }
";
    // N=1 erases the helper; larger N includes the ill-typed K=1 instance.
    assert_eq!(minimal_sizes(src, &[]), None);
}

#[test]
fn minimal_sizes_checks_every_dependent_range_branch() {
    let src = r"
fn helper<F: Field, N: Size, K: 1..N, L: 1..K>(instance a: [F; L]) -> F { a[0] }
proto p<F: Field>(instance a: F) where a == a { verify(a == a) }
";
    // Even when K=2 produces an instance, K=1 has an empty L range.
    assert_eq!(minimal_sizes(src, &[]), None);
}

#[test]
fn minimal_sizes_obeys_operator_bounds_and_fixed_values() {
    let src = r"
proto p<F: Field, N: Size, M: Size>(instance a: [F; N], instance b: [F; M]) where dot(a, b) == a[2] {
    verify(dot(a, b) == a[2])
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("M", 3), ("N", 3)]));
    assert_eq!(
        minimal_sizes(src, &[("M", 5)]),
        sizes(&[("M", 5), ("N", 5)])
    );
    assert_eq!(minimal_sizes(src, &[("M", 17)]), None);
    assert_eq!(
        minimal_sizes(src, &[("M", 17), ("N", 17)]),
        sizes(&[("M", 17), ("N", 17)])
    );
}

#[test]
fn minimal_sizes_resolves_calls_with_only_a_specialized_overload() {
    let src = r"
fn helper<F: Field, K: 2..5>(instance a: [F; K]) -> F { a[0] }
proto p<F: Field, N: Size>(instance a: [F; N]) where helper(a) == a[0] {
    verify(helper(a) == a[0])
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 2)]));
}

#[test]
fn minimal_sizes_distinguishes_polynomial_applications_from_helper_calls() {
    let src = r"
fn helper<F: Field, N: Size>(instance a: [F; N]) -> F { a[2] }
proto p<F: Field>(instance a: F, instance helper: Poly<F, 1, 1>) where helper(a) == a {
    verify(helper(a) == a)
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 3)]));
}

#[test]
fn failed_size_search_reports_range_rejection() {
    use lang::ast::SizeSearchStage;
    let module = UModule::parse(&with_typevars("X: Size, M: X..X"))
        .0
        .unwrap();
    let error = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert_eq!(error.stage, SizeSearchStage::Ranges);
    assert_eq!(error.candidate.get(&Tid::new("X")), Some(&1));
    assert!(error.diagnostics[0].summary.contains("empty"));
}

#[test]
fn failed_size_search_preserves_concretization_errors() {
    use lang::ast::SizeSearchStage;
    let src = r"
fn id<A: Group>(instance x: A) -> A { x }
fn id<B: Group>(instance y: B) -> [B; 1] { [y] }
proto p<G: Group, N: Size>(instance g: G) where g == g { verify(g == g) }
";
    let module = UModule::parse(src).0.unwrap();
    let error = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert_eq!(error.stage, SizeSearchStage::Concretization);
    let expected = Diagnostic::from(module.concretize(&error.candidate).unwrap_err());
    assert_eq!(error.diagnostics[0].summary, expected.summary);
    assert_eq!(error.diagnostics[0].span, expected.span);
}

#[test]
fn failed_size_search_preserves_type_errors() {
    use lang::ast::SizeSearchStage;
    let src = r"
proto p<G: Group, F: Scalar<G>, N: Size>(instance x: F, instance g: G) where x == x {
    verify(x + g == g)
}
";
    let module = UModule::parse(src).0.unwrap();
    let error = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert_eq!(error.stage, SizeSearchStage::Typecheck);
    let expected = module.concretize(&error.candidate).unwrap().typecheck();
    assert_eq!(error.diagnostics[0].span, expected[0].span);
    assert!(error.diagnostics[0].summary.contains("Cannot add"));
}

#[test]
fn failed_size_search_retains_a_candidate_that_typechecks() {
    use lang::ast::SizeSearchStage;
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..4>(instance x: [F; K]) -> F {
    weights(x[0..K-1]) + x[K-1]
}
fn weights<F: Field>(instance x: [F; 4]) -> F { x[0] }
proto p<F: Field, N: Size>(instance a: [F; N], instance b: [F; 2]) where weights(a) == dot(a, b) {
    verify(weights(a) == dot(a, b))
}
";
    let module = UModule::parse(src).0.unwrap();
    let error = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert_eq!(error.stage, SizeSearchStage::Coverage);
    assert_eq!(error.candidate.get(&Tid::new("N")), Some(&2));
    assert!(
        module
            .concretize(&error.candidate)
            .unwrap()
            .typecheck()
            .is_empty()
    );
    assert_eq!(error.diagnostics.len(), 1);
    assert!(error.diagnostics[0].summary.contains("not covered"));
}

#[test]
fn minimal_sizes_is_invariant_under_helper_renaming() {
    let src = r"
fn a<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn a<F: Field>(instance x: [F; 2]) -> F { z(x[0..1]) }
fn z<F: Field>(instance x: [F; 1]) -> F { a(x) }
proto p<F: Field, N: Size>(instance x: F) where x == x { verify(x == x) }
";
    let renamed = src
        .replace("fn a<", "fn zz<")
        .replace("{ a(x) }", "{ zz(x) }");
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 1)]));
    assert_eq!(minimal_sizes(&renamed, &[]), minimal_sizes(src, &[]));
}

#[test]
fn minimal_sizes_is_invariant_under_source_spans() {
    use lang::ast::spanned::Spanned;
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..4>(instance x: [F; K]) -> F { weights(x[0..K-1]) + x[K-1] }
proto p<F: Field, N: Size>(instance x: [F; N]) where weights(x) == weights(x) { verify(x == x) }
";
    let module = UModule::parse(src).0.unwrap();
    let expected = ast::minimal_sizes(&module, &Ctx::new()).unwrap();
    for span in [0..0, 100..200] {
        let decls = module
            .iter_decls()
            .map(|mut decl| {
                decl.sig.name.span = span.clone();
                Spanned::dummy(decl)
            })
            .collect();
        let sizes = ast::minimal_sizes(&UModule::from_decls(decls), &Ctx::new()).unwrap();
        assert_eq!(sizes, expected);
    }
}

#[test]
fn minimal_sizes_allows_valid_empty_slices() {
    let src = r"
proto p<F: Field, N: Size>(instance x: [F; N]) where x == x {
    verify(x[0..0] == x[0..0])
}
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 1)]));
}

#[test]
fn minimal_sizes_reports_singleton_end_overflow() {
    let src = format!(
        "fn helper<F: Field, K: {}>(instance x: F) -> F {{ x }}\n{}",
        usize::MAX,
        with_typevars("N: Size")
    );
    let module = UModule::parse(&src).0.unwrap();
    let error = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert!(error.diagnostics[0].summary.contains("overflow"));
    assert!(module.concretize(&error.candidate).is_err());
}

#[test]
fn minimal_sizes_checks_every_expansion_even_after_a_valid_one() {
    use lang::ast::SizeSearchStage;
    let src = r"
fn helper<F: Field, K: 2..4>(instance a: [F; K]) -> F { dot(a, [a[0], a[0]]) }
proto p<F: Field, N: Size>(instance a: F) where a == a { verify(a == a) }
";
    let module = UModule::parse(src).0.unwrap();
    let rejection = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert_eq!(rejection.stage, SizeSearchStage::Typecheck);
    assert!(
        rejection.diagnostics[0]
            .notes
            .iter()
            .any(|note| note.message.contains("[F; 3]"))
    );
}

#[test]
fn minimal_sizes_covers_relation_only_calls() {
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..4>(instance x: [F; K]) -> F { weights(x[0..K-1]) + x[K-1] }
proto p<F: Field, N: Size>(instance x: [F; N]) where weights(x) == weights(x) { verify(x == x) }
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 2)]));
}

#[test]
fn minimal_sizes_preserves_scope_for_polynomial_calls() {
    for body in [
        "let helper = fun(t) => t * a; verify(helper(a) == a * a)",
        "verify([helper(a) for helper in polys] == [helper(a) for helper in polys])",
        "let p = fun(helper) => helper(a); verify(p(a) == p(a))",
    ] {
        let src = format!(
            "fn helper<F: Field, N: Size>(instance x: [F; N]) -> F {{ x[2] }}\nproto p<F: Field>(instance a: F, instance polys: [Poly<F, 1, 1>; 1]) where a == a {{ {body} }}"
        );
        assert_eq!(minimal_sizes(&src, &[]), sizes(&[("N", 3)]), "{src}");
    }
}

#[test]
fn minimal_sizes_is_invariant_under_declaration_reordering() {
    use lang::ast::spanned::Spanned;
    let src = r"
fn weights<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn weights<F: Field, K: 2..4>(instance x: [F; K]) -> F { weights(x[0..K-1]) + x[K-1] }
proto p<F: Field, N: Size>(instance x: [F; N]) where weights(x) == weights(x) { verify(x == x) }
";
    let module = UModule::parse(src).0.unwrap();
    let expected = ast::minimal_sizes(&module, &Ctx::new()).unwrap();
    let decls = module.iter_decls().map(Spanned::dummy).collect::<Vec<_>>();
    for start in 0..decls.len() {
        let mut reordered = decls.clone();
        reordered.rotate_left(start);
        assert_eq!(
            ast::minimal_sizes(&UModule::from_decls(reordered), &Ctx::new()).unwrap(),
            expected
        );
    }
}

#[test]
fn minimal_sizes_rejects_a_later_empty_dependent_branch() {
    use lang::ast::SizeSearchStage;
    let src = r"
fn helper<F: Field, N: Size, K: 1..N, L: K..2>(instance x: [F; L]) -> F { x[0] }
proto p<F: Field>(instance x: F) where x == x { verify(x == x) }
";
    let module = UModule::parse(src).0.unwrap();
    let fixed = Ctx::singleton(Tid::new("N"), 3);
    assert!(module.concretize(&fixed).unwrap().typecheck().is_empty());
    assert_eq!(
        exhausted(ast::minimal_sizes(&module, &fixed).unwrap_err()).stage,
        SizeSearchStage::Ranges
    );
}

#[test]
fn minimal_sizes_rejects_zero_steps_without_hanging() {
    let src = r"
fn helper<F: Field, N: Size, K: 0,N-1..3>(instance x: [F; K+1]) -> F { x[0] }
proto p<F: Field>(instance x: F) where x == x { verify(x == x) }
";
    let module = UModule::parse(src).0.unwrap();
    let bad = Ctx::singleton(Tid::new("N"), 1);
    assert!(module.concretize(&bad).is_err());
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 2)]));
}

#[test]
fn minimal_sizes_matches_exhaustive_compiler_validation() {
    let src = r"
proto p<F: Field, X: Size, Y: Size>(instance a: [F; X], instance b: [F; Y]) where dot(a, b) == a[2] {
    verify(dot(a, b) == a[2])
}
";
    let module = UModule::parse(src).0.unwrap();
    let mut candidates: Vec<_> = (1..=4).flat_map(|x| (1..=4).map(move |y| (x, y))).collect();
    candidates.sort_by_key(|&(x, y)| (x + y, x, y));
    let expected = candidates
        .into_iter()
        .find_map(|(x, y)| {
            let mut sizes = Ctx::singleton(Tid::new("X"), x);
            sizes.insert(&Tid::new("Y"), &y);
            module
                .concretize(&sizes)
                .is_ok_and(|module| module.typecheck().is_empty())
                .then_some(sizes)
        })
        .unwrap();
    assert_eq!(ast::minimal_sizes(&module, &Ctx::new()).unwrap(), expected);
}

#[test]
fn minimal_sizes_does_not_require_coverage_of_unused_cycles() {
    let src = r"
fn a<F: Field>(instance x: [F; 1]) -> F { x[0] }
fn a<F: Field>(instance x: [F; 2]) -> F { z(x[0..1]) }
fn z<F: Field>(instance x: [F; 1]) -> F { a(x) }
fn entry<F: Field, N: Size>(instance x: [F; N]) -> F { a(x) }
proto p<F: Field>(instance x: F) where x == x { verify(x == x) }
";
    let renamed = src
        .replace("fn a<", "fn zz<")
        .replace("{ a(x) }", "{ zz(x) }");
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 1)]));
    assert_eq!(minimal_sizes(&renamed, &[]), sizes(&[("N", 1)]));
}

#[test]
fn minimal_sizes_handles_reachable_function_cycles() {
    let src = r"
fn a<F: Field>(instance x: F) -> F { b(x) }
fn b<F: Field>(instance x: F) -> F { a(x) }
proto p<F: Field, N: Size>(instance x: F) where x == x { verify(a(x) == x) }
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[("N", 1)]));

    let src = format!("fn b<F: Field>(instance x: [F; 2]) -> F {{ x[0] }}\n{src}");
    let module = UModule::parse(&src).0.unwrap();
    let rejection = exhausted(ast::minimal_sizes(&module, &Ctx::new()).unwrap_err());
    assert_eq!(rejection.stage, ast::SizeSearchStage::Coverage);
    assert_eq!(rejection.diagnostics.len(), 1);
    assert!(rejection.diagnostics[0].summary.contains("`b`"));
}

#[test]
fn minimal_sizes_handles_protocol_cycles() {
    let src = r"
proto p<F: Field>(instance x: F) where x == x { q(x); verify(x == x) }
proto q<F: Field>(instance x: F) where x == x { p(x); verify(x == x) }
";
    assert_eq!(minimal_sizes(src, &[]), sizes(&[]));
}
