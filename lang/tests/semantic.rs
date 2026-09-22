//! Semantic error snapshot and assertion tests.
//!
//! Snapshot tests render the full diagnostic output and compare against
//! insta snapshots in `snapshots/semantic/`. Assertion tests verify the
//! presence/absence of a specific error condition without snapshotting.

mod common;

use common::{assert_snap, render_errors, render_warnings};
use lang::ast::module::UModule;
use lang::diagnostic::{Phase, Severity};

const SNAP_DIR: &str = "snapshots/semantic";

// ── Semantic errors (snapshot) ──────────────────────────────────────────

#[test]
fn semantic_undefined_variable() {
    let rendered =
        render_errors("proto p<F: Field>(instance a: F) where a == b { verify(a == a) }");
    assert!(
        rendered.contains("undefined variable"),
        "expected semantic error for undefined variable `b`"
    );
    assert_snap!(SNAP_DIR, "undefined_variable", rendered);
}

#[test]
fn semantic_type_alias_cycle() {
    let rendered = render_errors("type A = B;\ntype B = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error"
    );
    assert_snap!(SNAP_DIR, "type_alias_cycle", rendered);
}

#[test]
fn semantic_type_alias_cycle_three() {
    let rendered = render_errors("type A = B;\ntype B = C;\ntype C = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error"
    );
    assert_snap!(SNAP_DIR, "type_alias_cycle_three", rendered);
}

#[test]
fn semantic_type_alias_self_ref() {
    let rendered = render_errors("type A = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error for self-referential alias"
    );
    assert_snap!(SNAP_DIR, "type_alias_self_ref", rendered);
}

#[test]
fn semantic_unbound_size_var() {
    // N is used in the type [F; N] but not declared in the typevar list.
    let rendered =
        render_errors("proto p<F: Field>(instance a: [F; N]) where a == a { verify(a == a) }");
    assert!(
        rendered.contains("unbound size variable"),
        "expected unbound size variable error"
    );
    assert_snap!(SNAP_DIR, "unbound_size_var", rendered);
}

#[test]
fn semantic_pairing_refs_non_group() {
    // Pairing<F, F> is invalid — F is Field, not Group.
    let src = "proto p<F: Field, P: Pairing<F, F>>(instance a: F) where a == a { verify(a == a) }";
    let rendered = render_errors(src);
    assert!(
        rendered.contains("`F` is not a Group"),
        "expected invalid group ref error, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "pairing_refs_non_group", rendered);
}

#[test]
fn semantic_unresolved_group_ref() {
    // Pairing<G, H> where G and H are not declared at all.
    let src = "proto p<P: Pairing<G, H>>(instance a: F) where a == a { verify(a == a) }";
    let rendered = render_errors(src);
    assert!(
        rendered.contains("unresolved group reference"),
        "expected unresolved group reference error, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "unresolved_group_ref", rendered);
}

#[test]
fn semantic_invalid_range_bounds() {
    // Range 10..5 has start > end.
    let rendered =
        render_errors("proto p<N: 10..5>(instance a: [F; N]) where a == a { verify(a == a) }");
    assert!(
        rendered.contains("invalid range bounds"),
        "expected invalid range bounds error"
    );
    assert_snap!(SNAP_DIR, "invalid_range_bounds", rendered);
}

#[test]
fn semantic_impure_verify_in_where() {
    // verify() nested in a where clause constraint is impure.
    // The where clause requires `exp == exp`, so we embed verify inside one side.
    let src = "proto p<F: Field>(instance a: F, instance b: F) where a == verify(b == b) { verify(a == a) }";
    let rendered = render_errors(src);
    assert!(
        rendered.contains("impure"),
        "expected impure relation error for verify in where clause, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "impure_verify_in_where", rendered);
}

#[test]
fn semantic_circular_typevar_ref() {
    // V: Pairing<G> and G: Pairing<V> — circular kind reference.
    let src = "proto p<V: Pairing<G, G>, G: Pairing<V, V>>(instance a: V) where a == a { verify(a == a) }";
    let rendered = render_errors(src);
    assert!(
        rendered.contains("circular type variable reference"),
        "expected circular typevar ref error, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "circular_typevar_ref", rendered);
}

#[test]
fn semantic_undefined_variable_repeated() {
    // `b` used twice — should merge into one error with "also used here".
    let rendered =
        render_errors("proto p<F: Field>(instance a: F) where b == b { verify(a == a) }");
    assert!(
        rendered.contains("undefined variable `b`"),
        "expected undefined variable error, got: {rendered}"
    );
    assert!(
        rendered.contains("also used here"),
        "expected 'also used here' label, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "undefined_variable_repeated", rendered);
}

#[test]
fn semantic_unbound_size_var_repeated() {
    // `N` used in two places — should merge into one error with "also used here".
    let rendered = render_errors(
        "proto p<F: Field>(instance a: [F; N], instance b: [F; N]) where a == a { verify(a == a) }",
    );
    assert!(
        rendered.contains("unbound size variable `N`"),
        "expected unbound size variable error, got: {rendered}"
    );
    assert!(
        rendered.contains("also used here"),
        "expected 'also used here' label, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "unbound_size_var_repeated", rendered);
}

#[test]
fn semantic_duplicate_typevar_triple() {
    // `F` declared three times — should merge into one error with "also declared here".
    let rendered = render_errors(
        "proto p<F: Field, F: Group, F: Field>(instance a: F) where a == a { verify(a == a) }",
    );
    assert!(
        rendered.contains("duplicate type variable `F`"),
        "expected duplicate typevar error, got: {rendered}"
    );
    assert!(
        rendered.contains("also declared here"),
        "expected 'also declared here' label, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "duplicate_typevar_triple", rendered);
}

#[test]
fn semantic_undefined_variable_did_you_mean_let() {
    // `x` is let-bound, `y` is undefined but similar to `x`.
    // The suggestion should find `x` even though it's not a function argument.
    let src = "proto p<F: Field>(instance a: F) where let x = a; y == a { }";
    let (_, diags) = UModule::parse(src);
    let has_suggestion = diags.iter().any(|d| {
        d.summary.contains("undefined variable `y`")
            && d.suggestions.iter().any(|s| s.message.contains("`x`"))
    });
    assert!(
        has_suggestion,
        "expected '`x`' in suggestion for `y`, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

// ── Semantic errors (assertion only) ────────────────────────────────────

#[test]
fn semantic_defined_variable_ok() {
    let src = "proto p<F: Field>(instance a: F) where a == a { verify(a == a) }";
    let (_, diags) = UModule::parse(src);
    let sem_errors: Vec<_> = diags
        .iter()
        .filter(|d| d.phase == Phase::Semantic && d.severity == Severity::Error)
        .collect();
    assert!(
        sem_errors.is_empty(),
        "expected no semantic errors, got: {:?}",
        sem_errors.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_let_binding_in_scope() {
    let src = "proto p<F: Field>(instance a: F) where let x = a; x == a { verify(a == a) }";
    let (_, diags) = UModule::parse(src);
    let sem_errors: Vec<_> = diags
        .iter()
        .filter(|d| d.phase == Phase::Semantic && d.severity == Severity::Error)
        .collect();
    assert!(
        sem_errors.is_empty(),
        "expected no semantic errors for let-bound variable, got: {:?}",
        sem_errors.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_let_binding_undefined_after() {
    let src = "proto p<F: Field>(instance a: F) where let x = a; y == a { }";
    let (_, diags) = UModule::parse(src);
    let sem_diags: Vec<_> = diags
        .iter()
        .filter(|d| d.phase == Phase::Semantic)
        .collect();
    assert!(
        !sem_diags.is_empty(),
        "expected semantic error for undefined `y` after let, got: {:?}",
        sem_diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_no_proto_declaration() {
    let src = "fn f<F: Field>(instance a: F) -> F { a }";
    let (_, diags) = UModule::parse(src);
    let no_proto = diags
        .iter()
        .find(|d| d.summary.contains("no proto declaration"));
    assert!(
        no_proto.is_some(),
        "expected 'no proto declaration' error, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
    assert_eq!(
        no_proto.unwrap().severity,
        Severity::Error,
        "NoProtoDeclaration should be an error"
    );
}

#[test]
fn semantic_multiple_proto_declarations() {
    let src = "proto p1<F: Field>(instance a: F) where a == a { }\n\
               proto p2<F: Field>(instance a: F) where a == a { }";
    let (_, diags) = UModule::parse(src);
    let has_multi = diags.iter().any(|d| d.summary.contains("multiple proto"));
    assert!(
        has_multi,
        "expected 'multiple proto declarations' error, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_impure_relation_challenge() {
    // Challenge in the body is fine; the impure check only applies to the
    // `where` relation. Since the parser doesn't allow `<-` in `where`,
    // this test verifies that a normal proto with challenge in body is OK.
    let src = "proto p<F: Field>(instance a: F) where a == a { r <- challenge<F>() }";
    let (_, diags) = UModule::parse(src);
    let has_impure = diags.iter().any(|d| d.summary.contains("impure"));
    assert!(
        !has_impure,
        "expected no impure relation error (challenge is in body, not relation), got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_duplicate_typevar() {
    let src = "proto p<F: Field, F: Group>(instance a: F) where a == a { }";
    let (_, diags) = UModule::parse(src);
    let has_dup = diags
        .iter()
        .any(|d| d.summary.contains("duplicate type variable"));
    assert!(
        has_dup,
        "expected duplicate typevar error, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

// `check_proto_verify` (E0013) is implemented in `lang::semantic::verify` but not yet wired
// into `UModule::parse` — it resolves calls by name with no overload resolution, which isn't
// mature enough to enforce on every parse. See the TODO in `lang/src/ast/module.rs`. These tests
// exercise the check directly instead of through `UModule::parse`/`render_errors`, so they stay
// green (and keep covering the check's own logic) independent of that deferral.

#[test]
fn semantic_proto_without_verify() {
    let src = "proto p<F: Field>(instance a: F) where a == a { let b = a; }";
    let (decls, parse_errors) = lang::parser::parse_decls(src);
    assert!(parse_errors.is_empty());
    let diags = lang::semantic::check_proto_verify(&decls);
    let rendered: String = diags
        .iter()
        .map(|d| lang::diagnostic::render_diagnostic(d, "test.zippel", src))
        .collect();
    assert!(
        rendered.contains("has no `verify` check"),
        "expected E0013, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "proto_without_verify", rendered);
}

#[test]
fn semantic_proto_empty_body_has_no_verify() {
    let src = "proto p<F: Field>(instance a: F) where a == a { }";
    let (decls, _) = lang::parser::parse_decls(src);
    let diags = lang::semantic::check_proto_verify(&decls);
    assert!(
        diags.iter().any(|d| d.code.as_deref() == Some("E0013")),
        "expected E0013, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_proto_verify_through_function_calls() {
    // `check` verifies; `outer` only calls `check`; the proto only calls `outer`.
    let src = "fn check<F: Field>(instance a: F) { verify(a == a) }\n\
               fn outer<F: Field>(instance a: F) { check(a) }\n\
               proto p<F: Field>(instance a: F) where a == a { outer(a) }";
    let (decls, _) = lang::parser::parse_decls(src);
    let diags = lang::semantic::check_proto_verify(&decls);
    assert!(
        !diags.iter().any(|d| d.code.as_deref() == Some("E0013")),
        "verify reached through calls should satisfy E0013, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_proto_calling_non_verifying_function_has_no_verify() {
    let src = "fn f<F: Field>(instance a: F) -> F { a }\n\
               proto p<F: Field>(instance a: F) where a == a { let b = f(a); }";
    let (decls, _) = lang::parser::parse_decls(src);
    let diags = lang::semantic::check_proto_verify(&decls);
    assert!(
        diags.iter().any(|d| d.code.as_deref() == Some("E0013")),
        "expected E0013, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

// ── Valid programs (assertion only) ─────────────────────────────────────

#[test]
fn valid_program_no_errors() {
    let src = "proto p<F: Field>(instance a: F) where a == a { verify(a == a) }";
    let (_, diags) = UModule::parse(src);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "expected no errors for valid program, got: {:?}",
        errors.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn valid_program_with_let() {
    let src = "proto p<F: Field>(instance a: F) where\n\
               let x = a;\n\
               let y = x;\n\
               y == a\n\
               { verify(a == a) }";
    let (_, diags) = UModule::parse(src);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "expected no errors, got: {:?}",
        errors.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

// ── Warnings (W0001) ────────────────────────────────────────────────────

/// Helper: collect warning summaries from parsing `src`.
fn warnings(src: &str) -> Vec<String> {
    let (_, diags) = UModule::parse(src);
    diags
        .iter()
        .filter(|d| d.severity == Severity::Warning)
        .map(|d| d.summary.clone())
        .collect()
}

// ── W0001: Dead variable / computation (snapshots) ──────────────────────

// Snapshot tests render the full warning diagnostic output.
// Negative cases use assertion tests to check no warning is emitted.

// ── Snapshot: unused function argument ──

#[test]
fn w0001_unused_arg() {
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { a }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`b`"),
        "expected W0001 for `b`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_unused_arg", rendered);
}

#[test]
fn w0001_unused_arg_underscore() {
    let src = "fn f<F: Field>(instance a: F, instance _b: F) -> F { a }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("`_b`")),
        "expected no W0001 for `_b`, got: {:?}",
        warns
    );
}

// ── Snapshot: unused let binding ──

#[test]
fn w0001_unused_let_binding() {
    let src = "fn f<F: Field>(instance a: F) -> F { let x = a; a }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`x`"),
        "expected W0001 for `x`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_unused_let", rendered);
}

#[test]
fn w0001_used_let_binding() {
    let src = "fn f<F: Field>(instance a: F) -> F { let x = a; x }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("`x`")),
        "expected no W0001 for used `x`, got: {:?}",
        warns
    );
}

#[test]
fn w0001_unused_let_underscore() {
    let src = "fn f<F: Field>(instance a: F) -> F { let _x = a; a }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("`_x`")),
        "expected no W0001 for `_x`, got: {:?}",
        warns
    );
}

// ── Snapshot: dead computation ──

#[test]
fn w0001_dead_computation() {
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { a + b; a }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused computation"),
        "expected W0001 dead computation, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_dead_computation", rendered);
}

#[test]
fn w0001_dead_computation_assert_ok() {
    let src = "fn f<F: Field>(instance a: F) -> F { assert(a == a); a }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("unused computation")),
        "assert has side effects, got: {:?}",
        warns
    );
}

#[test]
fn w0001_dead_computation_app_ok() {
    // Function call may have side effects — not a dead computation.
    // Define a helper function and call it.
    let src = "\
fn g<F: Field>(instance a: F) -> F { a }
fn f<F: Field>(instance a: F) -> F { g(a); a }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("unused computation")),
        "function call may have side effects, got: {:?}",
        warns
    );
}

// ── Snapshot: unused map comprehension variable ──

#[test]
fn w0001_unused_map_var() {
    // Return type is [F; 3] to match the comprehension result.
    let src = "fn f<F: Field>(instance a: F) -> [F; 3] { [0 for x in 0..3] }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`x`"),
        "expected W0001 for unused map var `x`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_unused_map_var", rendered);
}

#[test]
fn w0001_unused_map_var_underscore() {
    let src = "fn f<F: Field>(instance a: F) -> [F; 3] { [0 for _x in 0..3] }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("`_x`")),
        "expected no W0001 for `_x`, got: {:?}",
        warns
    );
}

#[test]
fn w0001_used_map_var() {
    let src = "fn f<F: Field>(instance a: F) -> [F; 3] { [x for x in 0..3] }";
    let warns = warnings(src);
    assert!(
        !warns
            .iter()
            .any(|w| w.contains("unused variable") && w.contains("`x`")),
        "expected no W0001 for used map var, got: {:?}",
        warns
    );
}

// ── Snapshot: variable shadowing ──

#[test]
fn w0001_shadowed_let() {
    // Inner `let x = b` shadows outer `let x = a`.
    // Outer x is unused (shadowed), inner x is used.
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { let x = a; let x = b; x }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`x`"),
        "expected W0001 for shadowed outer `x`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_shadowed_let", rendered);
}

#[test]
fn w0001_shadowed_arg() {
    // `let a = b` shadows arg `a`. Arg `a` is unused (shadowed).
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { let a = b; a }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`a`"),
        "expected W0001 for shadowed arg `a`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_shadowed_arg", rendered);
}

// ── Snapshot: app function position uses variable ──

#[test]
fn w0001_app_function_position() {
    // `p(t)` — p is used in function position of App, should NOT warn.
    // p is a Poly so p(t) is valid application.
    let src = "fn f<F: Field, N: Size>(instance p: Poly<F, N>) -> F { let t = 0; p(t) }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("`p`")),
        "expected no W0001 for `p` used in App function position, got: {:?}",
        warns
    );
}

// ── Snapshot: unused let in relation ──

#[test]
fn w0001_unused_let_in_relation() {
    // `let x = a` in the where clause is unused — only `a == a` matters.
    let src = "proto p<F: Field>(instance a: F) where let x = a; a == a { }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`x`"),
        "expected W0001 for unused `x` in relation, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_unused_let_in_relation", rendered);
}

#[test]
fn w0001_unused_arg_in_relation() {
    // Arg `b` is unused in both relation and body.
    let src = "proto p<F: Field>(instance a: F, instance b: F) where a == a { }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`b`"),
        "expected W0001 for unused arg `b`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_unused_arg_in_relation", rendered);
}

// ── Regression tests ────────────────────────────────────────────────────

/// `let x = val; body` — x must NOT be in scope for val.
/// `let x = x` should not mark the outer `x` as used.
#[test]
fn w0001_let_self_ref_not_used() {
    // `let x = a; let x = x; x` — the second `let x = x` references the
    // first `x` (in val position, before the new scope). The first `x`
    // should be marked used by that reference, not by the final `x`.
    // Actually: `let x = x` — the `x` in val refers to the *outer* x.
    // So outer x IS used. But if we had `let x = a; x`, that's normal.
    // The real regression: `let x = a; let y = x; y` — x is used in
    // the val of the second let. Make sure no false positive for x.
    let src = "fn f<F: Field>(instance a: F) -> F { let x = a; let y = x; y }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("`x`")),
        "expected no W0001 for `x` used in val of inner let, got: {:?}",
        warns
    );
}

/// `let x = x` — the `x` in val should refer to an outer binding,
/// not the binding being introduced. If there's no outer `x`, it's
/// an undefined variable (not our concern), but if there IS an outer
/// `x`, it should be marked used.
#[test]
fn w0001_let_shadow_val_refers_outer() {
    // `let x = a; let x = x; x` — second let's val `x` refers to the
    // first `x` (outer scope), marking it used. The third `x` refers
    // to the second `x` (inner scope). So neither `x` is unused.
    let src = "fn f<F: Field>(instance a: F) -> F { let x = a; let x = x; x }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("unused variable")),
        "expected no W0001 — outer x used by val ref, inner x used by body, got: {:?}",
        warns
    );
}

/// `[body for x in iter]` — x must NOT be in scope for iter.
/// `[y for y in y]` — the iter `y` should refer to an outer binding,
/// not the comprehension variable being introduced.
#[test]
fn w0001_map_iter_not_in_scope() {
    // `let y = [a, a, a]; [y for y in y]` — the iter `y` refers to the
    // outer `let y`, marking it used. The body `y` refers to the
    // comprehension variable. So both are used.
    let src = "fn f<F: Field>(instance a: F) -> [F; 3] { let y = [a, a, a]; [y for y in y] }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("unused variable")),
        "expected no W0001 — outer y used by iter, comprehension y used by body, got: {:?}",
        warns
    );
}

/// Dead computation requires a continuation: `val; body` where val is
/// pure and discarded. `val` alone (no `;`) is the return value, not dead.
#[test]
fn w0001_dead_computation_no_cont_ok() {
    // `a + b` as the final expression — return value, not dead computation.
    let src = "fn f<F: Field>(instance a: F, instance b: F) -> F { a + b }";
    let rendered = render_warnings(src);
    assert!(
        !rendered.contains("unused computation"),
        "expected no W0001 — return value is not dead, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_dead_computation_no_cont_ok", rendered);
}

/// `x <- val; body` (Log) — x is in scope for body, not val.
/// `x <- x` should not mark an outer `x` as used by the binding itself.
#[test]
fn w0001_log_val_not_in_scope() {
    // `let x = a; x <- x; x` — the val `x` in `x <- x` refers to the
    // outer `let x`, marking it used. The body `x` refers to the log
    // binding. So both are used.
    let src = "fn f<F: Field>(instance a: F) -> F { let x = a; x <- x; x }";
    let warns = warnings(src);
    assert!(
        !warns.iter().any(|w| w.contains("unused variable")),
        "expected no W0001 — outer x used by log val, log x used by body, got: {:?}",
        warns
    );
}

/// Log binding unused in continuation: `x <- val; body` where x not in body.
#[test]
fn w0001_log_unused_binding() {
    // `x <- a; a` — x is bound by log but never used in the body.
    let src = "fn f<F: Field>(instance a: F) -> F { x <- a; a }";
    let rendered = render_warnings(src);
    assert!(
        rendered.contains("unused variable") && rendered.contains("`x`"),
        "expected W0001 for unused log binding `x`, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "w0001_log_unused_binding", rendered);
}
