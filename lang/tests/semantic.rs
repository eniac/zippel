//! Semantic error snapshot and assertion tests.
//!
//! Snapshot tests render the full diagnostic output and compare against
//! insta snapshots in `snapshots/semantic/`. Assertion tests verify the
//! presence/absence of a specific error condition without snapshotting.

mod common;

use common::{assert_snap, render_all};
use lang::ast::module::UModule;
use lang::diagnostic::{Phase, Severity};

const SNAP_DIR: &str = "snapshots/semantic";

// ── Semantic errors (snapshot) ──────────────────────────────────────────

#[test]
fn semantic_undefined_variable() {
    let rendered = render_all("proto p<F: Field>(instance a: F) where a == b { }");
    assert!(
        rendered.contains("undefined variable"),
        "expected semantic error for undefined variable `b`"
    );
    assert_snap!(SNAP_DIR, "undefined_variable", rendered);
}

#[test]
fn semantic_type_alias_cycle() {
    let rendered = render_all("type A = B;\ntype B = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error"
    );
    assert_snap!(SNAP_DIR, "type_alias_cycle", rendered);
}

#[test]
fn semantic_type_alias_cycle_three() {
    let rendered = render_all("type A = B;\ntype B = C;\ntype C = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error"
    );
    assert_snap!(SNAP_DIR, "type_alias_cycle_three", rendered);
}

#[test]
fn semantic_type_alias_self_ref() {
    let rendered = render_all("type A = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error for self-referential alias"
    );
    assert_snap!(SNAP_DIR, "type_alias_self_ref", rendered);
}

#[test]
fn semantic_unbound_size_var() {
    // N is used in the type [F; N] but not declared in the typevar list.
    let rendered = render_all("proto p<F: Field>(instance a: [F; N]) where a == a { }");
    assert!(
        rendered.contains("unbound size variable"),
        "expected unbound size variable error"
    );
    assert_snap!(SNAP_DIR, "unbound_size_var", rendered);
}

#[test]
fn semantic_pairing_refs_non_group() {
    // Pairing<F, F> is invalid — F is Field, not Group.
    let src = "proto p<F: Field, P: Pairing<F, F>>(instance a: F) where a == a { }";
    let rendered = render_all(src);
    assert!(
        rendered.contains("`F` is not a Group"),
        "expected invalid group ref error, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "pairing_refs_non_group", rendered);
}

#[test]
fn semantic_unresolved_group_ref() {
    // Pairing<G, H> where G and H are not declared at all.
    let src = "proto p<P: Pairing<G, H>>(instance a: F) where a == a { }";
    let rendered = render_all(src);
    assert!(
        rendered.contains("unresolved group reference"),
        "expected unresolved group reference error, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "unresolved_group_ref", rendered);
}

#[test]
fn semantic_invalid_range_bounds() {
    // Range 10..5 has start > end.
    let rendered = render_all("proto p<N: 10..5>(instance a: [F; N]) where a == a { }");
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
    let src = "proto p<F: Field>(instance a: F, instance b: F) where a == verify(b == b) { }";
    let rendered = render_all(src);
    assert!(
        rendered.contains("impure"),
        "expected impure relation error for verify in where clause, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "impure_verify_in_where", rendered);
}

#[test]
fn semantic_circular_typevar_ref() {
    // V: Pairing<G> and G: Pairing<V> — circular kind reference.
    let src = "proto p<V: Pairing<G, G>, G: Pairing<V, V>>(instance a: V) where a == a { }";
    let rendered = render_all(src);
    assert!(
        rendered.contains("circular type variable reference"),
        "expected circular typevar ref error, got: {rendered}"
    );
    assert_snap!(SNAP_DIR, "circular_typevar_ref", rendered);
}

#[test]
fn semantic_undefined_variable_repeated() {
    // `b` used twice — should merge into one error with "also used here".
    let rendered = render_all("proto p<F: Field>(instance a: F) where b == b { }");
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
    let rendered =
        render_all("proto p<F: Field>(instance a: [F; N], instance b: [F; N]) where a == a { }");
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
    let rendered =
        render_all("proto p<F: Field, F: Group, F: Field>(instance a: F) where a == a { }");
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
    let src = "proto p<F: Field>(instance a: F) where a == a { }";
    let (_, diags) = UModule::parse(src);
    let sem_diags: Vec<_> = diags
        .iter()
        .filter(|d| d.phase == Phase::Semantic)
        .collect();
    assert!(
        sem_diags.is_empty(),
        "expected no semantic errors, got: {:?}",
        sem_diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn semantic_let_binding_in_scope() {
    let src = "proto p<F: Field>(instance a: F) where let x = a; x == a { }";
    let (_, diags) = UModule::parse(src);
    let sem_diags: Vec<_> = diags
        .iter()
        .filter(|d| d.phase == Phase::Semantic)
        .collect();
    assert!(
        sem_diags.is_empty(),
        "expected no semantic errors for let-bound variable, got: {:?}",
        sem_diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
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

// ── Valid programs (assertion only) ─────────────────────────────────────

#[test]
fn valid_program_no_errors() {
    let src = "proto p<F: Field>(instance a: F) where a == a { }";
    let (_, diags) = UModule::parse(src);
    assert!(
        diags.is_empty(),
        "expected no diagnostics for valid program, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}

#[test]
fn valid_program_with_let() {
    let src = "proto p<F: Field>(instance a: F) where\n\
               let x = a;\n\
               let y = x;\n\
               y == a\n\
               { }";
    let (_, diags) = UModule::parse(src);
    assert!(
        diags.is_empty(),
        "expected no diagnostics, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
    );
}
