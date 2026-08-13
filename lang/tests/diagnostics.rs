//! Integration tests for the diagnostic system.
//!
//! Tests are split into two categories:
//!
//! - **Snapshot tests**: Render the full diagnostic output (source context,
//!   labels, suggestions) and compare against insta snapshots. These catch
//!   visual regressions in diagnostic formatting. Use `assert_snap!`.
//! - **Assertion tests**: Verify the presence/absence of a specific error
//!   condition without snapshotting the rendered output. These are smoke
//!   tests for error detection logic, not formatting.
//!
//! Snapshot files are stored in `lang/tests/snapshots/diagnostics/` with
//! descriptive names (e.g. `undefined_variable.snap`), following the same
//! convention as `analyses/tests/snapshots/gb_snapshots/`.

use lang::ast::module::UModule;
use lang::diagnostic::render_diagnostic;

/// Snapshot directory (relative to the test file's location in `lang/tests/`).
const SNAP_DIR: &str = "snapshots/diagnostics";

/// Render all diagnostics for a source string, sorted by span.
/// Disables ANSI colors for clean snapshot text.
fn render_all(src: &str) -> String {
    yansi::disable();
    let (_, diags) = UModule::parse(src);
    diags
        .iter()
        .map(|d| render_diagnostic(d, "test.zippel", src))
        .collect::<Vec<_>>()
        .join("\n---\n")
}

/// Assert a named snapshot in `SNAP_DIR` without the `expression:` header.
/// Follows the gb_snapshots convention: descriptive file names, no
/// test-file prefix.
macro_rules! assert_snap {
    ($name:expr, $value:expr) => {{
        let mut settings = insta::Settings::clone_current();
        settings.set_snapshot_path(SNAP_DIR);
        settings.set_prepend_module_to_snapshot(false);
        settings.set_omit_expression(true);
        settings.bind(|| insta::assert_snapshot!($name, $value));
    }};
}

// ── Parse errors (snapshot) ────────────────────────────────────────────

#[test]
fn parse_error_missing_typevar_name() {
    let rendered = render_all("fn f<: Field>(instance a: F) -> F { a }");
    assert!(!rendered.is_empty(), "expected parse error");
    assert_snap!("parse_error_missing_typevar_name", rendered);
}

#[test]
fn parse_error_recovery_multiple() {
    let src = "fn f<: Field>(instance a: F) -> F { a }\n\
               fn g<F: Field>(instance a: F) -> F { a }\n\
               fn h<: Field>(instance a: F) -> F { a }";
    let rendered = render_all(src);
    let (module, _) = UModule::parse(src);
    assert!(module.is_some(), "expected module to be built");
    assert_snap!("parse_error_recovery_multiple", rendered);
}

// ── Semantic errors (snapshot) ─────────────────────────────────────────

#[test]
fn semantic_undefined_variable() {
    let rendered = render_all("proto p<F: Field>(instance a: F) where a == b { }");
    assert!(
        rendered.contains("undefined variable"),
        "expected semantic error for undefined variable `b`"
    );
    assert_snap!("undefined_variable", rendered);
}

#[test]
fn semantic_type_alias_cycle() {
    let rendered = render_all("type A = B;\ntype B = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error"
    );
    assert_snap!("type_alias_cycle", rendered);
}

#[test]
fn semantic_type_alias_cycle_three() {
    let rendered = render_all("type A = B;\ntype B = C;\ntype C = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error"
    );
    assert_snap!("type_alias_cycle_three", rendered);
}

#[test]
fn semantic_type_alias_self_ref() {
    let rendered = render_all("type A = A;");
    assert!(
        rendered.contains("circular type alias"),
        "expected circular type alias error for self-referential alias"
    );
    assert_snap!("type_alias_self_ref", rendered);
}

#[test]
fn semantic_unbound_size_var() {
    // N is used in the type [F; N] but not declared in the typevar list.
    let rendered = render_all("proto p<F: Field>(instance a: [F; N]) where a == a { }");
    assert!(
        rendered.contains("unbound size variable"),
        "expected unbound size variable error"
    );
    assert_snap!("unbound_size_var", rendered);
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
    assert_snap!("pairing_refs_non_group", rendered);
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
    assert_snap!("unresolved_group_ref", rendered);
}

#[test]
fn semantic_invalid_range_bounds() {
    // Range 10..5 has start > end.
    let rendered = render_all("proto p<N: 10..5>(instance a: [F; N]) where a == a { }");
    assert!(
        rendered.contains("invalid range bounds"),
        "expected invalid range bounds error"
    );
    assert_snap!("invalid_range_bounds", rendered);
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
    assert_snap!("impure_verify_in_where", rendered);
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
    assert_snap!("circular_typevar_ref", rendered);
}

// ── Semantic errors (assertion only) ───────────────────────────────────

#[test]
fn semantic_defined_variable_ok() {
    let src = "proto p<F: Field>(instance a: F) where a == a { }";
    let (_, diags) = UModule::parse(src);
    let sem_diags: Vec<_> = diags
        .iter()
        .filter(|d| d.phase == lang::diagnostic::Phase::Semantic)
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
        .filter(|d| d.phase == lang::diagnostic::Phase::Semantic)
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
        .filter(|d| d.phase == lang::diagnostic::Phase::Semantic)
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
    let has_no_proto = diags
        .iter()
        .any(|d| d.summary.contains("no proto declaration"));
    assert!(
        has_no_proto,
        "expected 'no proto declaration' error, got: {:?}",
        diags.iter().map(|d| &d.summary).collect::<Vec<_>>()
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

// ── Valid programs (assertion only) ────────────────────────────────────

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
