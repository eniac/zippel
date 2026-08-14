//! Parser error snapshot tests.
//!
//! Each test parses a source with a common parse error and snapshots the
//! rendered diagnostic output. Snapshots live in `snapshots/parser/`.

mod common;

use common::{assert_snap, render_all};
use lang::ast::module::UModule;

const SNAP_DIR: &str = "snapshots/parser";

// ── Existing parse error snapshots ──────────────────────────────────────

#[test]
fn parse_error_missing_typevar_name() {
    let rendered = render_all("fn f<: Field>(instance a: F) -> F { a }");
    assert!(!rendered.is_empty(), "expected parse error");
    assert_snap!(SNAP_DIR, "parse_error_missing_typevar_name", rendered);
}

#[test]
fn parse_error_recovery_multiple() {
    let src = "fn f<: Field>(instance a: F) -> F { a }\n\
               fn g<F: Field>(instance a: F) -> F { a }\n\
               fn h<: Field>(instance a: F) -> F { a }";
    let rendered = render_all(src);
    let (module, _) = UModule::parse(src);
    assert!(module.is_some(), "expected module to be built");
    assert_snap!(SNAP_DIR, "parse_error_recovery_multiple", rendered);
}

// ── New parse error snapshots ───────────────────────────────────────────

#[test]
fn parse_error_expression_boundary() {
    // `;` at the start of an expression — chumsky labels this "expression".
    let rendered = render_all("fn f<F: Field>(instance a: F) -> F { ; }");
    assert_snap!(SNAP_DIR, "parse_error_expression_boundary", rendered);
}

#[test]
fn parse_error_expression_interior() {
    // `a +` then `}` — interior failure retains raw expected patterns.
    let rendered = render_all("fn f<F: Field>(instance a: F) -> F { a + }");
    assert_snap!(SNAP_DIR, "parse_error_expression_interior", rendered);
}

#[test]
fn parse_error_type_boundary() {
    // `)` where a type is expected — chumsky labels this "type".
    let rendered = render_all("fn f<F: Field>(instance a: ) -> F { a }");
    assert_snap!(SNAP_DIR, "parse_error_type_boundary", rendered);
}

#[test]
fn parse_error_missing_rparen() {
    // Missing `)` before `->` in argument list.
    let rendered = render_all("fn f<F: Field>(instance a: F -> F { a }");
    assert_snap!(SNAP_DIR, "parse_error_missing_rparen", rendered);
}

#[test]
fn parse_error_missing_rbrace() {
    // Missing `}` at end of declaration body.
    let rendered = render_all("fn f<F: Field>(instance a: F) -> F { a");
    assert_snap!(SNAP_DIR, "parse_error_missing_rbrace", rendered);
}

#[test]
fn parse_error_missing_kind_in_tvar() {
    // `proto p<N: >` — missing kind after `:` in generic params.
    let rendered = render_all("proto p<N: >(instance a: F) where a == a { a }");
    assert_snap!(SNAP_DIR, "parse_error_missing_kind_in_tvar", rendered);
}

#[test]
fn parse_error_unexpected_token_after_fn() {
    // `fn f F: Field>` — missing `<` to open generics.
    let rendered = render_all("fn f F: Field>(instance a: F) -> F { a }");
    assert_snap!(SNAP_DIR, "parse_error_unexpected_token_after_fn", rendered);
}

#[test]
fn parse_error_missing_semi_in_where() {
    // `where a == b c == d` — missing `;` between where constraints.
    let rendered = render_all("proto p<F: Field>(instance a: F) where a == b c == d { () }");
    assert_snap!(SNAP_DIR, "parse_error_missing_semi_in_where", rendered);
}

#[test]
fn parse_error_type_alias_missing_eq() {
    // `type MyAlias F;` — missing `=` in type alias.
    let rendered = render_all("type MyAlias F;");
    assert_snap!(SNAP_DIR, "parse_error_type_alias_missing_eq", rendered);
}

#[test]
fn parse_error_type_alias_missing_semi() {
    // `type MyAlias = F` — missing `;` at end.
    let rendered = render_all("type MyAlias = F");
    assert_snap!(SNAP_DIR, "parse_error_type_alias_missing_semi", rendered);
}
