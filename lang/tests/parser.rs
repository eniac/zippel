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

// ── Numeric literal domains ─────────────────────────────────────────────

/// Expression literals keep every digit; size positions take exactly the values that fit in
/// `usize` and report an error located at the literal beyond it.
#[test]
fn numeric_literal_domain_boundaries() {
    use lang::diagnostic::Phase;
    use lang::parser::parse_decls;
    use num::BigUint;

    let parses = |src: &str| {
        let (decls, diags) = parse_decls(src);
        assert!(
            diags.is_empty(),
            "unexpected diagnostics for `{src}`: {diags:?}"
        );
        decls
    };
    for digits in ["34545435435435435435435", "4294967296"] {
        let decls = parses(&format!("fn f<F: Field>() -> F {{ {digits} }}"));
        let shown = decls[0].node.to_string();
        assert!(shown.contains(&format!("{{ {digits} }}")), "{shown}");
    }
    // A size above `u32::MAX` is still a valid 64-bit shape.
    if usize::BITS == 64 {
        parses("fn f<F: Field>(instance xs: [F; 4294967296]) -> F { xs[0] }");
    }
    parses("fn f<K: 7, F: Field>() -> F { 1 }");

    let too_big = (BigUint::from(usize::MAX) + 1u8).to_string();
    for src in [
        format!("fn f<F: Field>(instance xs: [F; {too_big}]) -> F {{ xs[0] }}"),
        format!("fn f<K: {too_big}, F: Field>() -> F {{ 1 }}"),
    ] {
        let (_, diags) = parse_decls(&src);
        let start = src.find(&too_big).unwrap();
        assert!(
            diags.iter().any(|d| d.phase == Phase::Parse
                && d.span == (start..start + too_big.len())
                && d.summary == "size literal exceeds target usize range"),
            "`{src}`: {diags:?}"
        );
    }
}
