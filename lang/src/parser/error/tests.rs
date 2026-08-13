//! Parser error tests.

use super::super::parse_decls;
use super::*;
use crate::diagnostic::{render_diagnostic, Diagnostic};

// ── Render tests ───────────────────────────────────────────────────

#[test]
fn render_shows_line_col() {
    let src = "fn f<F: Field>(instance a: F) -> F {\n    a +\n}\n";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let e = &errors[0];
    // Error points to `}` on line 3 — the parser expected
    // an expression after `+` but found `}`.
    let diag = Diagnostic::from(e.clone());
    let rendered = render_diagnostic(&diag, "test.zippel", src);
    eprintln!("--- error render ---\n{}", rendered);
    // ariadne output includes line numbers, source context, and carets
    assert!(rendered.contains("3:"), "rendered: {}", rendered);
    assert!(rendered.contains("}"), "rendered: {}", rendered);
    assert!(rendered.contains("found"), "rendered: {}", rendered);
    // Should have user-friendly summary and context labels
    assert!(rendered.contains("error:"), "rendered: {}", rendered);
    assert!(rendered.contains("unexpected"), "rendered: {}", rendered);
    assert!(rendered.contains("while parsing"), "rendered: {}", rendered);
}

#[test]
fn render_missing_rparen() {
    let src = "fn f<F: Field>(instance a: F -> F { a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let e = &errors[0];
    let diag = Diagnostic::from(e.clone());
    let rendered = render_diagnostic(&diag, "test.zippel", src);
    eprintln!("--- error render ---\n{}", rendered);
    // Should show `->` as found, and `,` `)` as expected
    assert!(rendered.contains("->"), "rendered: {}", rendered);
    assert!(rendered.contains("expected"), "rendered: {}", rendered);
    assert!(rendered.contains("')'"), "rendered: {}", rendered);
    assert!(rendered.contains("','"), "rendered: {}", rendered);
    // Should have context label
    assert!(rendered.contains("while parsing"), "rendered: {}", rendered);
}

#[test]
fn render_duplicate_decl() {
    use crate::ast::module::UModule;
    use crate::diagnostic::{render_diagnostic, Diagnostic};
    let src = "fn f<F: Field>(instance a: F) -> F { a }\nfn f<F: Field>(instance a: F) -> F { a }";
    let (_, diags) = UModule::parse(src);
    let diag: &Diagnostic = diags
        .iter()
        .find(|d| d.summary.contains("duplicate"))
        .expect("should find duplicate declaration diagnostic");
    let rendered = render_diagnostic(diag, "test.zippel", src);
    eprintln!("--- error render ---\n{}", rendered);
    // Error should point to the second declaration (line 2)
    assert!(rendered.contains("2:"), "rendered: {}", rendered);
    assert!(rendered.contains("duplicate"), "rendered: {}", rendered);
    assert!(rendered.contains("first defined"), "rendered: {}", rendered);
    // Should show user-friendly declaration description
    assert!(rendered.contains("fn f("), "rendered: {}", rendered);
}

// ── Help message tests ─────────────────────────────────────────────
// Each test parses a source with a common mistake and checks that
// the appropriate help tip is generated.

fn assert_help(src: &str, expected_help: &str) {
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty(), "expected parse error for: {src}");
    let help = errors
        .iter()
        .find_map(|e| e.suggestions.first().map(|s| s.message.as_str()))
        .unwrap_or_else(|| {
            panic!(
                "no suggestion found for: {src}\nerrors: {:?}",
                errors.iter().map(|e| &e.suggestions).collect::<Vec<_>>()
            )
        });
    assert!(
        help.contains(expected_help),
        "help \"{help}\" does not contain \"{expected_help}\""
    );
}

#[test]
fn help_where_missing_eq() {
    // `where random<F>;` — missing `==` constraint
    assert_help(
        "proto p<F: Field>(instance a: F) where random<F>; { () }",
        "where clause constraints use `==`",
    );
}

#[test]
fn help_where_using_single_eq() {
    // `where a = b` — should be `==`
    assert_help(
        "proto p<F: Field>(instance a: F) where a = b { () }",
        "use `==` for equality",
    );
}

#[test]
fn help_missing_rangle_in_generics() {
    // `proto p<F: Field(` — missing `>` before `(`
    assert_help(
        "proto p<F: Field(instance a: F) where a == a { () }",
        "missing `>` to close generic",
    );
}

#[test]
fn help_missing_rparen_in_args() {
    // `proto p<F: Field>(instance a: F {` — missing `)` before `{`
    assert_help(
        "proto p<F: Field>(instance a: F { () }",
        "missing `)` to close argument list",
    );
}

#[test]
fn help_missing_rbrace_in_body() {
    // `... { ()` — missing `}` at end of input
    assert_help(
        "proto p<F: Field>(instance a: F) where a == a { ()",
        "missing `}` to close declaration body",
    );
}

#[test]
fn help_missing_semi_between_where_constraints() {
    // `where a == b c == d` — missing `;` between constraints
    assert_help(
        "proto p<F: Field>(instance a: F) where a == b c == d { () }",
        "missing `;` after expression",
    );
}

#[test]
fn help_missing_type_in_arg() {
    // `fn f<F: Field>(instance a: )` — missing type after `:`
    assert_help(
        "fn f<F: Field>(instance a: ) -> F { a }",
        "expected a type after `:`",
    );
}

#[test]
fn help_missing_kind_in_tvar() {
    // `proto p<N: >` — missing kind after `:`
    assert_help(
        "proto p<N: >(instance a: F) where a == a { a }",
        "expected a kind after `:`",
    );
}

#[test]
fn help_incomplete_range() {
    // `0..]` — range needs an end bound
    assert_help(
        "proto p<N: Size>(instance a: F) where a == [a for i in 0..] { a }",
        "range needs an end bound",
    );
}

#[test]
fn help_missing_in_in_comprehension() {
    // `[a for x 0..N]` — missing `in`
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { [a for x 0..N] }",
        "missing `in` keyword in list comprehension",
    );
}

#[test]
fn help_missing_for_in_comprehension() {
    // `[a x in 0..N]` — missing `for`
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { [a x in 0..N] }",
        "missing `for` keyword in list comprehension",
    );
}

#[test]
fn help_none_for_valid_parse() {
    // Valid input should produce no help tips
    let src = "fn f<F: Field>(instance a: F) -> F { a }";
    let (_, errors) = parse_decls(src);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
}

#[test]
fn help_none_for_generic_error() {
    // An error that doesn't match any help pattern should have no help
    let src = "fn f<F: Field>(instance a: F) -> F {\n    a +\n}\n";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            e.suggestions.is_empty(),
            "unexpected suggestions: {:?}",
            e.suggestions
        );
    }
}

// ── New help patterns ──────────────────────────────────────────────

#[test]
fn help_lambda_arrow_not_fatarrow() {
    // `fun(x) -> x` — should use `=>` not `->`
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { fun(x) -> x + 1 }",
        "lambda expressions use `=>` (not `->`)",
    );
}

#[test]
fn help_missing_arrow_before_return_type() {
    // `fn f(...) F { a }` — missing `->` before return type
    assert_help(
        "fn f<F: Field>(instance a: F) F { a }",
        "missing `->` before return type",
    );
}

#[test]
fn help_fn_eq_not_arrow() {
    // `fn f(...) = F { a }` — should use `->` not `=`
    assert_help(
        "fn f<F: Field>(instance a: F) = F { a }",
        "use `->` before return type (not `=`)",
    );
}

#[test]
fn help_proto_with_return_type() {
    // `proto p(...) -> F where ...` — proto has no return type
    assert_help(
        "proto p<F: Field>(instance a: F) -> F where a == a { () }",
        "proto declarations don't have return types",
    );
}

#[test]
fn help_vector_comma_not_semi() {
    // `[F, N]` — vector type uses `;` not `,`
    assert_help(
        "fn f<F: Field>(instance a: [F, N]) -> F { a }",
        "vector types use `;`",
    );
}

#[test]
fn help_missing_colon_in_arg() {
    // `instance a F` — missing `:` after argument name
    assert_help(
        "fn f<F: Field>(instance a F) -> F { a }",
        "missing `:` after argument name",
    );
}

#[test]
fn help_proto_missing_where() {
    // `proto p(...) a == b { }` — missing `where` keyword
    assert_help(
        "proto p<F: Field>(instance a: F) a == b { () }",
        "missing `where` keyword before constraints",
    );
}

#[test]
fn help_record_semi_not_comma() {
    // `{| x: a; y: b |}` — record values use `,` not `;`
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { {| x: a; y: b |} }",
        "record values use `,` between fields (not `;`)",
    );
}

// ── False-positive regression tests ────────────────────────────────

#[test]
fn help_assert_eq_not_where_specific() {
    // `assert(a = b)` — should give generic `==` advice, not where-clause-specific
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { assert(a = b) }",
        "use `==` for equality",
    );
}

#[test]
fn help_let_missing_semi_not_where_specific() {
    // `let x = a x` — should give generic `;` advice, not where-clause-specific
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { let x = a x }",
        "missing `;` after expression",
    );
}

// ── Round 2: new patterns from subagent search ─────────────────────

#[test]
fn help_missing_langle_to_open_generics() {
    // `fn f F: Field>(...)` — missing `<` to open generics
    assert_help(
        "fn f F: Field>(instance a: F) -> F { a }",
        "missing `<` to open generic type parameters",
    );
}

#[test]
fn help_missing_lparen_to_open_args() {
    // `fn f<F: Field> instance a: F)` — missing `(` to open arg list
    assert_help(
        "fn f<F: Field> instance a: F) -> F { a }",
        "missing `(` to open argument list",
    );
}

#[test]
fn help_record_type_semi_not_comma() {
    // `{ x: F; y: F }` — record type uses `,` not `;`
    assert_help(
        "fn f<F: Field>(instance a: F) -> { x: F; y: F } { a }",
        "record types use `,` between fields (not `;`)",
    );
}

#[test]
fn help_record_type_missing_colon_no_false_positive() {
    // `{ x F, y F }` — record type missing `:` should NOT trigger
    // "missing `:` after argument name" (that's for args, not record types)
    let src = "fn f<F: Field>(instance a: F) -> { x F, y F } { a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            !e.suggestions
                .first()
                .map(|s| s.message.as_str())
                .unwrap_or("")
                .contains("argument name"),
            "false positive: {:?}",
            e.suggestions
        );
    }
}

// ── Round 2: new patterns ──────────────────────────────────────────

#[test]
fn help_type_alias_colon_not_eq() {
    // `type MyAlias: F;` — should use `=` not `:`
    assert_help("type MyAlias: F;", "type aliases use `=` (not `:`)");
}

#[test]
fn help_type_alias_missing_semi() {
    // `type MyAlias = F` — missing `;` at end
    assert_help("type MyAlias = F", "missing `;` at end of declaration");
}

#[test]
fn help_pairing_missing_comma() {
    // `Pairing<G H>` — missing `,` between type params
    assert_help(
        "fn f<F: Field, P: Pairing<G H>>(instance a: F) -> F { a }",
        "missing `,` between type parameters",
    );
}

// ── Round 2: false-positive regressions ────────────────────────────

#[test]
fn help_let_binding_no_arg_name_false_positive() {
    // `let x a;` — should NOT trigger "missing `:` after argument name"
    // (let bindings expect `:` or `=`, args expect only `:`)
    let src = "fn f<F: Field>(instance a: F) -> F { let x a; x }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            !e.suggestions
                .first()
                .map(|s| s.message.as_str())
                .unwrap_or("")
                .contains("argument name"),
            "false positive: {:?}",
            e.suggestions
        );
    }
}

#[test]
fn help_poly_missing_paren_no_arg_list_false_positive() {
    // `poly a` — should NOT trigger "missing `(` to open argument list"
    // (that's for declaration-level args, not expression-level function calls)
    let src = "fn f<F: Field>(instance a: F) -> F { poly a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            !e.suggestions
                .first()
                .map(|s| s.message.as_str())
                .unwrap_or("")
                .contains("argument list"),
            "false positive: {:?}",
            e.suggestions
        );
    }
}

#[test]
fn help_eval_no_generic_false_positive() {
    // `eval a` — should NOT trigger "missing `<` to open generic type parameters"
    // (that's for declaration-level generics, not expression-level eval)
    let src = "fn f<F: Field>(instance a: F) -> F { eval a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            !e.suggestions
                .first()
                .map(|s| s.message.as_str())
                .unwrap_or("")
                .contains("generic type parameters"),
            "false positive: {:?}",
            e.suggestions
        );
    }
}

// ── Round 3: new patterns ──────────────────────────────────────────

#[test]
fn help_let_missing_eq() {
    // `let x: F a;` — missing `=` before value
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { let x: F a; x }",
        "missing `=` in assignment",
    );
}

#[test]
fn help_type_alias_missing_eq() {
    // `type MyAlias F;` — missing `=` in type alias
    assert_help("type MyAlias F;", "missing `=` in assignment");
}

#[test]
fn help_vector_colon_not_semi() {
    // `[F: N]` — vector type uses `;` not `:`
    assert_help(
        "fn f<F: Field>(instance a: [F: N]) -> F { a }",
        "vector types use `;`",
    );
}

#[test]
fn help_reduce_semi_not_comma() {
    // `reduce(+; [a, b])` — should use `,` not `;`
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { reduce(+; [a, b]) }",
        "use `,` between arguments (not `;`)",
    );
}

// ── Round 3: false-positive regression ─────────────────────────────

#[test]
fn help_fin_no_arg_list_false_positive() {
    // `Fin<0 N>` — should NOT trigger "missing `(` to open argument list"
    let src = "fn f<F: Field, V: Fin<0 N>>(instance a: F) -> F { a }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    for e in &errors {
        assert!(
            !e.suggestions
                .first()
                .map(|s| s.message.as_str())
                .unwrap_or("")
                .contains("argument list"),
            "false positive: {:?}",
            e.suggestions
        );
    }
}

// ── Round 4: new patterns ──────────────────────────────────────────

#[test]
fn help_assert_missing_paren() {
    // `assert a == b` — missing `(` after assert
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { assert a == b }",
        "missing `(` after keyword",
    );
}

// ── Round 5: new patterns ──────────────────────────────────────────

#[test]
fn help_fn_fatarrow_not_arrow() {
    // `fn f(...) => F { a }` — should use `->` not `=>`
    assert_help(
        "fn f<F: Field>(instance a: F) => F { a }",
        "function return types use `->` (not `=>`)",
    );
}

#[test]
fn help_let_eqeq_not_eq() {
    // `let x == a;` — should use `=` not `==`
    assert_help(
        "fn f<F: Field>(instance a: F) -> F { let x == a; x }",
        "assignments use `=` (not `==`)",
    );
}

#[test]
fn help_tvar_eq_not_colon() {
    // `fn f<F = Field>(...)` — should use `:` not `=`
    assert_help(
        "fn f<F = Field>(instance a: F) -> F { a }",
        "type variables use `:` (not `=`)",
    );
}

// ── Did-you-mean keyword suggestion tests ──────────────────────────
// Suggestions appear in the error label (not the help tip) and only
// when the suggested keyword is NOT already in the expected list.

/// Helper: parse and return the label message from the first error.
fn label_of(src: &str) -> String {
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty(), "expected parse error for: {src}");
    error_label_msg(&errors[0])
}

#[test]
fn did_you_mean_for() {
    // `fro` is close to `for`. The expected list is long (operators + `]` + `for`),
    // so summarize_expected produces a generic "an operator or ']'" message.
    // The suggestion replaces the generic "expected" with a specific keyword.
    let label = label_of("fn f<F: Field>(instance a: F) -> F { [a fro x in 0..N] }");
    assert!(
        label.contains("similar name: `for`"),
        "expected suggestion in label: {label}"
    );
    assert!(
        !label.contains("expected"),
        "should not include generic 'expected' when suggestion is present: {label}"
    );
}

#[test]
fn context_label_shows_innermost() {
    // Error inside expression inside declaration should show the
    // innermost context ("while parsing this expression").
    // The From<ParseError> impl shows up to 2 context levels.
    let src = "fn f<F: Field>(instance a: F) -> F { [a fro x in 0..N] }";
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty());
    let rendered = render_diagnostic(&Diagnostic::from(errors[0].clone()), "test.zp", src);
    assert!(
        rendered.contains("while parsing this expression"),
        "should show innermost context: {rendered}"
    );
}

#[test]
fn did_you_mean_no_duplicate_when_keyword_expected() {
    // `wher` is close to `where`, and `where` IS in the expected list.
    // The error already says "expected 'where'", so no suggestion.
    let label = label_of("proto p<F: Field>(instance a: F) wher a == a { () }");
    assert!(
        !label.contains("similar name"),
        "should not suggest when keyword already expected: {label}"
    );
    // But the pattern-based help should still fire.
    let (_, errors) = parse_decls("proto p<F: Field>(instance a: F) wher a == a { () }");
    assert!(
        errors.iter().any(|e| e
            .suggestions
            .first()
            .map(|s| s.message.as_str())
            .unwrap_or("")
            .contains("missing `where` keyword")),
        "pattern help should still fire"
    );
}

#[test]
fn did_you_mean_no_suggestion_for_unrelated() {
    // `qqqq` is not close to any keyword — no suggestion in label.
    let label = label_of("proto p<F: Field>(instance a: F) qqqq a == a { () }");
    assert!(
        !label.contains("similar name"),
        "should not suggest for unrelated identifier: {label}"
    );
}

// ── summarize_expected tests ──────────────────────────────────────

/// Helper: parse a source and return the summary string from the first error.
fn summary_of(src: &str) -> String {
    let (_, errors) = parse_decls(src);
    assert!(!errors.is_empty(), "expected parse error for: {src}");
    summarize_expected(&errors[0].expected, &errors[0].contexts)
}

#[test]
fn summary_expression_atom_start() {
    // `a +` — after operator, expects expression atoms (17 tokens)
    let s = summary_of("fn f<F: Field>(instance a: F) -> F { a + }");
    assert!(s.contains("an expression"), "got: {s}");
}

#[test]
fn summary_expression_operator_continuation() {
    // `f(a` — after arg, expects operators + ')'
    let s = summary_of("fn f<F: Field>(instance a: F) -> F { f(a }");
    assert!(s.contains("an operator"), "got: {s}");
    assert!(s.contains("')'"), "got: {s}");
}

#[test]
fn summary_expression_with_closer() {
    // `[a, b` — vector literal, expects operators + ']'
    let s = summary_of("fn f<F: Field>(instance a: F) -> F { [a, b }");
    assert!(
        s.contains("an operator") || s.contains("an expression"),
        "got: {s}"
    );
    assert!(s.contains("']'"), "got: {s}");
}

#[test]
fn summary_type_annotation() {
    // `(instance a: )` — after `:`, expects type tokens (7 tokens)
    let s = summary_of("fn f<F: Field>(instance a: ) -> F { a }");
    assert_eq!(s, "a type", "got: {s}");
}

#[test]
fn summary_kind_annotation() {
    // `fn f<N: >` — after `:` in generic params, expects kind tokens (6 tokens)
    let s = summary_of("fn f<N: >(instance a: F) -> F { a }");
    assert_eq!(s, "a kind annotation", "got: {s}");
}

#[test]
fn summary_where_clause_operators() {
    // `where random<F>;` — expects operators + '=='
    let s = summary_of("proto p<F: Field>(instance a: F) where random<F>; { }");
    assert!(s.contains("'=='"), "got: {s}");
    assert!(s.contains("an operator"), "got: {s}");
}

#[test]
fn summary_short_listed_directly() {
    // `fn f<F: Field G: Group>` — expects `,` and `>` (2 tokens)
    let s = summary_of("fn f<F: Field G: Group>(instance a: F) -> F { a }");
    // Short lists (≤3) are listed directly, not categorized
    assert!(s.contains("','"), "got: {s}");
    assert!(s.contains("'>'"), "got: {s}");
}

#[test]
fn summary_single_token() {
    // `type X = F` — expects just `;`
    let s = summary_of("type X = F");
    assert_eq!(s, "';'", "got: {s}");
}

#[test]
fn summary_empty() {
    // Custom errors have empty expected
    let s = summarize_expected(&[], &[]);
    assert_eq!(s, "something else");
}

#[test]
fn summary_expression_no_context_fallback() {
    // `let x = ;` — expects expression atoms but no Expression context
    // (error occurs before entering exp_no_seq_parser)
    let s = summary_of("fn f<F: Field>(instance a: F) -> F { let x = ; x }");
    // No Expression context → fallback to listing tokens
    // Should still be readable (list or truncate)
    assert!(!s.is_empty(), "got: {s}");
}
