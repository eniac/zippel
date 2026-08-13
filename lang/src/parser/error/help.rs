//! Pattern-based help detection for common parse errors.
//!
//! Each pattern checks `found`, `expected`, and `contexts` to identify a
//! likely user mistake. Returns structured `Suggestion` values with span,
//! replacement text, and applicability level — enabling future `--fix`
//! tooling.

use std::ops::Range;

use super::super::label::Context;
use super::super::lexer::Token;
use super::{Expected, TokenExt};
use crate::diagnostic::{hint, insert_before, replace, Suggestion};

/// Detect common error patterns and generate structured suggestions.
pub(super) fn detect_help(
    found: &Option<Token<'static>>,
    expected: &[Expected],
    contexts: &[(Context, Range<usize>)],
    error_span: &Range<usize>,
) -> Vec<Suggestion> {
    detect_pattern_help(found, expected, contexts, error_span)
}

/// Pattern-based help detection — checks for common error patterns.
fn detect_pattern_help(
    found: &Option<Token<'static>>,
    expected: &[Expected],
    contexts: &[(Context, Range<usize>)],
    error_span: &Range<usize>,
) -> Vec<Suggestion> {
    let in_expr = contexts.iter().any(|(c, _)| *c == Context::Expression);
    let in_decl = contexts.iter().any(|(c, _)| *c == Context::Declaration);
    let in_type = contexts.iter().any(|(c, _)| *c == Context::Type);
    let in_arg = contexts.iter().any(|(c, _)| *c == Context::Argument);
    let in_generic_params = contexts.iter().any(|(c, _)| *c == Context::GenericParams);
    let in_arg_list = contexts.iter().any(|(c, _)| *c == Context::ArgumentList);
    let in_where_clause = contexts.iter().any(|(c, _)| *c == Context::WhereClause);
    let in_type_alias = contexts.iter().any(|(c, _)| *c == Context::TypeAlias);
    let in_range_bound = contexts.iter().any(|(c, _)| *c == Context::RangeBound);
    let in_call_args = contexts.iter().any(|(c, _)| *c == Context::CallArgs);

    // Helper: does the expected list contain a specific token?
    let expects = |tok: &Token| expected.iter().any(|e| e.is_token(tok));

    // Helper: is a specific token the sole expected token?
    let expects_only = |tok: &Token| expected.len() == 1 && expects(tok);

    // Helper: found is a non-punctuation token (identifier, keyword, literal).
    let found_non_punct = matches!(found, Some(f) if !f.is_punctuation());

    // ── Declaration-level patterns (check before expression patterns) ──

    // Missing `<` to open generics: found identifier, expected `<`, in declaration.
    // e.g. `fn f F: Field>(...)` should be `fn f<F: Field>(...)`
    // Only fire at declaration level (not inside expressions where `<` is an operator).
    if in_decl && !in_expr && found_non_punct && expects(&Token::LAngle) {
        return vec![insert_before(
            error_span,
            "missing `<` to open generic type parameters",
            "<",
        )];
    }

    // Missing `(` to open argument list: found identifier/keyword, `(` is the sole
    // expected token, in declaration.
    // e.g. `fn f<F: Field> instance a: F)` should be `fn f<F: Field>(instance a: F)`
    // kind_parser also expects `(` (for `Scalar<...>` / `Pairing<...>`) but alongside
    // kind keywords, so expects_only(LParen) is false there.
    if in_decl && !in_expr && !in_type && found_non_punct && expects_only(&Token::LParen) {
        return vec![insert_before(
            error_span,
            "missing `(` to open argument list",
            "(",
        )];
    }

    // Using `=>` instead of `->` in function return type.
    // e.g. `fn f(...) => F { a }` should be `fn f(...) -> F { a }`
    // More specific than the missing-`->` check below — fires when `=>` is the found token.
    if matches!(found, Some(Token::FatArrow)) && in_decl && expects(&Token::Arrow) {
        return vec![replace(
            error_span,
            "function return types use `->` (not `=>`)",
            "->",
        )];
    }

    // Missing `->` before return type: found identifier, expected `->` or `{`.
    // e.g. `fn f<F: Field>(a: F) F { a }` — missing `->` before return type
    if in_decl && found_non_punct && expects(&Token::Arrow) && expects(&Token::LBrace) {
        return vec![insert_before(
            error_span,
            "missing `->` before return type",
            "-> ",
        )];
    }

    // Using `=` instead of `->` before return type.
    // e.g. `fn f<F: Field>(a: F) = F { a }` — should be `-> F`
    if matches!(found, Some(Token::Eq)) && in_decl && expects(&Token::Arrow) {
        return vec![replace(
            error_span,
            "use `->` before return type (not `=`)",
            "->",
        )];
    }

    // Proto with return type: found `->`, expected `where` or `{`.
    // e.g. `proto p<F: Field>(a: F) -> F where ...` — proto has no return type
    if matches!(found, Some(Token::Arrow)) && in_decl && expects(&Token::KwWhere) {
        return vec![hint(
            error_span,
            "proto declarations don't have return types (use `fn` instead)",
        )];
    }

    // Missing `where` keyword in proto: found identifier, expected `where`.
    // e.g. `proto p<F: Field>(a: F) a == b { }` — missing `where`
    if in_decl && found_non_punct && expects(&Token::KwWhere) {
        return vec![insert_before(
            error_span,
            "missing `where` keyword before constraints",
            "where ",
        )];
    }

    // Missing `:` in argument declaration: found identifier, expected `:`, in argument.
    // e.g. `fn f<F: Field>(instance a F) -> F { a }` — missing `:` after name
    // `in_arg` is specific to argument context — record types and let bindings
    // are excluded naturally (they're not in Argument context).
    if in_arg && found_non_punct && expects(&Token::Colon) {
        return vec![insert_before(
            error_span,
            "missing `:` after argument name",
            ": ",
        )];
    }

    // Missing `>` to close generics: found `(`, expected `>`, in generic params.
    // e.g. `proto p<F: Field(instance a: F)` should be `proto p<F: Field>(instance a: F)`
    if matches!(found, Some(Token::LParen)) && expects(&Token::RAngle) && in_generic_params {
        return vec![insert_before(
            error_span,
            "missing `>` to close generic type parameters",
            "> ",
        )];
    }

    // Missing `)` to close argument list: found `{`, expected `)`, in argument list.
    // e.g. `proto p<F: Field>(instance a: F { }` should be `...(... ) { }`
    if matches!(found, Some(Token::LBrace)) && expects(&Token::RParen) && in_arg_list {
        return vec![insert_before(
            error_span,
            "missing `)` to close argument list",
            ") ",
        )];
    }

    // Missing `}` to close declaration body: found EOF, expected `}`, in declaration.
    if found.is_none() && expects(&Token::RBrace) && in_decl {
        return vec![insert_before(
            error_span,
            "missing `}` to close declaration body",
            "}",
        )];
    }

    // Type alias using `:` instead of `=`: found `:`, expected `=`, in declaration.
    // e.g. `type MyAlias: F;` should be `type MyAlias = F;`
    if matches!(found, Some(Token::Colon)) && in_decl && !in_type && expects(&Token::Eq) {
        return vec![replace(error_span, "type aliases use `=` (not `:`)", "=")];
    }

    // Using `=` instead of `:` in type variable declaration.
    // e.g. `fn f<F = Field>(...)` should be `fn f<F: Field>(...)`
    if matches!(found, Some(Token::Eq)) && in_generic_params && expects(&Token::Colon) {
        return vec![replace(
            error_span,
            "type variables use `:` (not `=`) for kind annotations",
            ":",
        )];
    }

    // Missing `;` after type alias: found EOF, expected `;`, in type alias.
    // e.g. `type MyAlias = F` — missing `;` at end of file
    if found.is_none() && in_type_alias && expects(&Token::Semi) {
        return vec![insert_before(
            error_span,
            "missing `;` at end of declaration",
            ";",
        )];
    }

    // Missing `,` between type parameters: found identifier, expected `,`, in generic params.
    // e.g. `Pairing<G H>` should be `Pairing<G, H>`
    if in_generic_params && found_non_punct && expects(&Token::Comma) {
        return vec![insert_before(
            error_span,
            "missing `,` between type parameters",
            ", ",
        )];
    }

    // Using `==` instead of `=` in assignment.
    // e.g. `let x == a;` should be `let x = a;`
    // More specific than the missing-`=` check below — fires when `==` is the found token.
    if matches!(found, Some(Token::EqEq)) && in_decl && !in_type && expects(&Token::Eq) {
        return vec![replace(error_span, "assignments use `=` (not `==`)", "=")];
    }

    // Missing `=` in let binding or type alias: found identifier, expected `=`, in declaration.
    // e.g. `let x: F a;` should be `let x: F = a;`
    // or `type MyAlias F;` should be `type MyAlias = F;`
    if in_decl && !in_expr && !in_type && found_non_punct && expects(&Token::Eq) {
        return vec![insert_before(error_span, "missing `=` in assignment", "= ")];
    }

    // Missing type in argument: found `)`, in argument context.
    // e.g. `fn f<F: Field>(instance a: )` — expected type after `:`
    // The Type label is filtered from expected, so we use the Argument
    // context to know we're parsing an argument.
    if matches!(found, Some(Token::RParen)) && in_arg {
        return vec![hint(
            error_span,
            "expected a type after `:` in argument declaration",
        )];
    }

    // Missing kind in type variable: found `>`, in generic params, expected
    // kind tokens. e.g. `proto p<N: >(instance a: F)` — expected kind after `:`
    // Since CtxError preserves the real expected tokens (label_with is a
    // no-op for Context), the kind tokens (Field, Group, Size, etc.) are
    // in the expected list.
    if matches!(found, Some(Token::RAngle)) && in_generic_params {
        let kind_tokens = [
            Token::KwField,
            Token::KwGroup,
            Token::KwSize,
            Token::KwPairing,
            Token::KwScalar,
            Token::KwFin,
            Token::KwUnit,
        ];
        if expected
            .iter()
            .any(|e| matches!(e, Expected::Token(t) if kind_tokens.contains(t)))
        {
            return vec![hint(
                error_span,
                "expected a kind after `:` (e.g., `Field`, `Size`, `Group`)",
            )];
        }
    }

    // ── Type-level patterns ─────────────────────────────────────────────

    // Record type using `;` instead of `,`: found `;`, expected `,` or `}`, in type.
    // e.g. `{ x: F; y: F }` should be `{ x: F, y: F }`
    // (record types use `,`; record values also use `,` — but `;` is a common mistake)
    if matches!(found, Some(Token::Semi)) && in_type && expects(&Token::Comma) {
        return vec![replace(
            error_span,
            "record types use `,` between fields (not `;`)",
            ",",
        )];
    }

    // Vector type using `,` instead of `;`: found `,`, expected `;`, in type.
    // e.g. `[F, N]` should be `[F; N]`
    if matches!(found, Some(Token::Comma)) && in_type && expects(&Token::Semi) {
        return vec![replace(
            error_span,
            "vector types use `;` to separate element type from size (e.g., `[T; N]`)",
            ";",
        )];
    }

    // Vector type using `:` instead of `;`: found `:`, expected `;`, in type.
    // e.g. `[F: N]` should be `[F; N]`
    if matches!(found, Some(Token::Colon)) && in_type && expects(&Token::Semi) {
        return vec![replace(
            error_span,
            "vector types use `;` to separate element type from size (e.g., `[T; N]`)",
            ";",
        )];
    }

    // ── Expression-level patterns ───────────────────────────────────────

    // Missing `(` after a function-like keyword: found expression-start, `(` is the sole
    // expected token, in expression.
    // e.g. `assert a == b` should be `assert(a == b)`
    // or `poly a` should be `poly(a)`
    // Function-like keywords (assert, verify, poly, coef, mle, dot, pair,
    // interpolate, reduce) expect exactly `(` after the keyword. Expression-
    // continuation errors have `(` as one of many tokens, so expects_only
    // distinguishes them.
    if in_expr && found_non_punct && expects_only(&Token::LParen) {
        return vec![insert_before(
            error_span,
            "missing `(` after keyword (e.g., `assert(expr == expr)`, `poly(expr)`)",
            "(",
        )];
    }

    // Lambda using `->` instead of `=>`: found `->`, expected `=>`.
    // e.g. `fun x -> x + 1` should be `fun x => x + 1`
    if matches!(found, Some(Token::Arrow)) && expects(&Token::FatArrow) && in_expr {
        return vec![replace(
            error_span,
            "lambda expressions use `=>` (not `->`)",
            "=>",
        )];
    }

    // Record value using `;` instead of `,`: found `;`, expected `|}` or `,`.
    // e.g. `{| x: a; y: b |}` should be `{| x: a, y: b |}`
    if matches!(found, Some(Token::Semi)) && expects(&Token::BarRBrace) && in_expr {
        return vec![replace(
            error_span,
            "record values use `,` between fields (not `;`)",
            ",",
        )];
    }

    // Using `;` instead of `,` in function call: found `;`, in call arguments,
    // `)` is NOT expected (i.e. not at the end of the last argument).
    // e.g. `reduce(+; [a, b])` should be `reduce(+, [a, b])`
    // e.g. `dot(a; b)` should be `dot(a, b)`
    // When `)` is expected (e.g. `assert(a == b; c)`), the `;` is more likely
    // a misplaced `)` — the error message already lists `)` as expected.
    if matches!(found, Some(Token::Semi))
        && in_call_args
        && !expects(&Token::Semi)
        && !expects(&Token::RParen)
    {
        return vec![replace(
            error_span,
            "use `,` between arguments (not `;`)",
            ",",
        )];
    }

    // Where clause missing `==`: found `;`, expected `==`, in where clause.
    // e.g. `where random<F>;` should be `where random<F> == something;`
    if matches!(found, Some(Token::Semi)) && expects(&Token::EqEq) && in_where_clause {
        return vec![insert_before(
            error_span,
            "where clause constraints use `==` (e.g., `expr == value;`)",
            "== ",
        )];
    }

    // Using `=` instead of `==`: found `=`, expected `==`, in expression.
    // e.g. `where a = b` or `assert(a = b)` — should use `==`
    // Keep `in_expr` (not `in_where_clause`) since this also covers assert/verify.
    if matches!(found, Some(Token::Eq)) && expects(&Token::EqEq) && in_expr {
        return vec![replace(error_span, "use `==` for equality (not `=`)", "==")];
    }

    // Missing `in` in comprehension: found expression-start, expected `in`.
    // e.g. `[a for x 0..N]` should be `[a for x in 0..N]`
    // Check before the missing-`;` check since `in` is more specific.
    if in_expr && expects(&Token::KwIn) {
        return vec![insert_before(
            error_span,
            "missing `in` keyword in list comprehension",
            "in ",
        )];
    }

    // Missing `for` in comprehension: found identifier, expected `for`.
    // e.g. `[a x in 0..N]` should be `[a for x in 0..N]`
    // Check before the missing-`;` check since `for` is more specific.
    if in_expr && expects(&Token::KwFor) && found_non_punct {
        return vec![insert_before(
            error_span,
            "missing `for` keyword in list comprehension",
            "for ",
        )];
    }

    // Missing `;` after expression: found expression-starting token, expected `;`.
    // e.g. `where a == b c == d` (missing `;` between where constraints)
    // or `let x = a x` (missing `;` after let-binding value)
    if in_expr && expects(&Token::Semi) && found_non_punct {
        return vec![insert_before(
            error_span,
            "missing `;` after expression",
            "; ",
        )];
    }

    // Incomplete range: found `]` or `)`, in range bound context.
    // e.g. `[a for i in 0..]` — range needs an end bound
    if matches!(found, Some(Token::RBrack) | Some(Token::RParen)) && in_range_bound {
        return vec![hint(error_span, "range needs an end bound (e.g., `0..N`)")];
    }

    vec![]
}
