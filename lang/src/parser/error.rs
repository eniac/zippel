//! Parse error types and rendering.
//!
//! `ParseError` is a pure data struct. `render_error` produces an ariadne
//! diagnostic report. `rich_to_parse_error` converts chumsky's `Rich` error
//! into `ParseError`.

use chumsky::error::{RichPattern, RichReason};

use super::label::{Context, CtxError, Terminal};
use super::lexer::Token;

// ── Expected ───────────────────────────────────────────────────────────

/// A single expected token or terminal category, owned.
///
/// Distinguishes concrete tokens (e.g. `Token::LParen`) from terminal
/// labels (e.g. `Terminal::Identifier`) so that
/// `Expected::Token(Token::KwType)` (the `type` keyword) and
/// `Expected::Terminal(Terminal::Identifier)` don't collide.
///
/// Construct-level labels (`Context`) are NOT stored here — they appear
/// in `ParseError::contexts` instead, which tells what the parser was
/// doing when the error occurred.
///
/// Tokens are `Token<'static>` (owned) so that `Expected` can outlive the
/// source string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expected {
    /// A concrete token.
    Token(Token<'static>),
    /// A terminal-level label from `.labelled()` (e.g. `Terminal::Identifier`).
    Terminal(Terminal),
    /// End of input.
    EndOfInput,
}

impl Expected {
    /// Return `true` if this is a `Token` matching the given token.
    fn is_token(&self, tok: &Token<'_>) -> bool {
        matches!(self, Expected::Token(t) if t == tok)
    }
}

impl std::fmt::Display for Expected {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expected::Token(t) => write!(f, "'{t}'"),
            Expected::Terminal(t) => write!(f, "{t}"),
            Expected::EndOfInput => write!(f, "end of input"),
        }
    }
}

// ── ParseError ─────────────────────────────────────────────────────────

/// A structured parse error with source span.
///
/// `Display` produces a concise one-line message.
/// Use [`render_error`] for full source-rendered output via ariadne.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Byte span in the source text where the error occurred.
    pub span: std::ops::Range<usize>,
    /// The token that was found (`None` if at end of input).
    /// Owned (`Token<'static>`) so the error can outlive the source.
    pub found: Option<Token<'static>>,
    /// What was expected (typed: token vs label vs end-of-input).
    pub expected: Vec<Expected>,
    /// Custom error message (for semantic errors like duplicate decls).
    /// When set, takes precedence over found/expected.
    pub message: Option<String>,
    /// Parser contexts (context, span) — what the parser was doing when the
    /// error occurred, from chumsky `.labelled().as_context()` calls.
    pub contexts: Vec<(Context, std::ops::Range<usize>)>,
    /// Optional help/suggestion text, rendered as a blue "Help:" note
    /// by ariadne (like rustc's help tips).
    pub help: Option<String>,
}

impl ParseError {
    /// Create a custom error with a message and no source location.
    pub fn custom(msg: String) -> Self {
        ParseError {
            span: 0..0,
            found: None,
            expected: vec![],
            message: Some(msg),
            contexts: vec![],
            help: None,
        }
    }
}

// ── Token category helper ──────────────────────────────────────────────

/// Extension trait for token category checks used in help detection.
trait TokenExt {
    /// Is this a single-character punctuation/operator token?
    /// Used to distinguish identifiers from punctuation in help detection.
    fn is_punctuation(&self) -> bool;
}

impl TokenExt for Token<'_> {
    fn is_punctuation(&self) -> bool {
        matches!(
            self,
            Token::LParen
                | Token::RParen
                | Token::LBrace
                | Token::RBrace
                | Token::LBrack
                | Token::RBrack
                | Token::LAngle
                | Token::RAngle
                | Token::Comma
                | Token::Semi
                | Token::Colon
                | Token::Eq
                | Token::Dot
                | Token::Plus
                | Token::Minus
                | Token::Star
                | Token::Slash
                | Token::Caret
                | Token::Percent
        )
    }
}

// ── summarize_expected ─────────────────────────────────────────────────

/// Group a list of `Expected` into a user-friendly summary.
/// Instead of listing 20 expression-starting tokens, we say "an expression".
///
/// Uses the parser's **context stack** (set via `.labelled().as_context()`)
/// to determine the category, rather than analyzing the token list. This is
/// robust because the context is set at the parse point — no guessing from
/// output.
///
/// For short lists (≤3 tokens), we list them directly regardless of context,
/// since they're always readable. For long lists, the innermost context
/// determines the summary.
fn summarize_expected(
    expected: &[Expected],
    contexts: &[(Context, std::ops::Range<usize>)],
) -> String {
    if expected.is_empty() {
        return "something else".to_string();
    }

    // Format a single Expected as a user-friendly string.
    let fmt_one = |e: &Expected| -> String {
        match e {
            Expected::Terminal(t) => t.to_string(),
            Expected::Token(t) => format!("'{t}'"),
            Expected::EndOfInput => "end of input".to_string(),
        }
    };

    // Short lists — always readable, list directly.
    if expected.len() <= 3 {
        return expected.iter().map(fmt_one).collect::<Vec<_>>().join(", ");
    }

    // Long list — use the context stack to pick a category.
    // Search for the most specific category context (innermost-first).
    let has_ctx = |c: Context| contexts.iter().any(|(ctx, _)| *ctx == c);

    // Check for a closing delimiter in the expected list (e.g. ')', ']', '|}').
    // When present alongside operators/atoms, we append "or ')'" to the summary.
    let closer = expected.iter().find_map(|e| match e {
        Expected::Token(t @ (Token::RParen | Token::RBrack | Token::BarRBrace | Token::RBrace)) => {
            Some(format!("'{t}'"))
        }
        _ => None,
    });

    // Category contexts: check from most specific to least.
    // These contexts are pushed when the corresponding parser is entered.
    if has_ctx(Context::Kind) {
        return "a kind annotation".to_string();
    }
    if has_ctx(Context::Type) {
        return "a type".to_string();
    }
    if has_ctx(Context::WhereClause) {
        // Where-clause continuation: operators + maybe `==` + maybe `}`.
        let has_eqeq = expected.iter().any(|e| e.is_token(&Token::EqEq));
        let has_rbrace = expected.iter().any(|e| e.is_token(&Token::RBrace));
        let mut parts: Vec<&str> = vec![];
        if has_eqeq {
            parts.push("'=='");
        }
        parts.push("an operator");
        if has_rbrace {
            parts.push("'}'");
        }
        if parts.len() == 1 {
            return parts[0].to_string();
        }
        return format!("{} or {}", parts[0], parts[1..].join(" or "));
    }
    if has_ctx(Context::Expression) {
        // Expression context: either atom-start (many expr tokens)
        // or operator-continuation (operators + maybe `,` + maybe a closer).
        // Distinguish by checking if expression-atom keywords are present.
        let has_expr_atoms = expected.iter().any(|e| {
            matches!(
                e,
                Expected::Token(
                    Token::KwFun
                        | Token::KwPoly
                        | Token::KwCoef
                        | Token::KwMle
                        | Token::KwDot
                        | Token::KwReduce
                        | Token::KwPair
                        | Token::KwAssert
                        | Token::KwVerify
                        | Token::KwEval
                        | Token::KwInterpolate
                        | Token::KwRandom
                        | Token::KwChallenge
                        | Token::LBraceBar
                )
            )
        });
        if has_expr_atoms {
            // Atom-start: "an expression" (optionally with a closer).
            if let Some(c) = closer {
                return format!("an expression or {c}");
            }
            return "an expression".to_string();
        } else {
            // Operator-continuation: "an operator", plus `,` if inside a
            // call argument list, and a closer if present.
            let mut parts: Vec<String> = vec!["an operator".to_string()];
            if has_ctx(Context::CallArgs) {
                parts.push("','".to_string());
            }
            if let Some(c) = closer {
                parts.push(c);
            }
            if parts.len() == 1 {
                return parts[0].clone();
            }
            return format!("{} or {}", parts[0], parts[1..].join(" or "));
        }
    }

    // No category context found — list tokens, cap at 5 with "...".
    let quoted: Vec<String> = expected.iter().map(fmt_one).collect();
    if quoted.len() <= 5 {
        quoted.join(", ")
    } else {
        format!("{}, ...", quoted[..5].join(", "))
    }
}

// ── detect_help ────────────────────────────────────────────────────────

/// Detect common error patterns and generate a help tip.
///
/// Each pattern checks `found`, `expected`, and `contexts` to identify a
/// likely user mistake. Returns a help message rendered as a blue "Help:"
/// note by ariadne (like rustc's help tips).
fn detect_help(
    found: &Option<Token<'static>>,
    expected: &[Expected],
    contexts: &[(Context, std::ops::Range<usize>)],
) -> Option<String> {
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
        return Some("missing `<` to open generic type parameters".to_string());
    }

    // Missing `(` to open argument list: found identifier/keyword, `(` is the sole
    // expected token, in declaration.
    // e.g. `fn f<F: Field> instance a: F)` should be `fn f<F: Field>(instance a: F)`
    // kind_parser also expects `(` (for `Scalar<...>` / `Pairing<...>`) but alongside
    // kind keywords, so expects_only(LParen) is false there.
    if in_decl && !in_expr && !in_type && found_non_punct && expects_only(&Token::LParen) {
        return Some("missing `(` to open argument list".to_string());
    }

    // Using `=>` instead of `->` in function return type.
    // e.g. `fn f(...) => F { a }` should be `fn f(...) -> F { a }`
    // More specific than the missing-`->` check below — fires when `=>` is the found token.
    if matches!(found, Some(Token::FatArrow)) && in_decl && expects(&Token::Arrow) {
        return Some("function return types use `->` (not `=>`)".to_string());
    }

    // Missing `->` before return type: found identifier, expected `->` or `{`.
    // e.g. `fn f<F: Field>(a: F) F { a }` — missing `->` before return type
    if in_decl && found_non_punct && expects(&Token::Arrow) && expects(&Token::LBrace) {
        return Some("missing `->` before return type".to_string());
    }

    // Using `=` instead of `->` before return type.
    // e.g. `fn f<F: Field>(a: F) = F { a }` — should be `-> F`
    if matches!(found, Some(Token::Eq)) && in_decl && expects(&Token::Arrow) {
        return Some("use `->` before return type (not `=`)".to_string());
    }

    // Proto with return type: found `->`, expected `where` or `{`.
    // e.g. `proto p<F: Field>(a: F) -> F where ...` — proto has no return type
    if matches!(found, Some(Token::Arrow)) && in_decl && expects(&Token::KwWhere) {
        return Some("proto declarations don't have return types (use `fn` instead)".to_string());
    }

    // Missing `where` keyword in proto: found identifier, expected `where`.
    // e.g. `proto p<F: Field>(a: F) a == b { }` — missing `where`
    if in_decl && found_non_punct && expects(&Token::KwWhere) {
        return Some("missing `where` keyword before constraints".to_string());
    }

    // Missing `:` in argument declaration: found identifier, expected `:`, in argument.
    // e.g. `fn f<F: Field>(instance a F) -> F { a }` — missing `:` after name
    // `in_arg` is specific to argument context — record types and let bindings
    // are excluded naturally (they're not in Argument context).
    if in_arg && found_non_punct && expects(&Token::Colon) {
        return Some("missing `:` after argument name".to_string());
    }

    // Missing `>` to close generics: found `(`, expected `>`, in generic params.
    // e.g. `proto p<F: Field(instance a: F)` should be `proto p<F: Field>(instance a: F)`
    if matches!(found, Some(Token::LParen)) && expects(&Token::RAngle) && in_generic_params {
        return Some("missing `>` to close generic type parameters".to_string());
    }

    // Missing `)` to close argument list: found `{`, expected `)`, in argument list.
    // e.g. `proto p<F: Field>(instance a: F { }` should be `...(... ) { }`
    if matches!(found, Some(Token::LBrace)) && expects(&Token::RParen) && in_arg_list {
        return Some("missing `)` to close argument list".to_string());
    }

    // Missing `}` to close declaration body: found EOF, expected `}`, in declaration.
    if found.is_none() && expects(&Token::RBrace) && in_decl {
        return Some("missing `}` to close declaration body".to_string());
    }

    // Type alias using `:` instead of `=`: found `:`, expected `=`, in declaration.
    // e.g. `type MyAlias: F;` should be `type MyAlias = F;`
    if matches!(found, Some(Token::Colon)) && in_decl && !in_type && expects(&Token::Eq) {
        return Some("type aliases use `=` (not `:`)".to_string());
    }

    // Using `=` instead of `:` in type variable declaration.
    // e.g. `fn f<F = Field>(...)` should be `fn f<F: Field>(...)`
    if matches!(found, Some(Token::Eq)) && in_generic_params && expects(&Token::Colon) {
        return Some("type variables use `:` (not `=`) for kind annotations".to_string());
    }

    // Missing `;` after type alias: found EOF, expected `;`, in type alias.
    // e.g. `type MyAlias = F` — missing `;` at end of file
    if found.is_none() && in_type_alias && expects(&Token::Semi) {
        return Some("missing `;` at end of declaration".to_string());
    }

    // Missing `,` between type parameters: found identifier, expected `,`, in generic params.
    // e.g. `Pairing<G H>` should be `Pairing<G, H>`
    if in_generic_params && found_non_punct && expects(&Token::Comma) {
        return Some("missing `,` between type parameters".to_string());
    }

    // Using `==` instead of `=` in assignment.
    // e.g. `let x == a;` should be `let x = a;`
    // More specific than the missing-`=` check below — fires when `==` is the found token.
    if matches!(found, Some(Token::EqEq)) && in_decl && !in_type && expects(&Token::Eq) {
        return Some("assignments use `=` (not `==`)".to_string());
    }

    // Missing `=` in let binding or type alias: found identifier, expected `=`, in declaration.
    // e.g. `let x: F a;` should be `let x: F = a;`
    // or `type MyAlias F;` should be `type MyAlias = F;`
    if in_decl && !in_expr && !in_type && found_non_punct && expects(&Token::Eq) {
        return Some("missing `=` in assignment".to_string());
    }

    // Missing type in argument: found `)`, in argument context.
    // e.g. `fn f<F: Field>(instance a: )` — expected type after `:`
    // The Type label is filtered from expected, so we use the Argument
    // context to know we're parsing an argument.
    if matches!(found, Some(Token::RParen)) && in_arg {
        return Some("expected a type after `:` in argument declaration".to_string());
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
            return Some("expected a kind after `:` (e.g., `Field`, `Size`, `Group`)".to_string());
        }
    }

    // ── Type-level patterns ─────────────────────────────────────────────

    // Record type using `;` instead of `,`: found `;`, expected `,` or `}`, in type.
    // e.g. `{ x: F; y: F }` should be `{ x: F, y: F }`
    // (record types use `,`; record values also use `,` — but `;` is a common mistake)
    if matches!(found, Some(Token::Semi)) && in_type && expects(&Token::Comma) {
        return Some("record types use `,` between fields (not `;`)".to_string());
    }

    // Vector type using `,` instead of `;`: found `,`, expected `;`, in type.
    // e.g. `[F, N]` should be `[F; N]`
    if matches!(found, Some(Token::Comma)) && in_type && expects(&Token::Semi) {
        return Some(
            "vector types use `;` to separate element type from size (e.g., `[T; N]`)".to_string(),
        );
    }

    // Vector type using `:` instead of `;`: found `:`, expected `;`, in type.
    // e.g. `[F: N]` should be `[F; N]`
    if matches!(found, Some(Token::Colon)) && in_type && expects(&Token::Semi) {
        return Some(
            "vector types use `;` to separate element type from size (e.g., `[T; N]`)".to_string(),
        );
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
        return Some(
            "missing `(` after keyword (e.g., `assert(expr == expr)`, `poly(expr)`)".to_string(),
        );
    }

    // Lambda using `->` instead of `=>`: found `->`, expected `=>`.
    // e.g. `fun x -> x + 1` should be `fun x => x + 1`
    if matches!(found, Some(Token::Arrow)) && expects(&Token::FatArrow) && in_expr {
        return Some("lambda expressions use `=>` (not `->`)".to_string());
    }

    // Record value using `;` instead of `,`: found `;`, expected `|}` or `,`.
    // e.g. `{| x: a; y: b |}` should be `{| x: a, y: b |}`
    if matches!(found, Some(Token::Semi)) && expects(&Token::BarRBrace) && in_expr {
        return Some("record values use `,` between fields (not `;`)".to_string());
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
        return Some("use `,` between arguments (not `;`)".to_string());
    }

    // Where clause missing `==`: found `;`, expected `==`, in where clause.
    // e.g. `where random<F>;` should be `where random<F> == something;`
    if matches!(found, Some(Token::Semi)) && expects(&Token::EqEq) && in_where_clause {
        return Some(
            "where clause constraints use `==` — did you mean `expr == value;`?".to_string(),
        );
    }

    // Using `=` instead of `==`: found `=`, expected `==`, in expression.
    // e.g. `where a = b` or `assert(a = b)` — should use `==`
    // Keep `in_expr` (not `in_where_clause`) since this also covers assert/verify.
    if matches!(found, Some(Token::Eq)) && expects(&Token::EqEq) && in_expr {
        return Some("use `==` for equality (not `=`)".to_string());
    }

    // Missing `in` in comprehension: found expression-start, expected `in`.
    // e.g. `[a for x 0..N]` should be `[a for x in 0..N]`
    // Check before the missing-`;` check since `in` is more specific.
    if in_expr && expects(&Token::KwIn) {
        return Some("missing `in` keyword in list comprehension".to_string());
    }

    // Missing `for` in comprehension: found identifier, expected `for`.
    // e.g. `[a x in 0..N]` should be `[a for x in 0..N]`
    // Check before the missing-`;` check since `for` is more specific.
    if in_expr && expects(&Token::KwFor) && found_non_punct {
        return Some("missing `for` keyword in list comprehension".to_string());
    }

    // Missing `;` after expression: found expression-starting token, expected `;`.
    // e.g. `where a == b c == d` (missing `;` between where constraints)
    // or `let x = a x` (missing `;` after let-binding value)
    if in_expr && expects(&Token::Semi) && found_non_punct {
        return Some("missing `;` after expression".to_string());
    }

    // Incomplete range: found `]` or `)`, in range bound context.
    // e.g. `[a for i in 0..]` — range needs an end bound
    if matches!(found, Some(Token::RBrack) | Some(Token::RParen)) && in_range_bound {
        return Some("range needs an end bound (e.g., `0..N`)".to_string());
    }

    None
}

// ── error_summary / error_label_msg ────────────────────────────────────

/// Build a user-friendly top-level summary message for the error.
fn error_summary(error: &ParseError) -> String {
    if let Some(msg) = &error.message {
        // Use only the first line of custom messages as the summary.
        return msg.lines().next().unwrap_or(msg).to_string();
    }

    let found = error
        .found
        .as_ref()
        .map(|t| format!("unexpected '{t}'"))
        .unwrap_or_else(|| "unexpected end of input".to_string());

    // If we have context labels, mention what we were parsing.
    if let Some((label, _)) = error.contexts.first() {
        format!("{found} while parsing {label}")
    } else if error.expected.is_empty() {
        found
    } else {
        format!(
            "{found}, expected {}",
            summarize_expected(&error.expected, &error.contexts)
        )
    }
}

/// Build the detailed label message for the error span.
fn error_label_msg(error: &ParseError) -> String {
    if let Some(msg) = &error.message {
        return msg.clone();
    }

    let found = error
        .found
        .as_ref()
        .map(|t| format!("found '{t}'"))
        .unwrap_or_else(|| "found end of input".to_string());

    if error.expected.is_empty() {
        found
    } else {
        format!(
            "{found}, expected {}",
            summarize_expected(&error.expected, &error.contexts)
        )
    }
}

// ── render_error ───────────────────────────────────────────────────────

/// Render a `ParseError` as a full ariadne diagnostic report with source
/// context. `filename` is shown in the report header.
/// Returns the rendered string.
pub fn render_error(error: &ParseError, filename: &str, src: &str) -> String {
    use ariadne::{Config, IndexType, Label, Report, ReportKind};

    let mut buf = Vec::new();
    let config = Config::new().with_index_type(IndexType::Byte);

    let summary = error_summary(error);
    let label_msg = error_label_msg(error);

    let mut builder = Report::build(
        ReportKind::Custom("error", ariadne::Color::Red),
        (filename.to_string(), error.span.clone()),
    )
    .with_config(config)
    .with_message(summary)
    .with_label(
        Label::new((filename.to_string(), error.span.clone()))
            .with_message(label_msg)
            .with_color(ariadne::Color::Red),
    );

    // Add context labels (e.g. "while parsing this expression") as
    // secondary yellow labels, like rustc does.
    for (label, span) in &error.contexts {
        builder = builder.with_label(
            Label::new((filename.to_string(), span.clone()))
                .with_message(format!("while parsing this {label}"))
                .with_color(ariadne::Color::Yellow),
        );
    }

    // Add help tip (blue, like rustc's "help:" notes).
    if let Some(help) = &error.help {
        builder = builder.with_help(help.clone());
    }

    builder
        .finish()
        .write(
            ariadne::sources([(filename.to_string(), src.to_string())]),
            &mut buf,
        )
        .unwrap();

    String::from_utf8(buf).unwrap_or_default()
}

// ── Display + Error ────────────────────────────────────────────────────

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(msg) = &self.message {
            return write!(f, "{msg}");
        }

        let found = self
            .found
            .as_ref()
            .map(|t| format!("found '{t}'"))
            .unwrap_or_else(|| "found end of input".to_string());
        write!(f, "{found}")?;
        if !self.expected.is_empty() {
            let parts: Vec<String> = self.expected.iter().map(|e| e.to_string()).collect();
            write!(f, ", expected {}", parts.join(", "))?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

// ── rich_to_parse_error ────────────────────────────────────────────────

/// Convert a chumsky `CtxError` into a self-contained `ParseError`.
pub(super) fn rich_to_parse_error(e: &CtxError) -> ParseError {
    let e = &e.0;
    // The error span is a byte-offset range (SimpleSpan).
    let span = e.span().into_range();

    // Capture parser contexts (from .labelled().as_context() calls) for secondary labels.
    let contexts: Vec<(Context, std::ops::Range<usize>)> = e
        .contexts()
        .filter_map(|(p, s)| match p {
            RichPattern::Label(cow) => Context::try_from(cow.as_ref())
                .ok()
                .map(|c| (c, s.into_range())),
            _ => None,
        })
        .collect();

    // Handle custom errors (e.g. duplicate declaration from .validate())
    if let RichReason::Custom(msg) = e.reason() {
        return ParseError {
            span,
            found: None,
            expected: vec![],
            message: Some(msg.to_string()),
            contexts,
            help: None,
        };
    }

    // Found token — convert borrowed token to owned (detaches from source).
    let found = e.found().map(|t| (*t).clone().into_owned());

    // Expected tokens — convert RichPattern to owned Expected.
    // Context labels never appear here (CtxError's label_with is a no-op
    // for Context), so no filtering needed.
    let expected: Vec<Expected> = e
        .expected()
        .filter_map(|p| match p {
            RichPattern::Token(t) => Some(Expected::Token((**t).clone().into_owned())),
            RichPattern::Label(cow) => Terminal::try_from(cow.as_ref())
                .ok()
                .map(Expected::Terminal),
            RichPattern::Identifier(_) => Some(Expected::Terminal(Terminal::Identifier)),
            RichPattern::EndOfInput => Some(Expected::EndOfInput),
            RichPattern::Any | RichPattern::SomethingElse => None,
            _ => None,
        })
        .collect();

    // Detect common error patterns and generate a help tip.
    let help = detect_help(&found, &expected, &contexts);

    ParseError {
        span,
        found,
        expected,
        message: None,
        contexts,
        help,
    }
}

// ── Tests ──────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::super::parse_decls;
    use super::*;

    // ── Render tests ───────────────────────────────────────────────────

    #[test]
    fn render_shows_line_col() {
        let src = "fn f<F: Field>(instance a: F) -> F {\n    a +\n}\n";
        let (_, errors) = parse_decls(src);
        assert!(!errors.is_empty());
        let e = &errors[0];
        // Error points to `}` on line 3 — the parser expected
        // an expression after `+` but found `}`.
        let rendered = render_error(e, "test.zippel", src);
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
        let rendered = render_error(e, "test.zippel", src);
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
        let src =
            "fn f<F: Field>(instance a: F) -> F { a }\nfn f<F: Field>(instance a: F) -> F { a }";
        let err = UModule::from_str(src).unwrap_err();
        let rendered = render_error(&err, "test.zippel", src);
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
            .find_map(|e| e.help.as_deref())
            .unwrap_or_else(|| {
                panic!(
                    "no help tip found for: {src}\nerrors: {:?}",
                    errors.iter().map(|e| &e.help).collect::<Vec<_>>()
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
            assert!(e.help.is_none(), "unexpected help: {:?}", e.help);
        }
    }

    // ── New help patterns ──────────────────────────────────────────────

    #[test]
    fn help_lambda_arrow_not_fatarrow() {
        // `fun x -> x` — should use `=>` not `->`
        assert_help(
            "fn f<F: Field>(instance a: F) -> F { fun x -> x + 1 }",
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
                !e.help.as_deref().unwrap_or("").contains("argument name"),
                "false positive: {:?}",
                e.help
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
                !e.help.as_deref().unwrap_or("").contains("argument name"),
                "false positive: {:?}",
                e.help
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
                !e.help.as_deref().unwrap_or("").contains("argument list"),
                "false positive: {:?}",
                e.help
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
                !e.help
                    .as_deref()
                    .unwrap_or("")
                    .contains("generic type parameters"),
                "false positive: {:?}",
                e.help
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
                !e.help.as_deref().unwrap_or("").contains("argument list"),
                "false positive: {:?}",
                e.help
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
}
