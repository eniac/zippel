//! Parser label types for chumsky `.labelled()` calls.
//!
//! `Context` labels construct-level parsers (declaration, expression, type,
//! etc.) and is used with `.as_context()` to produce secondary error labels.
//! `Terminal` labels terminal token-category parsers (identifier, positive
//! integer). Both implement `TryInto<RichPattern>` so the parser can use
//! `.labelled(Context::Type)` directly instead of `.labelled("type")`.
//!
//! `CtxError` is a newtype around `Rich` that makes `label_with` a no-op
//! for `Context` labels (preserving the real expected tokens) while
//! delegating to `Rich` for `Terminal` and `DefaultExpected` labels.

use std::borrow::Cow;

use chumsky::error::{Error, Rich, RichPattern};
use chumsky::input::Input;
use chumsky::label::LabelError;
use chumsky::span::SimpleSpan;
use chumsky::util::MaybeRef;
use chumsky::DefaultExpected;

use super::lexer::Token;

// ── Context ────────────────────────────────────────────────────────────

/// Context labels for parser constructs (from `.labelled().as_context()`).
///
/// These appear in `ParseError::contexts` and `Expected::Context` when a
/// construct-level parser (declaration, expression, type, etc.) fails.
/// They tell the user *what* the parser was building when the error occurred.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Context {
    Declaration,
    Expression,
    Type,
    /// Kind annotation after `:` in type variables (e.g. `F: Field`).
    Kind,
    /// Function/proto argument (e.g. `instance a: F`).
    Argument,
    /// Where-clause constraint in proto declarations.
    WhereClause,
    /// Generic type parameter list inside `<...>` (e.g. `<F: Field, N: Size>`).
    GenericParams,
    /// Argument list inside `(...)` of a fn/proto declaration.
    ArgumentList,
    /// Top-level type alias declaration (`type X = T;`).
    TypeAlias,
    /// Range end bound after `..` (e.g. `0..N`).
    RangeBound,
}

impl Context {
    /// The string chumsky stores in `RichPattern::Label`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Context::Declaration => "declaration",
            Context::Expression => "expression",
            Context::Type => "type",
            Context::Kind => "kind",
            Context::Argument => "argument",
            Context::WhereClause => "where clause",
            Context::GenericParams => "generic parameters",
            Context::ArgumentList => "argument list",
            Context::TypeAlias => "type alias",
            Context::RangeBound => "range bound",
        }
    }
}

impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(match self {
            Context::Declaration => "a declaration",
            Context::Expression => "an expression",
            Context::Type => "a type",
            Context::Kind => "a kind annotation",
            Context::Argument => "an argument",
            Context::WhereClause => "a where clause",
            Context::GenericParams => "generic parameters",
            Context::ArgumentList => "an argument list",
            Context::TypeAlias => "a type alias",
            Context::RangeBound => "a range bound",
        })
    }
}

/// Convert a `Context` to a chumsky `RichPattern` for `.labelled()`.
/// This lets the parser use `.labelled(Context::Type)` directly instead of
/// `.labelled("type")`, eliminating the string intermediary.
impl TryFrom<Context> for RichPattern<'_, Token> {
    type Error = ();
    fn try_from(ctx: Context) -> Result<Self, ()> {
        Ok(RichPattern::Label(Cow::Borrowed(ctx.as_str())))
    }
}

/// Recover a `Context` from the string chumsky stores in `RichPattern::Label`.
/// This is the inverse of `as_str` — used by `rich_to_parse_error` to convert
/// chumsky's string labels back to typed variants.
impl TryFrom<&str> for Context {
    type Error = ();
    fn try_from(s: &str) -> Result<Self, ()> {
        match s {
            "declaration" => Ok(Context::Declaration),
            "expression" => Ok(Context::Expression),
            "type" => Ok(Context::Type),
            "kind" => Ok(Context::Kind),
            "argument" => Ok(Context::Argument),
            "where clause" => Ok(Context::WhereClause),
            "generic parameters" => Ok(Context::GenericParams),
            "argument list" => Ok(Context::ArgumentList),
            "type alias" => Ok(Context::TypeAlias),
            "range bound" => Ok(Context::RangeBound),
            _ => Err(()),
        }
    }
}

// ── Terminal ───────────────────────────────────────────────────────────

/// Terminal labels for token-category parsers (from `.labelled()`).
///
/// These appear in `Expected::Terminal` when a terminal token parser
/// (identifier, positive integer) fails. They tell the user *what kind
/// of token* was expected, as opposed to `Context` which tells what
/// *construct* was being parsed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Terminal {
    Identifier,
    PositiveInteger,
    /// The `.set` method on records — used to label the `select!` filter
    /// that distinguishes `.set(` from field projection `.field`.
    Set,
}

impl Terminal {
    pub const fn as_str(self) -> &'static str {
        match self {
            Terminal::Identifier => "identifier",
            Terminal::PositiveInteger => "positive integer",
            Terminal::Set => "set",
        }
    }
}

impl std::fmt::Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl TryFrom<Terminal> for RichPattern<'_, Token> {
    type Error = ();
    fn try_from(term: Terminal) -> Result<Self, ()> {
        Ok(RichPattern::Label(Cow::Borrowed(term.as_str())))
    }
}

/// Recover a `Terminal` from the string chumsky stores in `RichPattern::Label`.
/// This is the inverse of `as_str` — used by `rich_to_parse_error`.
impl TryFrom<&str> for Terminal {
    type Error = ();
    fn try_from(s: &str) -> Result<Self, ()> {
        match s {
            "identifier" => Ok(Terminal::Identifier),
            "positive integer" => Ok(Terminal::PositiveInteger),
            "set" => Ok(Terminal::Set),
            _ => Err(()),
        }
    }
}

// ── CtxError ───────────────────────────────────────────────────────────

/// A newtype around `Rich` that selectively disables `label_with` for
/// `Context` labels.
///
/// `.labelled(L).as_context()` calls both `label_with` (replaces the
/// expected token list with a single label) and `in_context` (adds the
/// label to the context stack). For `Context` labels we want only the
/// context tracking — the real expected tokens are more useful for error
/// messages. For `Terminal` labels, `label_with` is the primary effect
/// (replacing raw tokens with "identifier" / "positive integer"), so it
/// delegates to `Rich` normally.
pub struct CtxError<'src>(pub Rich<'src, Token, SimpleSpan>);

impl<'src> std::fmt::Debug for CtxError<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'src> Clone for CtxError<'src> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

// Error trait — required by chumsky's parser infrastructure.
// Delegates to inner Rich. Requires LabelError for DefaultExpected.
impl<'src, I> Error<'src, I> for CtxError<'src>
where
    I: Input<'src, Token = Token, Span = SimpleSpan>,
{
    fn merge(self, other: Self) -> Self {
        Self(<Rich<'src, Token, SimpleSpan> as Error<'src, I>>::merge(
            self.0, other.0,
        ))
    }
}

// LabelError for DefaultExpected — required by Error trait.
// Both label_with and in_context delegate to Rich (normal behavior).
impl<'src, I> LabelError<'src, I, DefaultExpected<'src, Token>> for CtxError<'src>
where
    I: Input<'src, Token = Token, Span = SimpleSpan>,
{
    fn expected_found<E: IntoIterator<Item = DefaultExpected<'src, Token>>>(
        expected: E,
        found: Option<MaybeRef<'src, Token>>,
        span: SimpleSpan,
    ) -> Self {
        Self(<Rich<'src, Token, SimpleSpan> as LabelError<
            'src,
            I,
            DefaultExpected<'src, Token>,
        >>::expected_found(expected, found, span))
    }
}

// LabelError for Context — label_with redirects to in_context so that
// context is pushed even when the parser fails at its first token (no
// progress). Chumsky's LabelledWith::go calls label_with at boundary
// errors (new_alt_loc == before_loc) and in_context for interior errors
// (new_alt_loc > before_loc). By making label_with call in_context, we
// ensure the context is always on the stack regardless of whether the
// parser made progress. The expected tokens are preserved (not replaced
// with a single label) because we never call Rich's label_with.
impl<'src, I> LabelError<'src, I, Context> for CtxError<'src>
where
    I: Input<'src, Token = Token, Span = SimpleSpan>,
{
    fn expected_found<E: IntoIterator<Item = Context>>(
        expected: E,
        found: Option<MaybeRef<'src, Token>>,
        span: SimpleSpan,
    ) -> Self {
        Self(<Rich<'src, Token, SimpleSpan> as LabelError<
            'src,
            I,
            Context,
        >>::expected_found(expected, found, span))
    }

    fn label_with(&mut self, label: Context) {
        // Redirect to in_context: push the context label onto the stack
        // using the error's own span. This fires at boundary errors where
        // chumsky would normally call label_with (replacing expected tokens).
        // We keep the real expected tokens and add context instead.
        let span = *self.0.span();
        <Rich<'src, Token, SimpleSpan> as LabelError<'src, I, Context>>::in_context(
            &mut self.0,
            label,
            span,
        );
    }

    fn in_context(&mut self, label: Context, span: SimpleSpan) {
        <Rich<'src, Token, SimpleSpan> as LabelError<'src, I, Context>>::in_context(
            &mut self.0,
            label,
            span,
        );
    }
}

// LabelError for Terminal — both label_with and in_context delegate to Rich
// (Terminal labels use label_with as their primary effect).
impl<'src, I> LabelError<'src, I, Terminal> for CtxError<'src>
where
    I: Input<'src, Token = Token, Span = SimpleSpan>,
{
    fn expected_found<E: IntoIterator<Item = Terminal>>(
        expected: E,
        found: Option<MaybeRef<'src, Token>>,
        span: SimpleSpan,
    ) -> Self {
        Self(<Rich<'src, Token, SimpleSpan> as LabelError<
            'src,
            I,
            Terminal,
        >>::expected_found(expected, found, span))
    }
}
