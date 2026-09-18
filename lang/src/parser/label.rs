//! Parser label types for chumsky `.labelled()` calls.
//!
//! `Context` labels construct-level parsers (declaration, expression, type,
//! etc.) and is used with `.as_context()` to produce secondary error labels.
//! `Terminal` labels terminal token-category parsers (identifier, positive
//! integer). Both implement `TryInto<RichPattern>` so the parser can use
//! `.labelled(Context::Type)` directly instead of `.labelled("type")`.
//!
//! Native chumsky `Rich` is used directly — no custom error wrapper.

use std::borrow::Cow;

use chumsky::error::RichPattern;

use super::lexer::Token;

// ── Context ────────────────────────────────────────────────────────────

/// Context labels for parser constructs (from `.labelled().as_context()`).
///
/// These appear as `RichPattern::Label` in chumsky's `Rich` error contexts
/// when a construct-level parser (declaration, expression, type, etc.) fails.
/// They tell the user *what* the parser was building when the error occurred.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Context {
    /// Any top-level declaration (`fn`, `proto`, `type`, …).
    Declaration,
    /// Any value-level expression.
    Expression,
    /// A type annotation or type expression.
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
    /// Arguments inside `(...)` of a comma-separated function call or builtin
    /// operator (e.g. `dot(a, b)`, `poly(a)`, `f(a, b)`). Not used for
    /// `assert`/`verify` which use `==` between their two arguments.
    CallArgs,
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
            Context::CallArgs => "call arguments",
        }
    }
}

impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Convert a `Context` to a chumsky `RichPattern` for `.labelled()`.
/// This lets the parser use `.labelled(Context::Type)` directly instead of
/// `.labelled("type")`, eliminating the string intermediary.
impl<'a, 'src> TryFrom<Context> for RichPattern<'a, Token<'src>> {
    type Error = ();
    fn try_from(ctx: Context) -> Result<Self, ()> {
        Ok(RichPattern::Label(Cow::Borrowed(ctx.as_str())))
    }
}

/// Recover a `Context` from the string chumsky stores in `RichPattern::Label`.
/// This is the inverse of `as_str` — used by `rich_to_diagnostic` to decode
/// chumsky's string labels into typed variants for secondary labels.
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
            "call arguments" => Ok(Context::CallArgs),
            _ => Err(()),
        }
    }
}

// ── Terminal ───────────────────────────────────────────────────────────

/// Terminal labels for token-category parsers (from `.labelled()`).
///
/// These appear as `RichPattern::Label` in chumsky's `Rich` error expected
/// list when a terminal token parser (identifier, positive integer) fails.
/// They tell the user *what kind of token* was expected, as opposed to
/// `Context` which tells what *construct* was being parsed.
#[derive(Debug, Clone, Copy)]
pub enum Terminal {
    /// A `Tid`/`Vid` identifier token.
    Identifier,
    /// A nonzero unsigned integer literal, used for sizes and degrees.
    PositiveInteger,
    /// The `.set` method on records — used to label the `select!` filter
    /// that distinguishes `.set(` from field projection `.field`.
    Set,
    /// Shared label for all pratt operators (infix, prefix, postfix).
    /// Collapses the long list of operator tokens (`+`, `-`, `*`, `/`, etc.)
    /// into a single "operator" entry in error messages.
    Operator,
}

impl Terminal {
    /// The string chumsky stores in `RichPattern::Label`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Terminal::Identifier => "identifier",
            Terminal::PositiveInteger => "positive integer",
            Terminal::Set => "set",
            Terminal::Operator => "operator",
        }
    }
}

impl std::fmt::Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl<'a, 'src> TryFrom<Terminal> for RichPattern<'a, Token<'src>> {
    type Error = ();
    fn try_from(term: Terminal) -> Result<Self, ()> {
        Ok(RichPattern::Label(Cow::Borrowed(term.as_str())))
    }
}
