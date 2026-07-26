//! Token vocabulary for the logos lexer and chumsky parser.
//!
//! The `#[repr(u16)]` allows mapping to `rowan::SyntaxKind` without
//! conversion overhead if a CST is added later.

#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(non_camel_case_types, non_snake_case, clippy::upper_case_acronyms)]
pub enum SyntaxKind {
    // ── Tokens (leaves) ──────────────────────────────────────────────
    // Punctuation
    LPAREN,     // (
    RPAREN,     // )
    LBRACE,     // {
    RBRACE,     // }
    LBRACK,     // [
    RBRACK,     // ]
    LANGLE,     // <
    RANGLE,     // >
    COMMA,      // ,
    SEMI,       // ;
    COLON,      // :
    EQ,         // =
    ARROW,      // ->
    FAT_ARROW,  // =>
    EQ_EQ,      // ==
    DOT,        // .
    DOTDOT,     // ..
    LARROW,     // <-
    LBRACE_BAR, // {|
    BAR_RBRACE, // |}
    // Operators (also used as size-type operators)
    PLUS,      // +
    MINUS,     // -
    STAR,      // * (binary mul, also "non-zero" marker after random/challenge)
    SLASH,     // /
    CARET,     // ^
    PERCENT,   // %
    PLUS_PLUS, // ++
    // Literals
    POSITIVE, // [0-9]+
    // Identifiers
    ID, // variable/function/type-variable names
    // Keywords (lowercase — expression/declaration keywords)
    KW_LET,
    KW_FN,
    KW_PROTO,
    KW_TYPE,
    KW_FUN,
    KW_FOR,
    KW_IN,
    KW_INTERPOLATE,
    KW_POLY,
    KW_EVAL,
    KW_COEF,
    KW_MLE,
    KW_DOT, // `dot` (dot product function)
    KW_REDUCE,
    KW_RANDOM,
    KW_CHALLENGE,
    KW_ASSERT,
    KW_VERIFY,
    KW_PAIR,
    KW_WHERE,
    // Qualifier / distribution keywords
    KW_INSTANCE,
    KW_WITNESS,
    KW_EXTRA,
    KW_UNIFORM,
    // Type keywords (uppercase)
    KW_FIELD,
    KW_GROUP,
    KW_PAIRING,
    KW_SCALAR,
    KW_SIZE,
    KW_UNIT,
    KW_FIN,
    KW_POLY_TY, // `Poly`
    KW_UNI,     // `Uni`
    KW_MLE_TY,  // `Mle`
    // Trivia (preserved in token stream, skipped by parser)
    WHITESPACE,
    LINE_COMMENT,  // //...
    BLOCK_COMMENT, // /*...*/
    // Error
    ERROR,
}

impl SyntaxKind {
    /// Trivia tokens are preserved in the token stream but carry no semantic
    /// meaning. The parser skips them; the formatter keeps them.
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            SyntaxKind::WHITESPACE | SyntaxKind::LINE_COMMENT | SyntaxKind::BLOCK_COMMENT
        )
    }

    /// User-facing name for use in parse error messages.
    /// Punctuation shows the literal character(s); keywords show the word;
    /// `ID` shows `identifier`; `POSITIVE` shows `integer literal`.
    pub fn display(self) -> &'static str {
        match self {
            // Punctuation — show the literal
            SyntaxKind::LPAREN => "(",
            SyntaxKind::RPAREN => ")",
            SyntaxKind::LBRACE => "{",
            SyntaxKind::RBRACE => "}",
            SyntaxKind::LBRACK => "[",
            SyntaxKind::RBRACK => "]",
            SyntaxKind::LANGLE => "<",
            SyntaxKind::RANGLE => ">",
            SyntaxKind::COMMA => ",",
            SyntaxKind::SEMI => ";",
            SyntaxKind::COLON => ":",
            SyntaxKind::EQ => "=",
            SyntaxKind::ARROW => "->",
            SyntaxKind::FAT_ARROW => "=>",
            SyntaxKind::EQ_EQ => "==",
            SyntaxKind::DOT => ".",
            SyntaxKind::DOTDOT => "..",
            SyntaxKind::LARROW => "<-",
            SyntaxKind::LBRACE_BAR => "{|",
            SyntaxKind::BAR_RBRACE => "|}",
            // Operators
            SyntaxKind::PLUS => "+",
            SyntaxKind::MINUS => "-",
            SyntaxKind::STAR => "*",
            SyntaxKind::SLASH => "/",
            SyntaxKind::CARET => "^",
            SyntaxKind::PERCENT => "%",
            SyntaxKind::PLUS_PLUS => "++",
            // Literals / identifiers
            SyntaxKind::POSITIVE => "integer literal",
            SyntaxKind::ID => "identifier",
            // Keywords — show the word
            SyntaxKind::KW_LET => "let",
            SyntaxKind::KW_FN => "fn",
            SyntaxKind::KW_PROTO => "proto",
            SyntaxKind::KW_TYPE => "type",
            SyntaxKind::KW_FUN => "fun",
            SyntaxKind::KW_FOR => "for",
            SyntaxKind::KW_IN => "in",
            SyntaxKind::KW_INTERPOLATE => "interpolate",
            SyntaxKind::KW_POLY => "poly",
            SyntaxKind::KW_EVAL => "eval",
            SyntaxKind::KW_COEF => "coef",
            SyntaxKind::KW_MLE => "mle",
            SyntaxKind::KW_DOT => "dot",
            SyntaxKind::KW_REDUCE => "reduce",
            SyntaxKind::KW_RANDOM => "random",
            SyntaxKind::KW_CHALLENGE => "challenge",
            SyntaxKind::KW_ASSERT => "assert",
            SyntaxKind::KW_VERIFY => "verify",
            SyntaxKind::KW_PAIR => "pair",
            SyntaxKind::KW_WHERE => "where",
            SyntaxKind::KW_INSTANCE => "instance",
            SyntaxKind::KW_WITNESS => "witness",
            SyntaxKind::KW_EXTRA => "extra",
            SyntaxKind::KW_UNIFORM => "uniform",
            SyntaxKind::KW_FIELD => "Field",
            SyntaxKind::KW_GROUP => "Group",
            SyntaxKind::KW_PAIRING => "Pairing",
            SyntaxKind::KW_SCALAR => "Scalar",
            SyntaxKind::KW_SIZE => "Size",
            SyntaxKind::KW_UNIT => "Unit",
            SyntaxKind::KW_FIN => "Fin",
            SyntaxKind::KW_POLY_TY => "Poly",
            SyntaxKind::KW_UNI => "Uni",
            SyntaxKind::KW_MLE_TY => "Mle",
            // Trivia / error — not expected to appear in errors
            SyntaxKind::WHITESPACE => "whitespace",
            SyntaxKind::LINE_COMMENT => "line comment",
            SyntaxKind::BLOCK_COMMENT => "block comment",
            SyntaxKind::ERROR => "invalid token",
        }
    }
}
