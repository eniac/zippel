//! Logos-based lexer for Zippel.
//!
//! Turns `&str` into `Vec<(Token, SimpleSpan)>` where every token — including
//! trivia (whitespace, comments) and punctuation — has a byte span. This is
//! the key difference from pest: there are no "silent" tokens.
//!
//! The token stream is lossless: `src == tokens.map(|(t, s)| &src[s]).collect()`.

use chumsky::span::SimpleSpan;
use logos::{Lexer, Logos};

/// Lexer error type. Currently only produced for unterminated block comments.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum LexingError {
    /// `/*` with no matching `*/` before end of input.
    UnterminatedBlockComment,
    #[default]
    Other,
}

/// Callback for block comments. Logos matches the `/*` opening, then this
/// function scans for the closing `*/` and bumps the lexer past it.
///
/// A callback is required because logos's DFA-based regex engine can't match
/// the `/* ... */` pattern (it would need backtracking). This is the idiomatic
/// approach recommended by the logos handbook for comments and raw strings.
///
/// Returns `Err` for unterminated block comments so the caller can report a
/// proper error instead of silently consuming the rest of the input.
fn block_comment_end(lex: &mut Lexer<RawToken>) -> Result<(), LexingError> {
    let rest = lex.remainder();
    match rest.find("*/") {
        Some(pos) => {
            lex.bump(pos + 2);
            Ok(())
        }
        None => Err(LexingError::UnterminatedBlockComment),
    }
}

/// A token produced by the lexer. Data-carrying variants hold the source text
/// (`Id`, `Positive`); all other variants are unit. Span is separated — see
/// `lex_iter()` which yields `(Token, SimpleSpan)` pairs.
///
/// `PartialEq` is derived: unit variants compare trivially, data variants
/// compare by text. This is correct because `just()` (which requires
/// `PartialEq`) is only used for unit variants; data variants use `select!`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    // Punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,
    LAngle,
    RAngle,
    Comma,
    Semi,
    Colon,
    Eq,
    Arrow,
    FatArrow,
    EqEq,
    Dot,
    DotDot,
    LArrow,
    LBraceBar,
    BarRBrace,
    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    Percent,
    PlusPlus,
    // Literals — carry source text
    Positive(String),
    // Identifiers — carry source text
    Id(String),
    // Keywords
    KwLet,
    KwFn,
    KwProto,
    KwType,
    KwFun,
    KwFor,
    KwIn,
    KwInterpolate,
    KwPoly,
    KwEval,
    KwCoef,
    KwMle,
    KwDot,
    KwReduce,
    KwRandom,
    KwChallenge,
    KwAssert,
    KwVerify,
    KwPair,
    KwWhere,
    KwInstance,
    KwWitness,
    KwExtra,
    KwUniform,
    KwField,
    KwGroup,
    KwPairing,
    KwScalar,
    KwSize,
    KwUnit,
    KwFin,
    KwPolyTy,
    KwUni,
    KwMleTy,
    // Trivia
    Whitespace,
    LineComment,
    BlockComment,
    // Error
    Error,
}

impl Token {
    /// Trivia tokens are preserved in the token stream but carry no semantic
    /// meaning. The parser skips them; the formatter keeps them.
    pub fn is_trivia(&self) -> bool {
        matches!(
            self,
            Token::Whitespace | Token::LineComment | Token::BlockComment
        )
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Id(s) | Token::Positive(s) => write!(f, "{s}"),
            // Punctuation
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBrack => write!(f, "["),
            Token::RBrack => write!(f, "]"),
            Token::LAngle => write!(f, "<"),
            Token::RAngle => write!(f, ">"),
            Token::Comma => write!(f, ","),
            Token::Semi => write!(f, ";"),
            Token::Colon => write!(f, ":"),
            Token::Eq => write!(f, "="),
            Token::Arrow => write!(f, "->"),
            Token::FatArrow => write!(f, "=>"),
            Token::EqEq => write!(f, "=="),
            Token::Dot => write!(f, "."),
            Token::DotDot => write!(f, ".."),
            Token::LArrow => write!(f, "<-"),
            Token::LBraceBar => write!(f, "{{|"),
            Token::BarRBrace => write!(f, "|}}"),
            // Operators
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Caret => write!(f, "^"),
            Token::Percent => write!(f, "%"),
            Token::PlusPlus => write!(f, "++"),
            // Keywords
            Token::KwLet => write!(f, "let"),
            Token::KwFn => write!(f, "fn"),
            Token::KwProto => write!(f, "proto"),
            Token::KwType => write!(f, "type"),
            Token::KwFun => write!(f, "fun"),
            Token::KwFor => write!(f, "for"),
            Token::KwIn => write!(f, "in"),
            Token::KwInterpolate => write!(f, "interpolate"),
            Token::KwPoly => write!(f, "poly"),
            Token::KwEval => write!(f, "eval"),
            Token::KwCoef => write!(f, "coef"),
            Token::KwMle => write!(f, "mle"),
            Token::KwDot => write!(f, "dot"),
            Token::KwReduce => write!(f, "reduce"),
            Token::KwRandom => write!(f, "random"),
            Token::KwChallenge => write!(f, "challenge"),
            Token::KwAssert => write!(f, "assert"),
            Token::KwVerify => write!(f, "verify"),
            Token::KwPair => write!(f, "pair"),
            Token::KwWhere => write!(f, "where"),
            Token::KwInstance => write!(f, "instance"),
            Token::KwWitness => write!(f, "witness"),
            Token::KwExtra => write!(f, "extra"),
            Token::KwUniform => write!(f, "uniform"),
            Token::KwField => write!(f, "Field"),
            Token::KwGroup => write!(f, "Group"),
            Token::KwPairing => write!(f, "Pairing"),
            Token::KwScalar => write!(f, "Scalar"),
            Token::KwSize => write!(f, "Size"),
            Token::KwUnit => write!(f, "Unit"),
            Token::KwFin => write!(f, "Fin"),
            Token::KwPolyTy => write!(f, "Poly"),
            Token::KwUni => write!(f, "Uni"),
            Token::KwMleTy => write!(f, "Mle"),
            // Trivia / error
            Token::Whitespace => write!(f, "whitespace"),
            Token::LineComment => write!(f, "line comment"),
            Token::BlockComment => write!(f, "block comment"),
            Token::Error => write!(f, "invalid token"),
        }
    }
}

/// Internal logos enum. Logos generates a DFA at compile time from the
/// `#[regex]`/`#[token]` attributes. Keywords are lexed as `Ident` and
/// post-processed into keyword kinds via a lookup table.
///
/// Token ordering: logos matches longest-first for `#[token]`, so `++`
/// is preferred over `+`, `==` over `=`, `->` over `-`, `..` over `.`,
/// `<-` over `<`. We also declare longer tokens first as a safety net.
#[derive(Logos, Debug, PartialEq, Eq)]
#[logos(error = LexingError)]
enum RawToken {
    // Trivia
    #[regex(r"[ \t\r\n]+")]
    Whitespace,

    #[regex(r"//[^\n]*")]
    LineComment,

    // Block comment: /* ... */ with no nesting.
    // Uses a callback (the idiomatic logos pattern for comments/raw strings)
    // because logos's DFA can't match /* ... */ without backtracking.
    #[token("/*", block_comment_end)]
    BlockComment,

    // Multi-char punctuation (declared before single-char to ensure longest match)
    #[token("++")]
    PlusPlus,

    #[token("==")]
    EqEq,

    #[token("=>")]
    FatArrow,

    #[token("->")]
    Arrow,

    #[token("<-")]
    LArrow,

    #[token("..")]
    DotDot,

    #[token("{|")]
    LBraceBar,

    #[token("|}")]
    BarRBrace,

    // Single-char punctuation
    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[token("[")]
    LBrack,

    #[token("]")]
    RBrack,

    #[token("<")]
    LAngle,

    #[token(">")]
    RAngle,

    #[token(",")]
    Comma,

    #[token(";")]
    Semi,

    #[token(":")]
    Colon,

    #[token("=")]
    Eq,

    #[token(".")]
    Dot,

    // Operators
    #[token("+")]
    Plus,

    #[token("-")]
    Minus,

    #[token("*")]
    Star,

    #[token("/")]
    Slash,

    #[token("^")]
    Caret,

    #[token("%")]
    Percent,

    // Literals
    #[regex(r"[0-9]+")]
    Positive,

    // Identifiers — post-processed for keywords
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_']*")]
    Ident,

    // Catch-all: any single character that didn't match above.
    // This prevents logos from returning Err for unknown characters,
    // letting logos handle the byte advancement internally.
    // Mapped to Token::Error in raw_to_token.
    #[regex(r".", priority = 0)]
    #[regex(r"\n", priority = 0)]
    Unknown,
}

/// Keyword lookup table. Maps keyword text to the corresponding `Token` variant.
const KEYWORDS: &[(&str, Token)] = &[
    // Declaration keywords
    ("let", Token::KwLet),
    ("fn", Token::KwFn),
    ("proto", Token::KwProto),
    ("type", Token::KwType),
    // Expression keywords
    ("fun", Token::KwFun),
    ("for", Token::KwFor),
    ("in", Token::KwIn),
    ("interpolate", Token::KwInterpolate),
    ("poly", Token::KwPoly),
    ("eval", Token::KwEval),
    ("coef", Token::KwCoef),
    ("mle", Token::KwMle),
    ("dot", Token::KwDot),
    ("reduce", Token::KwReduce),
    ("random", Token::KwRandom),
    ("challenge", Token::KwChallenge),
    ("assert", Token::KwAssert),
    ("verify", Token::KwVerify),
    ("pair", Token::KwPair),
    ("where", Token::KwWhere),
    // Qualifier / distribution keywords
    ("instance", Token::KwInstance),
    ("witness", Token::KwWitness),
    ("extra", Token::KwExtra),
    ("uniform", Token::KwUniform),
    // Type keywords (uppercase)
    ("Field", Token::KwField),
    ("Group", Token::KwGroup),
    ("Pairing", Token::KwPairing),
    ("Scalar", Token::KwScalar),
    ("Size", Token::KwSize),
    ("Unit", Token::KwUnit),
    ("Fin", Token::KwFin),
    ("Poly", Token::KwPolyTy),
    ("Uni", Token::KwUni),
    ("Mle", Token::KwMleTy),
];

/// Map a `RawToken` to a `Token`, performing keyword lookup for identifiers.
fn raw_to_token(raw: &RawToken, text: &str) -> Token {
    match raw {
        RawToken::Whitespace => Token::Whitespace,
        RawToken::LineComment => Token::LineComment,
        RawToken::BlockComment => Token::BlockComment,
        RawToken::PlusPlus => Token::PlusPlus,
        RawToken::EqEq => Token::EqEq,
        RawToken::FatArrow => Token::FatArrow,
        RawToken::Arrow => Token::Arrow,
        RawToken::LArrow => Token::LArrow,
        RawToken::DotDot => Token::DotDot,
        RawToken::LBraceBar => Token::LBraceBar,
        RawToken::BarRBrace => Token::BarRBrace,
        RawToken::LParen => Token::LParen,
        RawToken::RParen => Token::RParen,
        RawToken::LBrace => Token::LBrace,
        RawToken::RBrace => Token::RBrace,
        RawToken::LBrack => Token::LBrack,
        RawToken::RBrack => Token::RBrack,
        RawToken::LAngle => Token::LAngle,
        RawToken::RAngle => Token::RAngle,
        RawToken::Comma => Token::Comma,
        RawToken::Semi => Token::Semi,
        RawToken::Colon => Token::Colon,
        RawToken::Eq => Token::Eq,
        RawToken::Dot => Token::Dot,
        RawToken::Plus => Token::Plus,
        RawToken::Minus => Token::Minus,
        RawToken::Star => Token::Star,
        RawToken::Slash => Token::Slash,
        RawToken::Caret => Token::Caret,
        RawToken::Percent => Token::Percent,
        RawToken::Positive => Token::Positive(text.to_string()),
        RawToken::Ident => {
            // Binary search would be faster, but the table is small (34 entries)
            // and linear search is branch-predictable.
            KEYWORDS
                .iter()
                .find(|(kw, _)| *kw == text)
                .map(|(_, tok)| tok.clone())
                .unwrap_or_else(|| Token::Id(text.to_string()))
        }
        RawToken::Unknown => Token::Error,
    }
}

/// Lex source text into a lazy iterator of `(Token, SimpleSpan)`.
///
/// Every token — including trivia (whitespace, comments) — gets a span.
/// The stream is lossless: concatenating `&src[span]` for all tokens
/// reproduces the original source.
///
/// Unknown characters produce `Token::Error` tokens (one per character).
pub fn lex_iter<'src>(src: &'src str) -> impl Iterator<Item = (Token, SimpleSpan)> + 'src {
    let mut lexer = RawToken::lexer(src);
    let mut done = false;

    std::iter::from_fn(move || {
        if done {
            return None;
        }
        match lexer.next() {
            None => {
                done = true;
                None
            }
            Some(Ok(raw)) => {
                let span = lexer.span();
                let text = &src[span.clone()];
                let tok = raw_to_token(&raw, text);
                Some((tok, span.into()))
            }
            Some(Err(LexingError::UnterminatedBlockComment)) => {
                let span = lexer.span();
                done = true;
                Some((Token::Error, (span.start..src.len()).into()))
            }
            Some(Err(_)) => {
                unreachable!("lexer error with Unknown catch-all in place")
            }
        }
    })
}

// ── Tests ──────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Collect all tokens from `lex_iter` into a `Vec` (test helper).
    fn lex(src: &str) -> Vec<(Token, SimpleSpan)> {
        lex_iter(src).collect()
    }

    /// Assert that lexing `src` produces exactly the expected tokens
    /// (ignoring spans). Convenience for readable tests.
    fn assert_tokens(src: &str, expected: &[Token]) {
        let tokens: Vec<Token> = lex(src).into_iter().map(|(t, _)| t).collect();
        assert_eq!(tokens, expected, "source: {:?}", src);
    }

    #[test]
    fn lex_empty() {
        assert!(lex("").is_empty());
    }

    #[test]
    fn lex_whitespace() {
        assert_tokens("   \n\t  ", &[Token::Whitespace]);
    }

    #[test]
    fn lex_line_comment() {
        assert_tokens("// hello\n", &[Token::LineComment, Token::Whitespace]);
    }

    #[test]
    fn lex_block_comment() {
        assert_tokens("/* hello */", &[Token::BlockComment]);
    }

    #[test]
    fn lex_block_comment_multiline() {
        assert_tokens("/* line 1\nline 2 */", &[Token::BlockComment]);
    }

    #[test]
    fn lex_unterminated_block_comment() {
        // Unterminated block comment → single ERROR token spanning to end of input
        let tokens = lex("/* unterminated");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].0, Token::Error);
        assert_eq!(tokens[0].1.into_range(), 0..15);
    }

    #[test]
    fn lex_block_comment_before_code() {
        // Code after a terminated block comment should still lex normally
        assert_tokens(
            "/* comment */ fn",
            &[Token::BlockComment, Token::Whitespace, Token::KwFn],
        );
    }

    #[test]
    fn lex_invalid_char_recovery() {
        // `$` is not a valid token — should produce ERROR token with correct span
        let tokens = lex("fn $");
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].0, Token::KwFn);
        assert_eq!(tokens[0].1.into_range(), 0..2);
        assert_eq!(tokens[1].0, Token::Whitespace);
        assert_eq!(tokens[1].1.into_range(), 2..3);
        assert_eq!(tokens[2].0, Token::Error);
        assert_eq!(tokens[2].1.into_range(), 3..4);
    }

    #[test]
    fn lex_invalid_char_at_start() {
        // Invalid char at position 0 — span should be 0..1
        let tokens = lex("$ fn");
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].0, Token::Error);
        assert_eq!(tokens[0].1.into_range(), 0..1);
        assert_eq!(tokens[1].0, Token::Whitespace);
        assert_eq!(tokens[1].1.into_range(), 1..2);
        assert_eq!(tokens[2].0, Token::KwFn);
        assert_eq!(tokens[2].1.into_range(), 2..4);
    }

    #[test]
    fn lex_lossless_with_invalid_char() {
        // Lossless property should hold even with error tokens
        let src = "fn $ a";
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|(_, s)| &src[s.into_range()]).collect();
        assert_eq!(reconstructed, src);
    }

    #[test]
    fn lex_punctuation() {
        assert_tokens(
            "(){}[]<>;:,=.",
            &[
                Token::LParen,
                Token::RParen,
                Token::LBrace,
                Token::RBrace,
                Token::LBrack,
                Token::RBrack,
                Token::LAngle,
                Token::RAngle,
                Token::Semi,
                Token::Colon,
                Token::Comma,
                Token::Eq,
                Token::Dot,
            ],
        );
    }

    #[test]
    fn lex_multi_char_punctuation() {
        assert_tokens(
            "++ == -> <- .. {| |}",
            &[
                Token::PlusPlus,
                Token::Whitespace,
                Token::EqEq,
                Token::Whitespace,
                Token::Arrow,
                Token::Whitespace,
                Token::LArrow,
                Token::Whitespace,
                Token::DotDot,
                Token::Whitespace,
                Token::LBraceBar,
                Token::Whitespace,
                Token::BarRBrace,
            ],
        );
    }

    #[test]
    fn lex_operators() {
        assert_tokens(
            "+ - * / ^ %",
            &[
                Token::Plus,
                Token::Whitespace,
                Token::Minus,
                Token::Whitespace,
                Token::Star,
                Token::Whitespace,
                Token::Slash,
                Token::Whitespace,
                Token::Caret,
                Token::Whitespace,
                Token::Percent,
            ],
        );
    }

    #[test]
    fn lex_positive() {
        assert_tokens("42", &[Token::Positive("42".to_string())]);
        assert_tokens(
            "0 1 123",
            &[
                Token::Positive("0".to_string()),
                Token::Whitespace,
                Token::Positive("1".to_string()),
                Token::Whitespace,
                Token::Positive("123".to_string()),
            ],
        );
    }

    #[test]
    fn lex_identifier() {
        assert_tokens("foo", &[Token::Id("foo".to_string())]);
        assert_tokens("x_1'", &[Token::Id("x_1'".to_string())]);
        assert_tokens(
            "a b c",
            &[
                Token::Id("a".to_string()),
                Token::Whitespace,
                Token::Id("b".to_string()),
                Token::Whitespace,
                Token::Id("c".to_string()),
            ],
        );
    }

    #[test]
    fn lex_keywords() {
        assert_tokens(
            "let fn proto type",
            &[
                Token::KwLet,
                Token::Whitespace,
                Token::KwFn,
                Token::Whitespace,
                Token::KwProto,
                Token::Whitespace,
                Token::KwType,
            ],
        );
        assert_tokens(
            "Field Group Scalar Size Unit",
            &[
                Token::KwField,
                Token::Whitespace,
                Token::KwGroup,
                Token::Whitespace,
                Token::KwScalar,
                Token::Whitespace,
                Token::KwSize,
                Token::Whitespace,
                Token::KwUnit,
            ],
        );
        assert_tokens(
            "random challenge assert verify",
            &[
                Token::KwRandom,
                Token::Whitespace,
                Token::KwChallenge,
                Token::Whitespace,
                Token::KwAssert,
                Token::Whitespace,
                Token::KwVerify,
            ],
        );
    }

    #[test]
    fn lex_keyword_not_prefix() {
        // "leto" should be an identifier, not KW_LET + "o"
        assert_tokens("leto", &[Token::Id("leto".to_string())]);
        // "fnord" should be an identifier
        assert_tokens("fnord", &[Token::Id("fnord".to_string())]);
        // "types" should be an identifier
        assert_tokens("types", &[Token::Id("types".to_string())]);
    }

    #[test]
    fn lex_schnorr_proto() {
        let src = "proto schnorr<G: Group>(witness x: F) where h == g*x { }";
        let tokens = lex(src);
        // Verify the first few tokens
        assert_eq!(tokens[0].0, Token::KwProto);
        assert_eq!(tokens[1].0, Token::Whitespace);
        assert_eq!(tokens[2].0, Token::Id("schnorr".to_string()));
        assert_eq!(tokens[3].0, Token::LAngle);
        assert_eq!(tokens[4].0, Token::Id("G".to_string()));
        assert_eq!(tokens[5].0, Token::Colon);
        assert_eq!(tokens[6].0, Token::Whitespace);
        assert_eq!(tokens[7].0, Token::KwGroup);
    }

    #[test]
    fn lex_range() {
        assert_tokens(
            "0..N",
            &[
                Token::Positive("0".to_string()),
                Token::DotDot,
                Token::Id("N".to_string()),
            ],
        );
    }

    #[test]
    fn lex_projection_vs_range() {
        // `a.b` → ID DOT ID (projection)
        assert_tokens(
            "a.b",
            &[
                Token::Id("a".to_string()),
                Token::Dot,
                Token::Id("b".to_string()),
            ],
        );
        // `a..b` → ID DOTDOT ID (range)
        assert_tokens(
            "a..b",
            &[
                Token::Id("a".to_string()),
                Token::DotDot,
                Token::Id("b".to_string()),
            ],
        );
    }

    #[test]
    fn lex_record() {
        assert_tokens(
            "{| x: 1 |}",
            &[
                Token::LBraceBar,
                Token::Whitespace,
                Token::Id("x".to_string()),
                Token::Colon,
                Token::Whitespace,
                Token::Positive("1".to_string()),
                Token::Whitespace,
                Token::BarRBrace,
            ],
        );
    }

    #[test]
    fn lex_transcript_log() {
        assert_tokens(
            "u <- g*r",
            &[
                Token::Id("u".to_string()),
                Token::Whitespace,
                Token::LArrow,
                Token::Whitespace,
                Token::Id("g".to_string()),
                Token::Star,
                Token::Id("r".to_string()),
            ],
        );
    }

    /// Lossless property: concatenating token text reproduces the source.
    #[test]
    fn lossless_simple() {
        let src = "fn f<F: Field>(instance a: F) -> F { a }";
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|(_, s)| &src[s.into_range()]).collect();
        assert_eq!(reconstructed, src);
    }

    #[test]
    fn lossless_with_comments() {
        let src = "fn f<F: Field>(instance a: F) -> F { // comment\n a }";
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|(_, s)| &src[s.into_range()]).collect();
        assert_eq!(reconstructed, src);
    }

    #[test]
    fn lossless_schnorr() {
        let src = include_str!("../../../examples/schnorr/schnorr.zippel");
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|(_, s)| &src[s.into_range()]).collect();
        assert_eq!(reconstructed, src);
    }

    /// Verify spans are contiguous and non-overlapping.
    #[test]
    fn spans_contiguous() {
        let src = "fn f<F: Field>(instance a: F) -> F { a }";
        let tokens = lex(src);
        for i in 0..tokens.len() {
            let span = tokens[i].1.into_range();
            assert_eq!(
                span.start,
                if i == 0 {
                    0
                } else {
                    tokens[i - 1].1.into_range().end
                },
                "gap or overlap at token {} ({:?})",
                i,
                tokens[i].0
            );
        }
        // Last token ends at src.len()
        assert_eq!(tokens.last().unwrap().1.into_range().end, src.len());
    }

    /// Lex all 38 examples and verify the lossless property.
    #[test]
    fn lossless_all_examples() {
        // Tests run from the crate root (lang/). The examples directory is
        // at the workspace root, one level up.
        let examples_dir = std::path::Path::new("../examples");
        let mut count = 0;
        for entry in std::fs::read_dir(examples_dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }
            for file in std::fs::read_dir(&path).unwrap() {
                let file = file.unwrap();
                let path = file.path();
                if path.extension().is_none_or(|e| e != "zippel") {
                    continue;
                }
                let src = std::fs::read_to_string(&path).unwrap();
                let tokens = lex(&src);
                let reconstructed: String =
                    tokens.iter().map(|(_, s)| &src[s.into_range()]).collect();
                assert_eq!(
                    reconstructed,
                    src,
                    "lossless property failed for {}",
                    path.display()
                );
                // Verify contiguous spans
                for i in 0..tokens.len() {
                    let span = tokens[i].1.into_range();
                    assert_eq!(
                        span.start,
                        if i == 0 {
                            0
                        } else {
                            tokens[i - 1].1.into_range().end
                        },
                        "span gap in {} at token {}",
                        path.display(),
                        i
                    );
                }
                assert_eq!(tokens.last().unwrap().1.into_range().end, src.len());
                count += 1;
            }
        }
        assert_eq!(count, 38, "expected 38 .zippel examples");
    }
}
