//! Logos-based lexer for Zippel.
//!
//! Turns `&str` into `Vec<Token>` where every token — including trivia
//! (whitespace, comments) and punctuation — has a `SyntaxKind` and a byte
//! `Span`. This is the key difference from pest: there are no "silent" tokens.
//!
//! The token stream is lossless: `src == tokens.map(|t| &src[t.span]).collect()`.

use logos::{Lexer, Logos};
use std::ops::Range;

use crate::kind::SyntaxKind;

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

/// A single token with its byte span in the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: SyntaxKind,
    pub span: Range<usize>,
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
    // Mapped to SyntaxKind::ERROR in raw_to_kind.
    #[regex(r".", priority = 0)]
    #[regex(r"\n", priority = 0)]
    Unknown,
}

/// Keyword lookup table. Derived from the pest grammar's `keyword` rule
/// (line 21) plus all keyword-like identifiers used in expression/type rules.
const KEYWORDS: &[(&str, SyntaxKind)] = &[
    // Declaration keywords
    ("let", SyntaxKind::KW_LET),
    ("fn", SyntaxKind::KW_FN),
    ("proto", SyntaxKind::KW_PROTO),
    ("type", SyntaxKind::KW_TYPE),
    // Expression keywords
    ("fun", SyntaxKind::KW_FUN),
    ("for", SyntaxKind::KW_FOR),
    ("in", SyntaxKind::KW_IN),
    ("interpolate", SyntaxKind::KW_INTERPOLATE),
    ("poly", SyntaxKind::KW_POLY),
    ("eval", SyntaxKind::KW_EVAL),
    ("coef", SyntaxKind::KW_COEF),
    ("mle", SyntaxKind::KW_MLE),
    ("dot", SyntaxKind::KW_DOT),
    ("reduce", SyntaxKind::KW_REDUCE),
    ("random", SyntaxKind::KW_RANDOM),
    ("challenge", SyntaxKind::KW_CHALLENGE),
    ("assert", SyntaxKind::KW_ASSERT),
    ("verify", SyntaxKind::KW_VERIFY),
    ("pair", SyntaxKind::KW_PAIR),
    ("where", SyntaxKind::KW_WHERE),
    // Qualifier / distribution keywords
    ("instance", SyntaxKind::KW_INSTANCE),
    ("witness", SyntaxKind::KW_WITNESS),
    ("extra", SyntaxKind::KW_EXTRA),
    ("uniform", SyntaxKind::KW_UNIFORM),
    // Type keywords (uppercase)
    ("Field", SyntaxKind::KW_FIELD),
    ("Group", SyntaxKind::KW_GROUP),
    ("Pairing", SyntaxKind::KW_PAIRING),
    ("Scalar", SyntaxKind::KW_SCALAR),
    ("Size", SyntaxKind::KW_SIZE),
    ("Unit", SyntaxKind::KW_UNIT),
    ("Fin", SyntaxKind::KW_FIN),
    ("Poly", SyntaxKind::KW_POLY_TY),
    ("Uni", SyntaxKind::KW_UNI),
    ("Mle", SyntaxKind::KW_MLE_TY),
];

/// Map a `RawToken` to its `SyntaxKind`, performing keyword lookup for
/// identifiers.
fn raw_to_kind(raw: &RawToken, text: &str) -> SyntaxKind {
    match raw {
        RawToken::Whitespace => SyntaxKind::WHITESPACE,
        RawToken::LineComment => SyntaxKind::LINE_COMMENT,
        RawToken::BlockComment => SyntaxKind::BLOCK_COMMENT,
        RawToken::PlusPlus => SyntaxKind::PLUS_PLUS,
        RawToken::EqEq => SyntaxKind::EQ_EQ,
        RawToken::FatArrow => SyntaxKind::FAT_ARROW,
        RawToken::Arrow => SyntaxKind::ARROW,
        RawToken::LArrow => SyntaxKind::LARROW,
        RawToken::DotDot => SyntaxKind::DOTDOT,
        RawToken::LBraceBar => SyntaxKind::LBRACE_BAR,
        RawToken::BarRBrace => SyntaxKind::BAR_RBRACE,
        RawToken::LParen => SyntaxKind::LPAREN,
        RawToken::RParen => SyntaxKind::RPAREN,
        RawToken::LBrace => SyntaxKind::LBRACE,
        RawToken::RBrace => SyntaxKind::RBRACE,
        RawToken::LBrack => SyntaxKind::LBRACK,
        RawToken::RBrack => SyntaxKind::RBRACK,
        RawToken::LAngle => SyntaxKind::LANGLE,
        RawToken::RAngle => SyntaxKind::RANGLE,
        RawToken::Comma => SyntaxKind::COMMA,
        RawToken::Semi => SyntaxKind::SEMI,
        RawToken::Colon => SyntaxKind::COLON,
        RawToken::Eq => SyntaxKind::EQ,
        RawToken::Dot => SyntaxKind::DOT,
        RawToken::Plus => SyntaxKind::PLUS,
        RawToken::Minus => SyntaxKind::MINUS,
        RawToken::Star => SyntaxKind::STAR,
        RawToken::Slash => SyntaxKind::SLASH,
        RawToken::Caret => SyntaxKind::CARET,
        RawToken::Percent => SyntaxKind::PERCENT,
        RawToken::Positive => SyntaxKind::POSITIVE,
        RawToken::Ident => {
            // Binary search would be faster, but the table is small (34 entries)
            // and linear search is branch-predictable.
            KEYWORDS
                .iter()
                .find(|(kw, _)| *kw == text)
                .map(|(_, kind)| *kind)
                .unwrap_or(SyntaxKind::ID)
        }
        RawToken::Unknown => SyntaxKind::ERROR,
    }
}

/// Lex source text into a token stream.
///
/// Every token — including trivia (whitespace, comments) — gets a span.
/// The stream is lossless: concatenating `&src[t.span]` for all tokens
/// reproduces the original source.
///
/// Unknown characters produce `SyntaxKind::ERROR` tokens (one per character).
pub fn lex(src: &str) -> Vec<Token> {
    let mut lexer = RawToken::lexer(src);
    let mut tokens = Vec::new();

    loop {
        match lexer.next() {
            None => break,
            Some(Ok(raw)) => {
                let span = lexer.span();
                let text = &src[span.clone()];
                let kind = raw_to_kind(&raw, text);
                tokens.push(Token { kind, span });
            }
            Some(Err(LexingError::UnterminatedBlockComment)) => {
                // The `/*` was matched but no closing `*/` was found.
                // The lexer span covers only the `/*` — extend to end of
                // input so the error token marks the whole unterminated
                // comment region.
                let span = lexer.span();
                tokens.push(Token {
                    kind: SyntaxKind::ERROR,
                    span: span.start..src.len(),
                });
                break;
            }
            Some(Err(_)) => {
                // Unreachable: the Unknown catch-all regex matches any single
                // character, so logos should never return Err for unknown input.
                // If we get here, it's a bug in the lexer definition.
                unreachable!("lexer error with Unknown catch-all in place")
            }
        }
    }

    tokens
}

// ── Tests ──────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Assert that lexing `src` produces exactly the expected token kinds
    /// (ignoring spans). Convenience for readable tests.
    fn assert_kinds(src: &str, expected: &[SyntaxKind]) {
        let tokens: Vec<SyntaxKind> = lex(src).into_iter().map(|t| t.kind).collect();
        assert_eq!(tokens, expected, "source: {:?}", src);
    }

    #[test]
    fn lex_empty() {
        assert!(lex("").is_empty());
    }

    #[test]
    fn lex_whitespace() {
        assert_kinds("   \n\t  ", &[SyntaxKind::WHITESPACE]);
    }

    #[test]
    fn lex_line_comment() {
        assert_kinds(
            "// hello\n",
            &[SyntaxKind::LINE_COMMENT, SyntaxKind::WHITESPACE],
        );
    }

    #[test]
    fn lex_block_comment() {
        assert_kinds("/* hello */", &[SyntaxKind::BLOCK_COMMENT]);
    }

    #[test]
    fn lex_block_comment_multiline() {
        assert_kinds("/* line 1\nline 2 */", &[SyntaxKind::BLOCK_COMMENT]);
    }

    #[test]
    fn lex_unterminated_block_comment() {
        // Unterminated block comment → single ERROR token spanning to end of input
        let tokens = lex("/* unterminated");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, SyntaxKind::ERROR);
        assert_eq!(tokens[0].span, 0..15);
    }

    #[test]
    fn lex_block_comment_before_code() {
        // Code after a terminated block comment should still lex normally
        assert_kinds(
            "/* comment */ fn",
            &[
                SyntaxKind::BLOCK_COMMENT,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_FN,
            ],
        );
    }

    #[test]
    fn lex_invalid_char_recovery() {
        // `$` is not a valid token — should produce ERROR token with correct span
        let tokens = lex("fn $");
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].kind, SyntaxKind::KW_FN);
        assert_eq!(tokens[0].span, 0..2);
        assert_eq!(tokens[1].kind, SyntaxKind::WHITESPACE);
        assert_eq!(tokens[1].span, 2..3);
        assert_eq!(tokens[2].kind, SyntaxKind::ERROR);
        assert_eq!(tokens[2].span, 3..4);
    }

    #[test]
    fn lex_invalid_char_at_start() {
        // Invalid char at position 0 — span should be 0..1
        let tokens = lex("$ fn");
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].kind, SyntaxKind::ERROR);
        assert_eq!(tokens[0].span, 0..1);
        assert_eq!(tokens[1].kind, SyntaxKind::WHITESPACE);
        assert_eq!(tokens[1].span, 1..2);
        assert_eq!(tokens[2].kind, SyntaxKind::KW_FN);
        assert_eq!(tokens[2].span, 2..4);
    }

    #[test]
    fn lex_lossless_with_invalid_char() {
        // Lossless property should hold even with error tokens
        let src = "fn $ a";
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|t| &src[t.span.clone()]).collect();
        assert_eq!(reconstructed, src);
    }

    #[test]
    fn lex_punctuation() {
        assert_kinds(
            "(){}[]<>;:,=.",
            &[
                SyntaxKind::LPAREN,
                SyntaxKind::RPAREN,
                SyntaxKind::LBRACE,
                SyntaxKind::RBRACE,
                SyntaxKind::LBRACK,
                SyntaxKind::RBRACK,
                SyntaxKind::LANGLE,
                SyntaxKind::RANGLE,
                SyntaxKind::SEMI,
                SyntaxKind::COLON,
                SyntaxKind::COMMA,
                SyntaxKind::EQ,
                SyntaxKind::DOT,
            ],
        );
    }

    #[test]
    fn lex_multi_char_punctuation() {
        assert_kinds(
            "++ == -> <- .. {| |}",
            &[
                SyntaxKind::PLUS_PLUS,
                SyntaxKind::WHITESPACE,
                SyntaxKind::EQ_EQ,
                SyntaxKind::WHITESPACE,
                SyntaxKind::ARROW,
                SyntaxKind::WHITESPACE,
                SyntaxKind::LARROW,
                SyntaxKind::WHITESPACE,
                SyntaxKind::DOTDOT,
                SyntaxKind::WHITESPACE,
                SyntaxKind::LBRACE_BAR,
                SyntaxKind::WHITESPACE,
                SyntaxKind::BAR_RBRACE,
            ],
        );
    }

    #[test]
    fn lex_operators() {
        assert_kinds(
            "+ - * / ^ %",
            &[
                SyntaxKind::PLUS,
                SyntaxKind::WHITESPACE,
                SyntaxKind::MINUS,
                SyntaxKind::WHITESPACE,
                SyntaxKind::STAR,
                SyntaxKind::WHITESPACE,
                SyntaxKind::SLASH,
                SyntaxKind::WHITESPACE,
                SyntaxKind::CARET,
                SyntaxKind::WHITESPACE,
                SyntaxKind::PERCENT,
            ],
        );
    }

    #[test]
    fn lex_positive() {
        assert_kinds("42", &[SyntaxKind::POSITIVE]);
        assert_kinds(
            "0 1 123",
            &[
                SyntaxKind::POSITIVE,
                SyntaxKind::WHITESPACE,
                SyntaxKind::POSITIVE,
                SyntaxKind::WHITESPACE,
                SyntaxKind::POSITIVE,
            ],
        );
    }

    #[test]
    fn lex_identifier() {
        assert_kinds("foo", &[SyntaxKind::ID]);
        assert_kinds("x_1'", &[SyntaxKind::ID]);
        assert_kinds(
            "a b c",
            &[
                SyntaxKind::ID,
                SyntaxKind::WHITESPACE,
                SyntaxKind::ID,
                SyntaxKind::WHITESPACE,
                SyntaxKind::ID,
            ],
        );
    }

    #[test]
    fn lex_keywords() {
        assert_kinds(
            "let fn proto type",
            &[
                SyntaxKind::KW_LET,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_FN,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_PROTO,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_TYPE,
            ],
        );
        assert_kinds(
            "Field Group Scalar Size Unit",
            &[
                SyntaxKind::KW_FIELD,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_GROUP,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_SCALAR,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_SIZE,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_UNIT,
            ],
        );
        assert_kinds(
            "random challenge assert verify",
            &[
                SyntaxKind::KW_RANDOM,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_CHALLENGE,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_ASSERT,
                SyntaxKind::WHITESPACE,
                SyntaxKind::KW_VERIFY,
            ],
        );
    }

    #[test]
    fn lex_keyword_not_prefix() {
        // "leto" should be an identifier, not KW_LET + "o"
        assert_kinds("leto", &[SyntaxKind::ID]);
        // "fnord" should be an identifier
        assert_kinds("fnord", &[SyntaxKind::ID]);
        // "types" should be an identifier
        assert_kinds("types", &[SyntaxKind::ID]);
    }

    #[test]
    fn lex_schnorr_proto() {
        let src = "proto schnorr<G: Group>(witness x: F) where h == g*x { }";
        let tokens = lex(src);
        // Verify the first few tokens
        assert_eq!(tokens[0].kind, SyntaxKind::KW_PROTO);
        assert_eq!(tokens[1].kind, SyntaxKind::WHITESPACE);
        assert_eq!(tokens[2].kind, SyntaxKind::ID);
        assert_eq!(tokens[3].kind, SyntaxKind::LANGLE);
        assert_eq!(tokens[4].kind, SyntaxKind::ID);
        assert_eq!(tokens[5].kind, SyntaxKind::COLON);
        assert_eq!(tokens[6].kind, SyntaxKind::WHITESPACE);
        assert_eq!(tokens[7].kind, SyntaxKind::KW_GROUP);
    }

    #[test]
    fn lex_range() {
        assert_kinds(
            "0..N",
            &[SyntaxKind::POSITIVE, SyntaxKind::DOTDOT, SyntaxKind::ID],
        );
    }

    #[test]
    fn lex_projection_vs_range() {
        // `a.b` → ID DOT ID (projection)
        assert_kinds("a.b", &[SyntaxKind::ID, SyntaxKind::DOT, SyntaxKind::ID]);
        // `a..b` → ID DOTDOT ID (range)
        assert_kinds(
            "a..b",
            &[SyntaxKind::ID, SyntaxKind::DOTDOT, SyntaxKind::ID],
        );
    }

    #[test]
    fn lex_record() {
        assert_kinds(
            "{| x: 1 |}",
            &[
                SyntaxKind::LBRACE_BAR,
                SyntaxKind::WHITESPACE,
                SyntaxKind::ID,
                SyntaxKind::COLON,
                SyntaxKind::WHITESPACE,
                SyntaxKind::POSITIVE,
                SyntaxKind::WHITESPACE,
                SyntaxKind::BAR_RBRACE,
            ],
        );
    }

    #[test]
    fn lex_transcript_log() {
        assert_kinds(
            "u <- g*r",
            &[
                SyntaxKind::ID,
                SyntaxKind::WHITESPACE,
                SyntaxKind::LARROW,
                SyntaxKind::WHITESPACE,
                SyntaxKind::ID,
                SyntaxKind::STAR,
                SyntaxKind::ID,
            ],
        );
    }

    /// Lossless property: concatenating token text reproduces the source.
    #[test]
    fn lossless_simple() {
        let src = "fn f<F: Field>(instance a: F) -> F { a }";
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|t| &src[t.span.clone()]).collect();
        assert_eq!(reconstructed, src);
    }

    #[test]
    fn lossless_with_comments() {
        let src = "fn f<F: Field>(instance a: F) -> F { // comment\n a }";
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|t| &src[t.span.clone()]).collect();
        assert_eq!(reconstructed, src);
    }

    #[test]
    fn lossless_schnorr() {
        let src = include_str!("../../examples/schnorr/schnorr.zippel");
        let tokens = lex(src);
        let reconstructed: String = tokens.iter().map(|t| &src[t.span.clone()]).collect();
        assert_eq!(reconstructed, src);
    }

    /// Verify spans are contiguous and non-overlapping.
    #[test]
    fn spans_contiguous() {
        let src = "fn f<F: Field>(instance a: F) -> F { a }";
        let tokens = lex(src);
        for i in 0..tokens.len() {
            assert_eq!(
                tokens[i].span.start,
                if i == 0 { 0 } else { tokens[i - 1].span.end },
                "gap or overlap at token {} ({:?})",
                i,
                tokens[i].kind
            );
        }
        // Last token ends at src.len()
        assert_eq!(tokens.last().unwrap().span.end, src.len());
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
                let reconstructed: String = tokens.iter().map(|t| &src[t.span.clone()]).collect();
                assert_eq!(
                    reconstructed,
                    src,
                    "lossless property failed for {}",
                    path.display()
                );
                // Verify contiguous spans
                for i in 0..tokens.len() {
                    assert_eq!(
                        tokens[i].span.start,
                        if i == 0 { 0 } else { tokens[i - 1].span.end },
                        "span gap in {} at token {}",
                        path.display(),
                        i
                    );
                }
                assert_eq!(tokens.last().unwrap().span.end, src.len());
                count += 1;
            }
        }
        assert_eq!(count, 38, "expected 38 .zippel examples");
    }
}
