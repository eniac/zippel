//! Chumsky parser for Zippel — produces the AST from the logos token stream.
//!
//! - Every token has a span (from the logos lexer) — no silent tokens.
//! - The precedence table is in `chumsky::pratt`, queryable — no duplication.
//! - Error recovery is built-in via chumsky.

use chumsky::pratt::{self, Associativity};
use chumsky::prelude::*;

use crate::ast::arg::Args;
use crate::ast::decl::{Decl, UDecl};
use crate::ast::{BinOp, Exps, GArg, UExp};
use crate::id::{Tid, Vid};
use crate::kind::SyntaxKind;
use crate::lexer::lex;
use crate::typ::{Distribution, GTyp, Kind, Qualifier, Range, Size, Typ, TypeVar, TypeVars};

/// A structured parse error with source location context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Byte span in the source text where the error occurred.
    pub span: std::ops::Range<usize>,
    /// 0-based line number.
    pub line: usize,
    /// 0-based column (byte offset within the line).
    pub col: usize,
    /// The source line containing the error.
    pub source_line: String,
    /// The token that was found (`None` if at end of input).
    pub found: Option<(SyntaxKind, String)>,
    /// What was expected (human-readable descriptions).
    pub expected: Vec<String>,
    /// Custom error message (for semantic errors like duplicate decls).
    /// When set, takes precedence over found/expected in Display.
    pub message: Option<String>,
}

impl ParseError {
    /// Create a custom error with a message and no source location.
    pub fn custom(msg: String) -> Self {
        ParseError {
            span: 0..0,
            line: 0,
            col: 0,
            source_line: String::new(),
            found: None,
            expected: vec![],
            message: Some(msg),
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let (line, col) = (self.line + 1, self.col + 1);

        // Always show location context if we have a source line
        if !self.source_line.is_empty() {
            writeln!(f, "parse error at line {}, column {}:", line, col)?;
            writeln!(f, "  | {}", self.source_line)?;
            writeln!(f, "  | {}^", " ".repeat(self.col))?;
        }

        if let Some(msg) = &self.message {
            return write!(f, "  {}", msg);
        }

        let found_str = self
            .found
            .as_ref()
            .map(|(k, t)| {
                // For punctuation/operators, show the literal in backticks.
                // For keywords/identifiers, show the actual text in backticks.
                let name = k.display();
                if name.chars().next().is_none_or(|c| !c.is_alphanumeric()) {
                    format!("`{}`", name)
                } else {
                    format!("`{}`", t)
                }
            })
            .unwrap_or_else(|| "end of input".to_string());

        write!(f, "  found: {}", found_str)?;
        if !self.expected.is_empty() {
            write!(f, ", expected: {}", self.expected.join(", "))?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

// ── Token type ─────────────────────────────────────────────────────────

/// A token with its text and byte span — what the parser consumes.
/// Trivia (whitespace, comments) is filtered out before parsing.
///
/// `PartialEq` compares only `kind` — two tokens are "the same" if they
/// have the same kind. This lets `just()` match a token by kind without
/// caring about text/span, producing `RichPattern::Token` in errors.
#[derive(Debug, Clone, Eq)]
pub struct Tok {
    pub kind: SyntaxKind,
    pub text: String,
    /// Byte span in the source text (for error reporting).
    pub span: std::ops::Range<usize>,
}

impl PartialEq for Tok {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

// ── Token matching helpers ─────────────────────────────────────────────

/// Match a specific `SyntaxKind`, returning the token's text.
/// Used for tokens where the actual text matters (ID, POSITIVE).
/// Uses `filter_map + labelled` which produces `RichPattern::Label` in errors.
fn tk<'src>(
    kind: SyntaxKind,
) -> impl Parser<'src, &'src [Tok], String, extra::Err<Rich<'src, Tok>>> + Clone {
    any()
        .filter_map(
            move |t: Tok| {
                if t.kind == kind {
                    Some(t.text)
                } else {
                    None
                }
            },
        )
        .labelled(kind.display().to_string())
}

/// Match a specific `SyntaxKind`, discarding the token.
/// Uses `just()` which produces `RichPattern::Token` in errors —
/// the most specific and useful error pattern.
fn sym<'src>(
    kind: SyntaxKind,
) -> impl Parser<'src, &'src [Tok], (), extra::Err<Rich<'src, Tok>>> + Clone {
    just(Tok {
        kind,
        text: String::new(),
        span: 0..0,
    })
    .ignored()
}

/// Match an identifier, returning its name as a `Vid`.
fn id_tok<'src>() -> impl Parser<'src, &'src [Tok], Vid, extra::Err<Rich<'src, Tok>>> + Clone {
    tk(SyntaxKind::ID).map(Vid)
}

/// Match an identifier, returning its name as a `Tid`.
fn tid_tok<'src>() -> impl Parser<'src, &'src [Tok], Tid, extra::Err<Rich<'src, Tok>>> + Clone {
    tk(SyntaxKind::ID).map(Tid::from)
}

/// Match a positive integer literal, returning its value.
fn positive_tok<'src>() -> impl Parser<'src, &'src [Tok], u32, extra::Err<Rich<'src, Tok>>> + Clone
{
    tk(SyntaxKind::POSITIVE).map(|s| s.parse::<u32>().unwrap_or(0))
}

// ── Size parser (pratt) ────────────────────────────────────────────────

/// Parse a size-type expression using pratt parsing.
/// Mirrors `size_ty` in the pest grammar:
///   size_ty = { size_ty_term ~ (size_bin_op ~ size_ty_term)* }
///   size_ty_term = _{ "(" ~ size_ty ~ ")" | positive | size_var }
fn size_ty_parser<'src>(
) -> impl Parser<'src, &'src [Tok], Size, extra::Err<Rich<'src, Tok>>> + Clone {
    recursive(|size_rec| {
        let atom = choice((
            sym(SyntaxKind::LPAREN)
                .ignore_then(size_rec)
                .then_ignore(sym(SyntaxKind::RPAREN)),
            positive_tok().map(Size::Lit),
            tid_tok().map(Size::Var),
        ));

        atom.pratt((
            pratt::infix(
                Associativity::Left(1),
                sym(SyntaxKind::PLUS),
                |a, _, b, _| Size::Add(Box::new(a), Box::new(b)),
            ),
            pratt::infix(
                Associativity::Left(1),
                sym(SyntaxKind::MINUS),
                |a, _, b, _| Size::Sub(Box::new(a), Box::new(b)),
            ),
            pratt::infix(
                Associativity::Left(2),
                sym(SyntaxKind::STAR),
                |a, _, b, _| Size::Mul(Box::new(a), Box::new(b)),
            ),
            pratt::infix(
                Associativity::Left(2),
                sym(SyntaxKind::SLASH),
                |a, _, b, _| Size::Div(Box::new(a), Box::new(b)),
            ),
            pratt::infix(
                Associativity::Right(3),
                sym(SyntaxKind::CARET),
                |a, _, b, _| Size::Pow(Box::new(a), Box::new(b)),
            ),
        ))
    })
}

// ── Range parser ───────────────────────────────────────────────────────

/// Parse a range expression.
/// Mirrors `range` in the pest grammar:
///   range = { step_r | unit_r }
///   step_r = { size_ty ~ "," ~ size_ty ~ ".." ~ size_ty }
///   unit_r = { size_ty ~ ".." ~ size_ty }
fn range_parser<'src>(
) -> impl Parser<'src, &'src [Tok], Range<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    choice((
        // step_r: start, step, "..", end
        size_ty_parser()
            .then_ignore(sym(SyntaxKind::COMMA))
            .then(size_ty_parser())
            .then_ignore(sym(SyntaxKind::DOTDOT))
            .then(size_ty_parser())
            .map(|((start, step), end)| Range { start, step, end }),
        // unit_r: start, "..", end (step = 1)
        size_ty_parser()
            .then_ignore(sym(SyntaxKind::DOTDOT))
            .then(size_ty_parser())
            .map(|(start, end)| Range {
                start: start.clone(),
                step: Size::Lit(1),
                end,
            }),
    ))
}

// ── Kind parser ────────────────────────────────────────────────────────

/// Parse a kind (type variable kind annotation).
/// Mirrors `kind_ty` in the pest grammar:
///   kind_ty = { field_ty | group_ty | range_ty | pairing_ty | scalar_ty | size_var_ty | size_ref_ty | positive }
fn kind_parser<'src>(
) -> impl Parser<'src, &'src [Tok], Kind<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    choice((
        kw_field(),
        kw_group(),
        kw_size(),
        pairing_kind(),
        scalar_kind(),
        range_parser().map(Kind::Range),
        // size_ref_ty: a bare size_ty → singleton range
        size_ty_parser().map(|s| {
            Kind::Range(Range {
                start: s.clone(),
                step: Size::Lit(1),
                end: s + Size::Lit(1),
            })
        }),
        // positive: a bare positive literal → singleton range
        positive_tok().map(|n| {
            Kind::Range(Range {
                start: Size::Lit(n),
                step: Size::Lit(1),
                end: Size::Lit(n + 1),
            })
        }),
    ))
}

fn kw_field<'src>(
) -> impl Parser<'src, &'src [Tok], Kind<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    sym(SyntaxKind::KW_FIELD).to(Kind::Field)
}
fn kw_group<'src>(
) -> impl Parser<'src, &'src [Tok], Kind<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    sym(SyntaxKind::KW_GROUP).to(Kind::Group)
}
fn kw_size<'src>() -> impl Parser<'src, &'src [Tok], Kind<Size>, extra::Err<Rich<'src, Tok>>> + Clone
{
    sym(SyntaxKind::KW_SIZE).to(Kind::SizeVar)
}

fn pairing_kind<'src>(
) -> impl Parser<'src, &'src [Tok], Kind<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    sym(SyntaxKind::KW_PAIRING)
        .ignore_then(sym(SyntaxKind::LANGLE))
        .ignore_then(tid_tok())
        .then_ignore(sym(SyntaxKind::COMMA))
        .then(tid_tok())
        .then_ignore(sym(SyntaxKind::RANGLE))
        .map(|(a, b)| Kind::Pairing(a, b))
}

/// Scalar<ids> — takes a comma-separated list of group type variables.
fn scalar_kind<'src>(
) -> impl Parser<'src, &'src [Tok], Kind<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    sym(SyntaxKind::KW_SCALAR)
        .ignore_then(sym(SyntaxKind::LANGLE))
        .ignore_then(
            tid_tok()
                .separated_by(sym(SyntaxKind::COMMA))
                .allow_trailing()
                .collect::<Vec<_>>(),
        )
        .then_ignore(sym(SyntaxKind::RANGLE))
        .map(|ids: Vec<Tid>| Kind::Scalar(ids.into_iter().collect()))
}

// ── Type parser ────────────────────────────────────────────────────────

/// Parse a type.
/// Mirrors `typ` in the pest grammar:
///   typ = _{ poly_ty | uni_ty | mle_ty | vec_ty | fin_ty | unit_ty | base_ty | record_ty }
fn typ_parser<'src>(
) -> impl Parser<'src, &'src [Tok], GTyp<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    recursive(|typ_rec| {
        choice((
            // Poly<F, M, N>
            sym(SyntaxKind::KW_POLY_TY)
                .ignore_then(sym(SyntaxKind::LANGLE))
                .ignore_then(tid_tok())
                .then_ignore(sym(SyntaxKind::COMMA))
                .then(size_ty_parser())
                .then_ignore(sym(SyntaxKind::COMMA))
                .then(size_ty_parser())
                .then_ignore(sym(SyntaxKind::RANGLE))
                .map(|((b, m), n)| Typ::Poly(b, m, n)),
            // Uni<F, N>
            sym(SyntaxKind::KW_UNI)
                .ignore_then(sym(SyntaxKind::LANGLE))
                .ignore_then(tid_tok())
                .then_ignore(sym(SyntaxKind::COMMA))
                .then(size_ty_parser())
                .then_ignore(sym(SyntaxKind::RANGLE))
                .map(|(b, n)| Typ::Poly(b, Size::Lit(1), n)),
            // Mle<F, N>
            sym(SyntaxKind::KW_MLE_TY)
                .ignore_then(sym(SyntaxKind::LANGLE))
                .ignore_then(tid_tok())
                .then_ignore(sym(SyntaxKind::COMMA))
                .then(size_ty_parser())
                .then_ignore(sym(SyntaxKind::RANGLE))
                .map(|(b, n)| Typ::Poly(b, n, Size::Lit(1))),
            // Fin<range> or Fin<size_ty>
            // A bare size_ty N becomes Range { start: 0, step: 1, end: N }
            sym(SyntaxKind::KW_FIN)
                .ignore_then(sym(SyntaxKind::LANGLE))
                .ignore_then(choice((
                    range_parser().map(Typ::Fin),
                    size_ty_parser().map(|s| {
                        Typ::Fin(Range {
                            start: Size::Lit(0),
                            step: Size::Lit(1),
                            end: s,
                        })
                    }),
                )))
                .then_ignore(sym(SyntaxKind::RANGLE)),
            // Unit
            sym(SyntaxKind::KW_UNIT).to(Typ::Unit),
            // Vec<T, N>  (vec_ty = { "[" ~ typ ~ ";" ~ size_ty ~ "]" })
            sym(SyntaxKind::LBRACK)
                .ignore_then(typ_rec.clone())
                .then_ignore(sym(SyntaxKind::SEMI))
                .then(size_ty_parser())
                .then_ignore(sym(SyntaxKind::RBRACK))
                .map(|(t, n)| Typ::Vec(Box::new(t), n)),
            // Record { field: typ, ... }
            sym(SyntaxKind::LBRACE)
                .ignore_then(
                    tid_tok()
                        .then_ignore(sym(SyntaxKind::COLON))
                        .then(typ_rec.clone())
                        .separated_by(sym(SyntaxKind::COMMA))
                        .allow_trailing()
                        .collect::<Vec<_>>(),
                )
                .then_ignore(sym(SyntaxKind::RBRACE))
                .map(|fields: Vec<(Tid, GTyp<Size>)>| {
                    let mut ctx = share::Ctx::new();
                    for (name, typ) in fields {
                        ctx.insert(&name.0, &typ);
                    }
                    Typ::Record(ctx)
                }),
            // Base type variable
            tid_tok().map(Typ::Base),
        ))
    })
}

// ── TypeVar parser ─────────────────────────────────────────────────────

/// Parse a type variable declaration.
/// Mirrors `tvar = { id ~ ":" ~ kind_ty }`
fn tvar_parser<'src>(
) -> impl Parser<'src, &'src [Tok], TypeVar<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    tid_tok()
        .then_ignore(sym(SyntaxKind::COLON))
        .then(kind_parser())
        .map(|(id, kind)| TypeVar { id, kind })
}

/// Parse a list of type variables.
/// Mirrors `tvars = { tvar ~ ("," ~ tvar)* }`
fn tvars_parser<'src>(
) -> impl Parser<'src, &'src [Tok], TypeVars<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    tvar_parser()
        .separated_by(sym(SyntaxKind::COMMA))
        .allow_trailing()
        .collect::<Vec<_>>()
        .map(|v: Vec<_>| TypeVars(v))
}

// ── Arg parser ─────────────────────────────────────────────────────────

/// Parse a qualifier.
/// Mirrors `qualifier = { instance | witness | extra }`
fn qualifier_parser<'src>(
) -> impl Parser<'src, &'src [Tok], Qualifier, extra::Err<Rich<'src, Tok>>> + Clone {
    choice((
        sym(SyntaxKind::KW_INSTANCE).to(Qualifier::Instance),
        sym(SyntaxKind::KW_WITNESS).to(Qualifier::Witness),
        sym(SyntaxKind::KW_EXTRA).to(Qualifier::Extra),
    ))
}

/// Parse a distribution.
/// Mirrors `distribution = { "uniform" ~ star? }`
fn distribution_parser<'src>(
) -> impl Parser<'src, &'src [Tok], Distribution, extra::Err<Rich<'src, Tok>>> + Clone {
    sym(SyntaxKind::KW_UNIFORM)
        .then(sym(SyntaxKind::STAR).or_not())
        .map(|(_, star)| {
            if star.is_some() {
                Distribution::UniformNonZero
            } else {
                Distribution::Uniform
            }
        })
}

/// Parse an argument.
/// Mirrors `arg = { qualifier? ~ distribution? ~ id ~ ":" ~ typ }`
fn arg_parser<'src>(
) -> impl Parser<'src, &'src [Tok], GArg<Size>, extra::Err<Rich<'src, Tok>>> + Clone {
    qualifier_parser()
        .or_not()
        .then(distribution_parser().or_not())
        .then(id_tok())
        .then_ignore(sym(SyntaxKind::COLON))
        .then(typ_parser())
        .map(|(((qual, dist), id), typ)| GArg {
            qualifier: qual.unwrap_or(Qualifier::Local),
            distribution: dist.unwrap_or(Distribution::Nonuniform),
            id,
            typ,
        })
}

// ── Binary operator parser ─────────────────────────────────────────────

/// Parse a binary operator token.
/// Mirrors `bin_op = _{ concat_op | add_op | sub_op | mul_op | div_op | pow_op | rem_op }`
fn bin_op_parser<'src>(
) -> impl Parser<'src, &'src [Tok], BinOp, extra::Err<Rich<'src, Tok>>> + Clone {
    choice((
        sym(SyntaxKind::PLUS_PLUS).to(BinOp::Concat),
        sym(SyntaxKind::PLUS).to(BinOp::Add),
        sym(SyntaxKind::MINUS).to(BinOp::Sub),
        sym(SyntaxKind::STAR).to(BinOp::Mul),
        sym(SyntaxKind::SLASH).to(BinOp::Div),
        sym(SyntaxKind::CARET).to(BinOp::Pow),
        sym(SyntaxKind::PERCENT).to(BinOp::Rem),
    ))
}

// ── Expression parser ──────────────────────────────────────────────────

/// Type alias for a boxed expression parser — needed to break the mutual
/// recursion cycle between exp_atom, exp_no_seq, and exp.
type ExpParser<'src> = Boxed<'src, 'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>>;

/// Parse an expression atom (the primary/operand for pratt parsing).
/// Takes boxed recursive references to break the mutual recursion cycle.
/// Mirrors `exp_term` in the pest grammar (lines 65-90).
fn exp_atom<'src>(
    exp_no_seq: ExpParser<'src>,
    exp: ExpParser<'src>,
) -> impl Parser<'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>> + Clone {
    choice((
        // Range expression: 0..N or 0,1..N
        // Must come before parenthesized expression so (M-1)..(M-1) is parsed as a range, not (M-1)
        range_parser().map(UExp::Range),
        // Unit value: ()
        sym(SyntaxKind::LPAREN)
            .then(sym(SyntaxKind::RPAREN))
            .to(UExp::Unit),
        // Parenthesized expression: ( exp )
        sym(SyntaxKind::LPAREN)
            .ignore_then(exp.clone())
            .then_ignore(sym(SyntaxKind::RPAREN)),
        // fun x, y => exp
        sym(SyntaxKind::KW_FUN)
            .ignore_then(
                id_tok()
                    .separated_by(sym(SyntaxKind::COMMA))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(sym(SyntaxKind::FAT_ARROW))
            .then(exp.clone())
            .map(|(vars, body)| UExp::Fun(vars, Box::new(body))),
        // interpolate(exp) or interpolate(exp, exp)
        sym(SyntaxKind::KW_INTERPOLATE)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then(
                sym(SyntaxKind::COMMA)
                    .ignore_then(exp_no_seq.clone())
                    .or_not(),
            )
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(first, second)| match second {
                None => UExp::Interpolate(None, Box::new(first)),
                Some(s) => UExp::Interpolate(Some(Box::new(first)), Box::new(s)),
            }),
        // poly(exp)
        sym(SyntaxKind::KW_POLY)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|e| UExp::Poly(Box::new(e))),
        // coef(exp)
        sym(SyntaxKind::KW_COEF)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|e| UExp::Coef(Box::new(e))),
        // mle(exp)
        sym(SyntaxKind::KW_MLE)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|e| UExp::Mle(Box::new(e))),
        // dot(exp, exp) — dot product → Bin(Dot, a, b)
        sym(SyntaxKind::KW_DOT)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::COMMA))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(a, b)| UExp::dot(a, b)),
        // random<T> or random<T*>
        sym(SyntaxKind::KW_RANDOM)
            .ignore_then(sym(SyntaxKind::LANGLE))
            .ignore_then(tid_tok())
            .then(sym(SyntaxKind::STAR).or_not())
            .then_ignore(sym(SyntaxKind::RANGLE))
            .map(|(t, star)| UExp::Random(t, star.is_some())),
        // challenge<T> or challenge<T*>
        sym(SyntaxKind::KW_CHALLENGE)
            .ignore_then(sym(SyntaxKind::LANGLE))
            .ignore_then(tid_tok())
            .then(sym(SyntaxKind::STAR).or_not())
            .then_ignore(sym(SyntaxKind::RANGLE))
            .map(|(t, star)| UExp::Challenge(t, star.is_some())),
        // [exp for x in exp] (map comprehension)
        sym(SyntaxKind::LBRACK)
            .ignore_then(exp.clone())
            .then_ignore(sym(SyntaxKind::KW_FOR))
            .then(id_tok())
            .then_ignore(sym(SyntaxKind::KW_IN))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RBRACK))
            .map(|((body, var), iter)| UExp::Map(Box::new(body), var, Box::new(iter))),
        // reduce(op, exp)
        sym(SyntaxKind::KW_REDUCE)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(bin_op_parser())
            .then_ignore(sym(SyntaxKind::COMMA))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(op, e)| UExp::Reduce(op, Box::new(e))),
        // [exp, exp, ...] (vector)
        sym(SyntaxKind::LBRACK)
            .ignore_then(
                exp_no_seq
                    .clone()
                    .separated_by(sym(SyntaxKind::COMMA))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(sym(SyntaxKind::RBRACK))
            .map(|v: Vec<_>| UExp::Vec(Exps(v))),
        // pair(exp, exp)
        sym(SyntaxKind::KW_PAIR)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::COMMA))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(a, b)| UExp::Pair(Box::new(a), Box::new(b))),
        // assert(constraint)
        sym(SyntaxKind::KW_ASSERT)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::EQ_EQ))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(lhs, rhs)| UExp::Assert(Box::new(lhs), Box::new(rhs))),
        // verify(constraint)
        sym(SyntaxKind::KW_VERIFY)
            .ignore_then(sym(SyntaxKind::LPAREN))
            .ignore_then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::EQ_EQ))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(lhs, rhs)| UExp::Verify(Box::new(lhs), Box::new(rhs))),
        // eval<range>(exp) or eval<size>(exp) or eval(exp) or eval(exp, exp)
        eval_exp_parser(exp_no_seq.clone()),
        // Record construction: {| field: val, ... |}
        sym(SyntaxKind::LBRACE_BAR)
            .ignore_then(
                id_tok()
                    .then_ignore(sym(SyntaxKind::COLON))
                    .then(exp_no_seq.clone())
                    .separated_by(sym(SyntaxKind::COMMA))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(sym(SyntaxKind::BAR_RBRACE))
            .map(|fields: Vec<(Vid, UExp)>| {
                let mut ctx = share::Ctx::new();
                for (name, val) in fields {
                    ctx.insert(&name.0, &val);
                }
                UExp::Record(ctx)
            }),
        // Positive literal
        positive_tok().map(|n| UExp::Lit(Size::Lit(n))),
        // app_exp: id(exps) — function application
        id_tok()
            .then_ignore(sym(SyntaxKind::LPAREN))
            .then(
                exp_no_seq
                    .clone()
                    .separated_by(sym(SyntaxKind::COMMA))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(sym(SyntaxKind::RPAREN))
            .map(|(id, args)| UExp::App(id, Exps(args))),
        // ram_exp: id[exp] — array access
        id_tok()
            .then_ignore(sym(SyntaxKind::LBRACK))
            .then(exp_no_seq.clone())
            .then_ignore(sym(SyntaxKind::RBRACK))
            .map(|(id, idx)| UExp::Ram(Box::new(UExp::Var(id)), Box::new(idx))),
        // Bare identifier: uppercase → Size::Var, lowercase → Exp::Var
        id_tok().map(|id| {
            if id.0.starts_with(|c: char| c.is_uppercase()) {
                UExp::Lit(Size::Var(Tid::from(id.0)))
            } else {
                UExp::Var(id)
            }
        }),
    ))
}

/// eval<range>(exp) or eval<size>(exp) or eval(exp) or eval(exp, exp)
/// Mirrors `eval_exp = { "eval" ~ eval_selector? ~ "(" ~ exp_no_seq ~ ("," ~ exp_no_seq)? ~ ")" }`
fn eval_exp_parser<'src>(
    exp_no_seq: ExpParser<'src>,
) -> impl Parser<'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>> + Clone {
    // The selector normalizes both range and size_ty to Range<Size>.
    let selector = sym(SyntaxKind::LANGLE)
        .ignore_then(choice((
            range_parser(),
            size_ty_parser().map(|s| Range {
                start: s.clone(),
                step: Size::Lit(1),
                end: s + Size::Lit(1),
            }),
        )))
        .then_ignore(sym(SyntaxKind::RANGLE))
        .or_not();

    sym(SyntaxKind::KW_EVAL)
        .ignore_then(selector)
        .then(sym(SyntaxKind::LPAREN))
        .then(exp_no_seq.clone())
        .then(sym(SyntaxKind::COMMA).ignore_then(exp_no_seq).or_not())
        .then_ignore(sym(SyntaxKind::RPAREN))
        .map(|(((sel, _), poly), second)| match (sel, second) {
            (None, None) => UExp::Evaluate(Box::new(poly), None, None),
            (None, Some(s)) => UExp::Evaluate(Box::new(poly), None, Some(Box::new(s))),
            (Some(r), Some(f)) => UExp::Evaluate(Box::new(poly), Some(r), Some(Box::new(f))),
            (Some(_), None) => UExp::Evaluate(Box::new(poly), None, None),
        })
}

/// Parse an expression without `;` sequencing, using pratt parsing.
/// Mirrors `exp_no_seq = { exp_term ~ (record_set_op | proj_op | bin_op ~ exp_term)* }`
fn exp_no_seq_parser<'src>(
) -> impl Parser<'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>> + Clone {
    recursive(|exp_no_seq_rec| {
        // Build the exp parser using the recursive exp_no_seq reference
        let exp = exp_parser_inner(exp_no_seq_rec.clone().boxed()).boxed();
        let atom = exp_atom(exp_no_seq_rec.clone().boxed(), exp);

        atom.pratt((
            // Lowest precedence first (matches AEXP_PARSER order)
            pratt::infix(
                Associativity::Left(1),
                sym(SyntaxKind::PLUS),
                |a, _, b, _| UExp::add(a, b),
            ),
            pratt::infix(
                Associativity::Left(1),
                sym(SyntaxKind::MINUS),
                |a, _, b, _| UExp::sub(a, b),
            ),
            pratt::infix(
                Associativity::Left(2),
                sym(SyntaxKind::STAR),
                |a, _, b, _| UExp::mul(a, b),
            ),
            pratt::infix(
                Associativity::Left(2),
                sym(SyntaxKind::SLASH),
                |a, _, b, _| UExp::div(a, b),
            ),
            pratt::infix(
                Associativity::Left(2),
                sym(SyntaxKind::PERCENT),
                |a, _, b, _| UExp::rem(a, b),
            ),
            pratt::infix(
                Associativity::Left(3),
                sym(SyntaxKind::PLUS_PLUS),
                |a, _, b, _| UExp::concat(a, b),
            ),
            pratt::infix(
                Associativity::Right(4),
                sym(SyntaxKind::CARET),
                |a, _, b, _| UExp::pow(a, b),
            ),
            // Prefix: unary minus → desugar to Bin(Sub, Lit(0), x)
            // Precedence 0 (lowest) — pest's `minus_exp = _{ unary_minus ~ exp_no_seq }`
            // wraps the entire following exp_no_seq, so `-b0 * z` = `-(b0 * z)`.
            pratt::prefix(0, sym(SyntaxKind::MINUS), |_, rhs, _| {
                UExp::sub(UExp::Lit(Size::Lit(0)), rhs)
            }),
            // Postfix: record set r.set(field, val) — must come before projection
            // so that `.set(` is not consumed as projection `.set`.
            // record_set_op = { "." ~ "set" ~ "(" ~ id ~ "," ~ exp_no_seq ~ ")" }
            pratt::postfix(
                6,
                sym(SyntaxKind::DOT)
                    .ignore_then(tk(SyntaxKind::ID).filter(|s: &String| s == "set"))
                    .ignore_then(sym(SyntaxKind::LPAREN))
                    .ignore_then(id_tok())
                    .then_ignore(sym(SyntaxKind::COMMA))
                    .then(exp_no_seq_rec.clone().boxed())
                    .then_ignore(sym(SyntaxKind::RPAREN)),
                |lhs, (field, val): (Vid, UExp), _| UExp::set_record(lhs, field.0, val),
            ),
            // Postfix: projection r.field
            pratt::postfix(
                6,
                sym(SyntaxKind::DOT).ignore_then(id_tok()),
                |lhs, field: Vid, _| UExp::Proj(Box::new(lhs), field.0),
            ),
        ))
    })
}

/// Inner exp parser — takes the recursive exp_no_seq reference.
/// Mirrors `exp = { let_exp | log_exp | seq_exp | exp_no_seq }`
fn exp_parser_inner<'src>(
    exp_no_seq: ExpParser<'src>,
) -> impl Parser<'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>> + Clone {
    recursive(|exp_rec| {
        choice((
            // let x = exp_no_seq; exp?
            sym(SyntaxKind::KW_LET)
                .ignore_then(id_tok())
                .then(sym(SyntaxKind::COLON).ignore_then(typ_parser()).or_not())
                .then_ignore(sym(SyntaxKind::EQ))
                .then(exp_no_seq.clone())
                .then_ignore(sym(SyntaxKind::SEMI))
                .then(exp_rec.clone().or_not())
                .map(|(((var, _typ), val), body)| {
                    UExp::Let(
                        Some(var),
                        Box::new(val),
                        Box::new(body.unwrap_or(UExp::Unit)),
                    )
                }),
            // id <- exp_no_seq; exp?  (transcript log)
            id_tok()
                .then_ignore(sym(SyntaxKind::LARROW))
                .then(exp_no_seq.clone())
                .then_ignore(sym(SyntaxKind::SEMI))
                .then(exp_rec.clone().or_not())
                .map(|((id, val), body)| {
                    UExp::Log(id, Box::new(val), Box::new(body.unwrap_or(UExp::Unit)))
                }),
            // exp_no_seq; exp?  (sequencing)
            exp_no_seq
                .clone()
                .then_ignore(sym(SyntaxKind::SEMI))
                .then(exp_rec.clone().or_not())
                .map(|(lhs, rhs)| {
                    UExp::Let(None, Box::new(lhs), Box::new(rhs.unwrap_or(UExp::Unit)))
                }),
            // exp_no_seq (no sequencing)
            exp_no_seq.clone(),
        ))
    })
}

/// Parse a top-level expression (allows `;` sequencing).
/// Public entry point — builds the full exp parser from exp_no_seq.
fn exp_parser<'src>() -> impl Parser<'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>> + Clone {
    exp_parser_inner(exp_no_seq_parser().boxed())
}

/// Parse a where clause expression.
/// Mirrors `where_exp = { where_let | where_eq | exp_no_seq }`
fn where_exp_parser<'src>(
) -> impl Parser<'src, &'src [Tok], UExp, extra::Err<Rich<'src, Tok>>> + Clone {
    recursive(|where_rec| {
        let exp_no_seq = exp_no_seq_parser().boxed();
        choice((
            // where_let: let x = exp_no_seq; where_exp?
            sym(SyntaxKind::KW_LET)
                .ignore_then(id_tok())
                .then(sym(SyntaxKind::COLON).ignore_then(typ_parser()).or_not())
                .then_ignore(sym(SyntaxKind::EQ))
                .then(exp_no_seq.clone())
                .then_ignore(sym(SyntaxKind::SEMI))
                .then(where_rec.clone().or_not())
                .map(|(((var, _typ), val), body)| {
                    UExp::Let(
                        Some(var),
                        Box::new(val),
                        Box::new(body.unwrap_or(UExp::Unit)),
                    )
                }),
            // where_eq: exp_no_seq == exp_no_seq (; where_exp?)?
            // Only wraps in seq when there's a `;` continuation.
            exp_no_seq
                .clone()
                .then_ignore(sym(SyntaxKind::EQ_EQ))
                .then(exp_no_seq.clone())
                .then(
                    sym(SyntaxKind::SEMI)
                        .ignore_then(where_rec.clone().or_not())
                        .or_not(),
                )
                .map(|((lhs, rhs), body)| {
                    let assert = UExp::Assert(Box::new(lhs), Box::new(rhs));
                    match body {
                        Some(Some(cont)) => UExp::Let(None, Box::new(assert), Box::new(cont)),
                        Some(None) => UExp::Let(None, Box::new(assert), Box::new(UExp::Unit)),
                        None => assert,
                    }
                }),
            // exp_no_seq
            exp_no_seq.clone(),
        ))
    })
}

// ── Declaration parser ─────────────────────────────────────────────────

/// Map a token-index span to a byte-offset span using the matched tokens.
/// `e.slice()` returns the slice of `Tok`s that made up this parse.
fn tok_span_to_byte_span(toks: &[Tok]) -> std::ops::Range<usize> {
    if toks.is_empty() {
        0..0
    } else {
        toks[0].span.start..toks[toks.len() - 1].span.end
    }
}

/// Parse a declaration.
/// Mirrors `decl = { proto_decl | func_decl | type_decl }`
fn decl_parser<'src>() -> impl Parser<'src, &'src [Tok], UDecl, extra::Err<Rich<'src, Tok>>> + Clone
{
    choice((
        // proto_decl = { "proto" ~ id ~ "<" ~ tvars ~ ">" ~ "(" ~ args ~ ")" ~ "where" ~ where_exp ~ "{" ~ exp ~ "}" }
        sym(SyntaxKind::KW_PROTO)
            .ignore_then(id_tok())
            .then_ignore(sym(SyntaxKind::LANGLE))
            .then(tvars_parser())
            .then_ignore(sym(SyntaxKind::RANGLE))
            .then_ignore(sym(SyntaxKind::LPAREN))
            .then(
                arg_parser()
                    .separated_by(sym(SyntaxKind::COMMA))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(sym(SyntaxKind::RPAREN))
            .then_ignore(sym(SyntaxKind::KW_WHERE))
            .then(where_exp_parser())
            .then_ignore(sym(SyntaxKind::LBRACE))
            .then(exp_parser())
            .then_ignore(sym(SyntaxKind::RBRACE))
            .map_with(|((((name, tvars), args), relation), body), e| {
                let mut d = Decl::proto(name, tvars, Args(args), relation, body);
                d.span = tok_span_to_byte_span(e.slice());
                d
            }),
        // func_decl = { "fn" ~ id ~ "<" ~ tvars ~ ">" ~ "(" ~ args ~ ")" ~ ("->" ~ typ)? ~ "{" ~ exp ~ "}" }
        sym(SyntaxKind::KW_FN)
            .ignore_then(id_tok())
            .then_ignore(sym(SyntaxKind::LANGLE))
            .then(tvars_parser())
            .then_ignore(sym(SyntaxKind::RANGLE))
            .then_ignore(sym(SyntaxKind::LPAREN))
            .then(
                arg_parser()
                    .separated_by(sym(SyntaxKind::COMMA))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(sym(SyntaxKind::RPAREN))
            .then(sym(SyntaxKind::ARROW).ignore_then(typ_parser()).or_not())
            .then_ignore(sym(SyntaxKind::LBRACE))
            .then(exp_parser())
            .then_ignore(sym(SyntaxKind::RBRACE))
            .map_with(|((((name, tvars), args), ret), body), e| {
                let mut d = Decl::func(name, tvars, Args(args), ret.unwrap_or(Typ::Unit), body);
                d.span = tok_span_to_byte_span(e.slice());
                d
            }),
        // type_decl = { "type" ~ id ~ "=" ~ typ ~ ";" }
        sym(SyntaxKind::KW_TYPE)
            .ignore_then(tid_tok())
            .then_ignore(sym(SyntaxKind::EQ))
            .then(typ_parser())
            .then_ignore(sym(SyntaxKind::SEMI))
            .map_with(|(name, typ), e| {
                let mut d = Decl::type_alias(Vid(name.0), typ);
                d.span = tok_span_to_byte_span(e.slice());
                d
            }),
    ))
}

/// Parse a module (list of declarations).
/// Mirrors `decls = { SOI ~ decl* ~ EOI }`
fn decls_parser<'src>(
) -> impl Parser<'src, &'src [Tok], Vec<UDecl>, extra::Err<Rich<'src, Tok>>> + Clone {
    decl_parser().repeated().collect()
}

// ── Entry point ────────────────────────────────────────────────────────

/// Parse source text into a list of declarations.
/// This is the chumsky equivalent of `UModule::from_str`.
pub fn parse_decls(src: &str) -> (Vec<UDecl>, Vec<ParseError>) {
    let tokens = lex(src);
    // Convert Token to Tok (include text + byte span), filtering out trivia
    let toks: Vec<Tok> = tokens
        .iter()
        .filter(|t| !t.kind.is_trivia())
        .map(|t| Tok {
            kind: t.kind,
            text: src[t.span.clone()].to_string(),
            span: t.span.clone(),
        })
        .collect();

    let result = decls_parser().parse(toks.as_slice());
    let (output, errs) = result.into_output_errors();
    let decls = output.unwrap_or_default();
    let errors: Vec<ParseError> = errs
        .iter()
        .map(|e| rich_to_parse_error(e, &toks, src))
        .collect();
    (decls, errors)
}

/// Convert a chumsky `Rich` error into a self-contained `ParseError`.
fn rich_to_parse_error(e: &Rich<Tok>, toks: &[Tok], src: &str) -> ParseError {
    // The error span is a token-index range. Map to byte span.
    let tok_span = e.span();
    let byte_span = if tok_span.start < toks.len() {
        toks[tok_span.start].span.clone()
    } else if !toks.is_empty() {
        // Past end — use the span of the last token's end
        let end = toks[toks.len() - 1].span.end;
        end..end
    } else {
        0..0
    };

    // Compute line/col from byte offset
    let byte_pos = byte_span.start;
    let (line, col, source_line) = line_col_at(src, byte_pos);

    // Found token
    let found = e.found().map(|t| (t.kind, t.text.clone()));

    // Expected tokens — collect from the Rich error's reason, filtering
    // out unhelpful patterns like "something else".
    let expected: Vec<String> = e
        .expected()
        .filter_map(|p| format_rich_pattern(p))
        .collect();

    ParseError {
        span: byte_span,
        line,
        col,
        source_line,
        found,
        expected,
        message: None,
    }
}

/// Format a `RichPattern` as a human-readable string.
/// Returns `None` for unhelpful patterns (like "something else") so they
/// can be filtered out.
fn format_rich_pattern(p: &chumsky::error::RichPattern<Tok>) -> Option<String> {
    use chumsky::error::RichPattern;
    match p {
        RichPattern::Token(t) => Some(fmt_kind(t.kind)),
        RichPattern::Label(s) => Some(fmt_label(s)),
        RichPattern::Identifier(s) => Some(fmt_label(&format!("identifier {}", s))),
        RichPattern::EndOfInput => Some("end of input".to_string()),
        // "something else" / "anything" are unhelpful — skip them
        RichPattern::Any | RichPattern::SomethingElse => None,
        _ => None,
    }
}

/// Format a `SyntaxKind` for error messages.
/// Punctuation/operators show as the literal in backticks (e.g. ``(``, ``->``);
/// keywords show as the word (e.g. `fn`, `let`);
/// `ID` shows as `identifier`; `POSITIVE` shows as `integer literal`.
fn fmt_kind(kind: SyntaxKind) -> String {
    fmt_label(kind.display())
}

/// Format a label string: wrap source tokens (keywords, punctuation) in
/// backticks; leave category descriptions (`identifier`, `integer literal`)
/// bare.
fn fmt_label(s: &str) -> String {
    if s.contains(' ') || s == "identifier" {
        s.to_string()
    } else {
        format!("`{}`", s)
    }
}

/// Compute (0-based line, 0-based byte column, source line text) for a byte offset.
pub fn line_col_at(src: &str, byte_pos: usize) -> (usize, usize, String) {
    let mut line = 0;
    let mut line_start = 0;
    for (i, ch) in src.char_indices() {
        if i >= byte_pos {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    let col = byte_pos - line_start;
    // Extract the source line (from line_start to next newline or end)
    let line_end = src[line_start..]
        .find('\n')
        .map(|p| line_start + p)
        .unwrap_or(src.len());
    let source_line = src[line_start..line_end].to_string();
    (line, col, source_line)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_fn() {
        let src = "fn f<F: Field>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_error_shows_line_col() {
        let src = "fn f<F: Field>(instance a: F) -> F {\n    a +\n}\n";
        let (_, errors) = parse_decls(src);
        assert!(!errors.is_empty());
        let e = &errors[0];
        // Error points to `}` on line 3 (0-based line 2) — the parser expected
        // an expression after `+` but found `}`.
        let displayed = format!("{}", e);
        eprintln!("--- error display ---\n{}", displayed);
        assert!(displayed.contains("line 3,"), "displayed: {}", displayed);
        assert!(displayed.contains("  | "), "displayed: {}", displayed);
        assert!(displayed.contains("^"), "displayed: {}", displayed);
        // `}` is shown as the literal char in backticks, not `RBRACE`
        assert!(displayed.contains("found: `}`"), "displayed: {}", displayed);
    }

    #[test]
    fn parse_error_missing_rparen() {
        let src = "fn f<F: Field>(instance a: F -> F { a }";
        let (_, errors) = parse_decls(src);
        assert!(!errors.is_empty());
        let e = &errors[0];
        let displayed = format!("{}", e);
        // Should show `->` as found, and `,` `)` as expected
        assert!(
            displayed.contains("found: `->`"),
            "displayed: {}",
            displayed
        );
        assert!(displayed.contains("expected:"), "displayed: {}", displayed);
        assert!(displayed.contains(")"), "displayed: {}", displayed);
        assert!(displayed.contains(","), "displayed: {}", displayed);
    }

    #[test]
    fn parse_error_duplicate_decl() {
        use crate::ast::module::UModule;
        let src =
            "fn f<F: Field>(instance a: F) -> F { a }\nfn f<F: Field>(instance a: F) -> F { a }";
        let err = UModule::from_str(src).unwrap_err();
        let displayed = format!("{}", err);
        // Error should point to the second declaration (line 2)
        assert!(displayed.contains("line 2"), "displayed: {}", displayed);
        assert!(displayed.contains("duplicate"), "displayed: {}", displayed);
        assert!(
            displayed.contains("first defined"),
            "displayed: {}",
            displayed
        );
    }

    #[test]
    fn parse_unary_minus_precedence() {
        // -a * a should parse as -(a * a), not (-a) * a
        // In chumsky pratt, prefix(0) consumes all operators with precedence > 0
        let src = "fn f<F: Field>(instance a: F) -> F { -a * a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        use crate::ast::{BinOp, Body, Exp};
        match &decls[0].body {
            Body::Func { body } => {
                // Should be Sub(Lit(0), Mul(a, a)) = -(a*a)
                // NOT Mul(Sub(Lit(0), a), a) = (-a)*a
                match body {
                    Exp::Bin(op, l, r) => {
                        assert_eq!(*op, BinOp::Sub, "outer should be Sub, got {:?}", op);
                        // right should be Mul(a, a)
                        match r.as_ref() {
                            Exp::Bin(op2, _, _) => {
                                assert_eq!(*op2, BinOp::Mul, "inner should be Mul");
                            }
                            other => panic!("expected Bin(Mul), got {:?}", other),
                        }
                    }
                    other => panic!("expected Bin(Sub), got {:?}", other),
                }
            }
            other => panic!("expected Func, got {:?}", other),
        }
    }

    #[test]
    fn parse_range_kind() {
        let src = "fn f<F: Field, V: 2..21>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_complex_range_kind() {
        let src = "fn f<G: Group, F: Scalar<G>, M: Size, N: 2..((M - 1) - (M - 1) / 2) + 1>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_spartan_tvars() {
        let src = "fn bullet_collect<G: Group, F: Scalar<G>, M: Size, N: 2..((M - 1) - (M - 1) / 2) + 1>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_eval_selector() {
        let src = "fn f<F: Field>(instance p: F) -> F { eval<0>(p) }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_ram_range() {
        let src = "fn f<F: Field>(instance x: [F; 4]) -> F { x[0..3] }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_ram_complex_range() {
        let src = "fn f<F: Field, M: Size>(instance x: [F; M]) -> F { x[((M - 1) - (M - 1) / 2)..(M - 1)] }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_ram_range_paren_start() {
        let src = "fn f<F: Field, M: Size>(instance x: [F; M]) -> F { x[(M - 1)..(M - 1)] }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_ram_range_simple_start() {
        let src = "fn f<F: Field, M: Size>(instance x: [F; M]) -> F { x[M..(M - 1)] }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_reduce_with_eval() {
        let src = r#"fn f<F: Field>(instance p: F) -> F {
            reduce(+, [eval<0>(p, t) for t in [0, 1]])
        }"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_record_return_type() {
        let src = "fn f<F: Field>(instance a: F) -> { x: F, y: F } { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_spartan_bullet_body() {
        let src = r#"fn bullet_collect<G: Group, F: Scalar<G>, M: Size, N: 2..((M - 1) - (M - 1) / 2) + 1>(
    instance g_base: G,
    instance h_base: G,
    witness g_folded: [G; 2^N],
    witness a_folded: [F; 2^N],
    witness x_folded: [F; 2^N],
    witness y_folded: F,
    witness r_Upsilon_folded: F
) -> { challenges: [F; N], challenges_inv: [F; N], Ls: [G; N], Rs: [G; N], final_x: F, final_y: F, final_r: F } {
    let x_1 = x_folded[0..2^(N-1)];
    let inner = bullet_collect(g_base, h_base, next_g, next_a, next_x, next_y, next_r);
    {|
        challenges: [c] ++ inner.challenges,
        final_x: inner.final_x
    |}
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_spartan_proto() {
        let src = r#"proto spartan<G: Group, F: Scalar<G>, M: Size>(
    instance mat_a_t:   Poly<F, 2*M, 1>,
    instance io:        [F; 2^(M - 1) - 1],
    witness az:       [F; 2^M]
) where
    az * bz == cz
{
    ()
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_proto_simple() {
        let src = r#"proto p<G: Group, F: Scalar<G>, M: Size>(
    instance a: Poly<F, 2*M, 1>
) where
    a == b
{
    ()
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_proto_minimal() {
        let src = "proto p<F: Field>(instance a: F) where a == b { () }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_proto_where_mul() {
        let src = "proto p<F: Field>(instance a: F, instance b: F, instance c: F) where a * b == c { () }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_proto_no_where() {
        let src = "proto p<F: Field>(instance a: F) where a { () }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_proto_where_eq() {
        let src = "proto p<F: Field>(instance a: F) where a == b { () }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_proto_let_body() {
        let src = "proto p<F: Field>(instance a: F) where a == b { let r = a; r }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_eq_weights() {
        let src = r#"fn eq_weights<G: Group, F: Scalar<G>>(instance x: [F; 1]) -> [F; 2] {
    [(1 - x[0]), x[0]]
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_with_comments() {
        let src = r#"// This is a comment
fn f<F: Field>(instance a: F) -> F { a }"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_range_kind_simple() {
        let src = "fn f<G: Group, F: Scalar<G>, M: Size, V: 3..M + 1>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_range_kind_long_name() {
        let src = "fn f<F: Field, NUM_VARS_CONST: Size, V: 3..NUM_VARS_CONST + 1, MAX_DEGREE_CONST: Size>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_sumcheck_round() {
        let src = r#"fn f<F: Field, NUM_VARS_CONST: Size, V: 3..NUM_VARS_CONST + 1, MAX_DEGREE_CONST: Size>(
    witness curr_poly: Poly<F, V, MAX_DEGREE_CONST>,
    instance points: [F; MAX_DEGREE_CONST + 1],
    instance challenges: [F; NUM_VARS_CONST - V + 1],
    instance prev_eval: F,
    instance ch: F,
    instance curr_round: Fin<NUM_VARS_CONST>
) -> Unit {
    let residual_poly = eval(curr_poly, [ch]);
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_nested_map_comprehension() {
        let src = r#"fn f<F: Field>(instance p: F) -> F {
    reduce(+, [
        eval<0>(p, t)
        for t in [
            [p[(i / 2) % 2] for j in 0..3]
            for i in 0..4
        ]
    ])
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_map_with_eval_selector() {
        let src = r#"fn f<F: Field>(instance p: F) -> F {
    [eval<0>(p, t) for t in [0, 1]]
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_reduce_with_map_eval() {
        let src = r#"fn f<F: Field>(instance p: F) -> F {
    reduce(+, [
        eval<0>(p, t)
        for t in [
            [p[(i / 2) % 2] for j in 0..3]
            for i in 0..4
        ]
    ])
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_two_eq_weights() {
        let src = r#"fn eq_weights<G: Group, F: Scalar<G>>(instance x: [F; 1]) -> [F; 2] {
    [(1 - x[0]), x[0]]
}
fn eq_weights<G: Group, F: Scalar<G>, EK: 2..21>(instance x: [F; EK]) -> [F; 2^EK] {
    let x_lo = x[0..(EK-1)];
    let a    = x[EK-1];
    let prev = eq_weights(x_lo);
    (prev * (1 - a)) ++ (prev * a)
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn parse_comments_and_two_eq_weights() {
        let src = r#"// Comment 1
// Comment 2

fn eq_weights<G: Group, F: Scalar<G>>(instance x: [F; 1]) -> [F; 2] {
    [(1 - x[0]), x[0]]
}
fn eq_weights<G: Group, F: Scalar<G>, EK: 2..21>(instance x: [F; EK]) -> [F; 2^EK] {
    let x_lo = x[0..(EK-1)];
    let a    = x[EK-1];
    let prev = eq_weights(x_lo);
    (prev * (1 - a)) ++ (prev * a)
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn parse_sc_recurse_d3_prefix() {
        let src = r#"fn sc_recurse_d3<G: Group, F: Scalar<G>, M: Size, V: 3..M + 1>(
    instance curr_poly:       Poly<F, V, 3>,
    instance points:          [F; 4],
    instance prev_challenges: [F; M - V + 1],
    instance prev_eval:       F,
    instance round_challenge: F,
    instance curr_round:      Fin<M>,
    instance g_evs_d3:        [G; 4],
    instance h_evs:           G
) -> { final_eval: F, challenges: [F; M] } {
    let residual_poly = eval(curr_poly, [round_challenge]);
    let round_poly = reduce(+, [
        eval<0>(residual_poly, tail)
        for tail in [
            [points[(i / (2^j)) % 2] for j in 0..(V - 2)]
            for i in 0..(2^(V - 2))
        ]
    ]);
    let evs_local = [round_poly(t) for t in points];
    evs <- evs_local;
    verify(prev_eval == evs[0] + evs[1]);
    let g = interpolate(points, evs);
    r_next <- challenge<F>;
    let next_prev = g(r_next);
    let new_challenges = prev_challenges ++ [r_next];

    let r_poly_sc = random<F>;
    comm_evs <- dot(g_evs_d3, evs) + h_evs * r_poly_sc;
    let r_eval_sc = random<F>;
    comm_eval_sc <- g_evs_d3[0] * next_prev + h_evs * r_eval_sc;
    let d_vec_sc = [random<F> for i in 0..4];
    let r_delta_sc = random<F>;
    let r_beta_sc = random<F>;
    delta_sc <- dot(g_evs_d3, d_vec_sc) + h_evs * r_delta_sc;
    let a_d_dot_sc = dot(d_vec_sc, evs);
    beta_sc <- g_evs_d3[0] * a_d_dot_sc + h_evs * r_beta_sc;
    c_sc <- challenge<F>;
    z_vec_sc <- [c_sc * evs[i] + d_vec_sc[i] for i in 0..4];
    z_delta_sc <- c_sc * r_poly_sc + r_delta_sc;
    z_beta_sc <- c_sc * r_eval_sc + r_beta_sc;
    verify(dot(g_evs_d3, z_vec_sc) + h_evs * z_delta_sc == comm_evs * c_sc + delta_sc);

    sc_recurse_d3(residual_poly, points, new_challenges, next_prev, r_next, curr_round + 1, g_evs_d3, h_evs)
}"#;
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn parse_schnorr() {
        let src = include_str!("../../examples/schnorr/schnorr.zippel");
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
    }

    /// Golden test: chumsky parser parses the example without errors.
    fn check_golden(path: &str) {
        let src = std::fs::read_to_string(path).unwrap();
        let (decls, errors) = parse_decls(&src);
        assert!(errors.is_empty(), "{}: parse errors: {:?}", path, errors);
        assert!(!decls.is_empty(), "{}: parsed zero declarations", path);
    }

    macro_rules! golden_test {
        ($name:ident, $path:literal) => {
            #[test]
            fn $name() {
                check_golden($path);
            }
        };
    }

    golden_test!(golden_bccgp, "../examples/bccgp/bccgp.zippel");
    golden_test!(golden_cds, "../examples/cds/cds.zippel");
    golden_test!(
        golden_coin_proof,
        "../examples/coin_proof/coin_proof.zippel"
    );
    golden_test!(
        golden_commitment_equality,
        "../examples/commitment_equality/commitment_equality.zippel"
    );
    golden_test!(golden_cp, "../examples/cp/cp.zippel");
    golden_test!(golden_dekart, "../examples/dekart/dekart.zippel");
    golden_test!(golden_dory, "../examples/dory/dory.zippel");
    golden_test!(golden_groth16, "../examples/groth16/groth16.zippel");
    golden_test!(golden_hadamard, "../examples/hadamard/hadamard.zippel");
    golden_test!(
        golden_hyperplonk,
        "../examples/hyperplonk/hyperplonk.zippel"
    );
    golden_test!(
        golden_hyperplonk_multiset,
        "../examples/hyperplonk_multiset/hyperplonk_multiset.zippel"
    );
    golden_test!(
        golden_hyperplonk_permutation,
        "../examples/hyperplonk_permutation/hyperplonk_permutation.zippel"
    );
    golden_test!(
        golden_hyperplonk_productcheck,
        "../examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel"
    );
    golden_test!(
        golden_hyperplonk_zerocheck,
        "../examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel"
    );
    golden_test!(golden_hyrax, "../examples/hyrax/hyrax.zippel");
    golden_test!(golden_hyrax_ipa, "../examples/hyrax_ipa/hyrax_ipa.zippel");
    golden_test!(
        golden_hyrax_podp,
        "../examples/hyrax_podp/hyrax_podp.zippel"
    );
    golden_test!(golden_hyrax_pop, "../examples/hyrax_pop/hyrax_pop.zippel");
    golden_test!(golden_ipa, "../examples/ipa/ipa.zippel");
    golden_test!(
        golden_ipa_weighted,
        "../examples/ipa_weighted/ipa_weighted.zippel"
    );
    golden_test!(golden_kzg, "../examples/kzg/kzg.zippel");
    golden_test!(golden_kzh, "../examples/kzh/kzh.zippel");
    golden_test!(
        golden_membership,
        "../examples/membership/membership.zippel"
    );
    golden_test!(
        golden_mle_sumcheck,
        "../examples/mle_sumcheck/mle_sumcheck.zippel"
    );
    golden_test!(
        golden_okamoto_elgamal,
        "../examples/okamoto_elgamal/okamoto_elgamal.zippel"
    );
    golden_test!(golden_okamoto, "../examples/okamoto/okamoto.zippel");
    golden_test!(golden_pari, "../examples/pari/pari.zippel");
    golden_test!(
        golden_pedersen_eq,
        "../examples/pedersen_eq/pedersen_eq.zippel"
    );
    golden_test!(golden_pst13, "../examples/pst13/pst13.zippel");
    golden_test!(
        golden_r1cs_sigma,
        "../examples/r1cs_sigma/r1cs_sigma.zippel"
    );
    golden_test!(
        golden_schnorr_3round,
        "../examples/schnorr_3round/schnorr_3round.zippel"
    );
    golden_test!(golden_schnorr, "../examples/schnorr/schnorr.zippel");
    golden_test!(golden_spartan, "../examples/spartan/spartan.zippel");
    golden_test!(
        golden_sumcheck_full,
        "../examples/sumcheck/sumcheck_full.zippel"
    );
    golden_test!(golden_sumcheck, "../examples/sumcheck/sumcheck.zippel");
    golden_test!(golden_zerocheck, "../examples/zerocheck/zerocheck.zippel");
    golden_test!(
        golden_zeromorph_kzg,
        "../examples/zeromorph_kzg/zeromorph_kzg.zippel"
    );
    golden_test!(golden_zk_kzg, "../examples/zk_kzg/zk_kzg.zippel");
}
