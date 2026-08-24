//! Chumsky parser for Zippel — produces the AST from the logos token stream.
//!
//! - Every token has a span (from the logos lexer) — no silent tokens.
//! - The precedence table is in `chumsky::pratt`, queryable — no duplication.
//! - Error recovery is built-in via chumsky.

pub mod error;
mod label;
mod lexer;

pub use label::{Context, Terminal};
pub use lexer::{lex_iter, Token};

use std::borrow::Cow;

use chumsky::error::Rich;
use chumsky::input::{Stream, ValueInput};
use chumsky::pratt::{self, Associativity};
use chumsky::prelude::*;
use chumsky::span::SimpleSpan;

use crate::ast::arg::Args;
use crate::ast::decl::{Decl, UDecl};
use crate::ast::spanned::Spanned;
use crate::ast::Size;
use crate::ast::{BinOp, Exps, GArg, UExp};
use crate::diagnostic::Diagnostic;
use crate::id::{Tid, Vid};
use crate::typ::{Distribution, GTyp, Kind, Qualifier, Range, Typ, TypeVar, TypeVars};

use error::rich_to_diagnostic;

/// Native chumsky error type alias — no wrapper.
type RichError<'src> = Rich<'src, Token<'src>, SimpleSpan>;

// ── Token matching helpers ─────────────────────────────────────────────

/// Match an identifier, returning its name as a `Spanned<Vid>`.
fn id_tok<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Spanned<Vid>, extra::Err<RichError<'src>>> + Clone {
    select! { Token::Id(s) => s }
        .labelled(Terminal::Identifier)
        .map_with(|s, e| {
            let sp: SimpleSpan = e.span();
            Spanned::new(Vid(s.into_owned()), sp.into_range())
        })
}

/// Match an identifier, returning its name as a `Spanned<Tid>`.
fn tid_tok<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Spanned<Tid>, extra::Err<RichError<'src>>> + Clone {
    select! { Token::Id(s) => s }
        .labelled(Terminal::Identifier)
        .map_with(|s, e| {
            let sp: SimpleSpan = e.span();
            Spanned::new(Tid::from(s.into_owned()), sp.into_range())
        })
}

/// Match a positive integer literal, returning its value.
fn positive_tok<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, u32, extra::Err<RichError<'src>>> + Clone {
    select! { Token::Positive(s) => s }
        .labelled(Terminal::PositiveInteger)
        .map(|s| s.parse::<u32>().unwrap_or(0))
}

// ── Size parser (pratt) ────────────────────────────────────────────────

/// Parse a size-type expression using pratt parsing.
/// Mirrors `size_ty` in the pest grammar:
///   size_ty = { size_ty_term ~ (size_bin_op ~ size_ty_term)* }
///   size_ty_term = _{ "(" ~ size_ty ~ ")" | positive | size_var }
fn size_ty_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    recursive(|size_rec| {
        let atom = choice((
            just(Token::LParen)
                .ignored()
                .ignore_then(size_rec)
                .then_ignore(just(Token::RParen).ignored()),
            positive_tok().map_with(|n, e| {
                let sp: SimpleSpan = e.span();
                Spanned::new(Size::Lit(n), sp.into_range())
            }),
            tid_tok().map_with(|t, e| {
                let sp: SimpleSpan = e.span();
                Spanned::new(Size::Var(t.node), sp.into_range())
            }),
        ));

        atom.pratt((
            pratt::infix(
                Associativity::Left(1),
                just(Token::Plus).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(Size::Add(Box::new(a), Box::new(b)), sp.into_range())
                },
            ),
            pratt::infix(
                Associativity::Left(1),
                just(Token::Minus).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(Size::Sub(Box::new(a), Box::new(b)), sp.into_range())
                },
            ),
            pratt::infix(
                Associativity::Left(2),
                just(Token::Star).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(Size::Mul(Box::new(a), Box::new(b)), sp.into_range())
                },
            ),
            pratt::infix(
                Associativity::Left(2),
                just(Token::Slash).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(Size::Div(Box::new(a), Box::new(b)), sp.into_range())
                },
            ),
            pratt::infix(
                Associativity::Right(3),
                just(Token::Caret).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(Size::Pow(Box::new(a), Box::new(b)), sp.into_range())
                },
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
fn range_parser<'src, I>() -> impl Parser<'src, I, Range<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    choice((
        // step_r: start, step, "..", end
        size_ty_parser()
            .then_ignore(just(Token::Comma).ignored())
            .then(size_ty_parser())
            .then_ignore(just(Token::DotDot).ignored())
            .then(size_ty_parser().labelled(Context::RangeBound).as_context())
            .map(|((start, step), end)| Range {
                start,
                step: Some(step),
                end: Some(end),
            }),
        // unit_r: start, "..", end (step = 1)
        size_ty_parser()
            .then_ignore(just(Token::DotDot).ignored())
            .then(size_ty_parser().labelled(Context::RangeBound).as_context())
            .map(|(start, end)| Range {
                start: start.clone(),
                step: None,
                end: Some(end),
            }),
    ))
}

// ── Kind parser ────────────────────────────────────────────────────────

/// Parse a kind (type variable kind annotation).
/// Mirrors `kind_ty` in the pest grammar:
///   kind_ty = { field_ty | group_ty | range_ty | pairing_ty | scalar_ty | size_var_ty | size_ref_ty | positive }
fn kind_parser<'src, I>() -> impl Parser<'src, I, Kind<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    choice((
        kw_field(),
        kw_group(),
        kw_size(),
        pairing_kind(),
        scalar_kind(),
        range_parser().map(Kind::Range),
        // size_ref_ty: a bare size_ty → singleton range
        size_ty_parser().map_with(|s, e| {
            let sp: SimpleSpan = e.span();
            Kind::Range(Range {
                start: Spanned::new(s.node, sp.into_range()),
                step: None,
                end: None,
            })
        }),
        // positive: a bare positive literal → singleton range
        positive_tok().map_with(|n, e| {
            let sp: SimpleSpan = e.span();
            Kind::Range(Range {
                start: Spanned::new(Size::Lit(n), sp.into_range()),
                step: None,
                end: None,
            })
        }),
    ))
    .labelled(Context::Kind)
    .as_context()
}

fn kw_field<'src, I>() -> impl Parser<'src, I, Kind<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    just(Token::KwField).ignored().to(Kind::Field)
}
fn kw_group<'src, I>() -> impl Parser<'src, I, Kind<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    just(Token::KwGroup).ignored().to(Kind::Group)
}
fn kw_size<'src, I>() -> impl Parser<'src, I, Kind<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    just(Token::KwSize).ignored().to(Kind::SizeVar)
}

fn pairing_kind<'src, I>() -> impl Parser<'src, I, Kind<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    just(Token::KwPairing)
        .ignored()
        .ignore_then(just(Token::LAngle).ignored())
        .ignore_then(tid_tok())
        .then_ignore(just(Token::Comma).ignored())
        .then(tid_tok())
        .then_ignore(just(Token::Comma).ignored().or_not())
        .then_ignore(just(Token::RAngle).ignored())
        .map(|(a, b)| Kind::Pairing(a, b))
}

/// Scalar<ids> — takes a comma-separated list of group type variables.
fn scalar_kind<'src, I>() -> impl Parser<'src, I, Kind<Size>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    just(Token::KwScalar)
        .ignored()
        .ignore_then(just(Token::LAngle).ignored())
        .ignore_then(
            tid_tok()
                .separated_by(just(Token::Comma).ignored())
                .allow_trailing()
                .collect::<Vec<_>>(),
        )
        .then_ignore(just(Token::RAngle).ignored())
        .map(|ids: Vec<Spanned<Tid>>| Kind::Scalar(ids.into_iter().collect()))
}

// ── Type parser ────────────────────────────────────────────────────────

/// Parse a type.
/// Mirrors `typ` in the pest grammar:
///   typ = _{ poly_ty | uni_ty | mle_ty | vec_ty | fin_ty | unit_ty | base_ty | record_ty }
fn typ_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<GTyp<Size>>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    recursive(|typ_rec| {
        choice((
            // Poly<F, M, N>
            just(Token::KwPolyTy)
                .ignored()
                .ignore_then(just(Token::LAngle).ignored())
                .ignore_then(tid_tok())
                .then_ignore(just(Token::Comma).ignored())
                .then(size_ty_parser())
                .then_ignore(just(Token::Comma).ignored())
                .then(size_ty_parser())
                .then_ignore(just(Token::Comma).ignored().or_not())
                .then_ignore(just(Token::RAngle).ignored())
                .map_with(|((b, m), n), e| {
                    let sp: SimpleSpan = e.span();
                    Spanned::new(Typ::Poly(b.node, m, n), sp.into_range())
                }),
            // Uni<F, N>
            just(Token::KwUni)
                .ignored()
                .ignore_then(just(Token::LAngle).ignored())
                .ignore_then(tid_tok())
                .then_ignore(just(Token::Comma).ignored())
                .then(size_ty_parser())
                .then_ignore(just(Token::Comma).ignored().or_not())
                .then_ignore(just(Token::RAngle).ignored())
                .map_with(|(b, n), e| {
                    let sp: SimpleSpan = e.span();
                    Spanned::new(
                        Typ::Poly(b.node, Spanned::dummy(Size::Lit(1)), n),
                        sp.into_range(),
                    )
                }),
            // Mle<F, N>
            just(Token::KwMleTy)
                .ignored()
                .ignore_then(just(Token::LAngle).ignored())
                .ignore_then(tid_tok())
                .then_ignore(just(Token::Comma).ignored())
                .then(size_ty_parser())
                .then_ignore(just(Token::Comma).ignored().or_not())
                .then_ignore(just(Token::RAngle).ignored())
                .map_with(|(b, n), e| {
                    Spanned::new(Typ::Poly(b.node, n, Spanned::dummy(Size::Lit(1))), {
                        let sp: SimpleSpan = e.span();
                        sp.into_range()
                    })
                }),
            // Fin<range> or Fin<size_ty>
            // A bare size_ty N becomes Range { start: 0, step: 1, end: N }
            just(Token::KwFin)
                .ignored()
                .ignore_then(just(Token::LAngle).ignored())
                .ignore_then(choice((
                    range_parser().map_with(|r, e| {
                        Spanned::new(Typ::Fin(r), {
                            let sp: SimpleSpan = e.span();
                            sp.into_range()
                        })
                    }),
                    size_ty_parser().map_with(|s, e| {
                        Spanned::new(
                            Typ::Fin(Range {
                                start: Spanned::dummy(Size::Lit(0)),
                                step: None,
                                end: Some(s),
                            }),
                            {
                                let sp: SimpleSpan = e.span();
                                sp.into_range()
                            },
                        )
                    }),
                )))
                .then_ignore(just(Token::Comma).ignored().or_not())
                .then_ignore(just(Token::RAngle).ignored()),
            // Unit
            just(Token::KwUnit).ignored().map_with(|_, e| {
                Spanned::new(Typ::Unit, {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
            // Vec<T, N>  (vec_ty = { "[" ~ typ ~ ";" ~ size_ty ~ "]" })
            just(Token::LBrack)
                .ignored()
                .ignore_then(typ_rec.clone())
                .then_ignore(just(Token::Semi).ignored())
                .then(size_ty_parser())
                .then_ignore(just(Token::Semi).ignored().or_not())
                .then_ignore(just(Token::RBrack).ignored())
                .map_with(|(t, n), e| {
                    Spanned::new(Typ::Vec(Box::new(t), n), {
                        let sp: SimpleSpan = e.span();
                        sp.into_range()
                    })
                }),
            // Record { field: typ, ... }
            just(Token::LBrace)
                .ignored()
                .ignore_then(
                    tid_tok()
                        .then_ignore(just(Token::Colon).ignored())
                        .then(typ_rec.clone())
                        .separated_by(just(Token::Comma).ignored())
                        .allow_trailing()
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Token::RBrace).ignored())
                .map_with(|fields: Vec<(Spanned<Tid>, Spanned<GTyp<Size>>)>, e| {
                    let mut ctx = share::Ctx::new();
                    for (name, typ) in fields {
                        let field_name = Spanned::new(name.node.0.clone(), name.span.clone());
                        ctx.insert(&field_name, &typ);
                    }
                    Spanned::new(Typ::Record(ctx), {
                        let sp: SimpleSpan = e.span();
                        sp.into_range()
                    })
                }),
            // Base type variable
            tid_tok().map_with(|t, e| {
                Spanned::new(Typ::Base(t.node), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        ))
    })
    .labelled(Context::Type)
    .as_context()
}

// ── TypeVar parser ─────────────────────────────────────────────────────

/// Parse a type variable declaration.
/// Mirrors `tvar = { id ~ ":" ~ kind_ty }`
fn tvar_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<TypeVar<Size>>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    tid_tok()
        .then_ignore(just(Token::Colon).ignored())
        .then(kind_parser())
        .map_with(|(id, kind), e| {
            let sp: SimpleSpan = e.span();
            Spanned::new(TypeVar { id, kind }, sp.into_range())
        })
}

/// Parse a list of type variables.
/// Mirrors `tvars = { tvar ~ ("," ~ tvar)* }`
fn tvars_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<TypeVars<Size>>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    tvar_parser()
        .separated_by(just(Token::Comma).ignored())
        .allow_trailing()
        .collect::<Vec<_>>()
        .map_with(|v: Vec<_>, e| {
            let sp: SimpleSpan = e.span();
            Spanned::new(TypeVars(v), sp.into_range())
        })
        .labelled(Context::GenericParams)
        .as_context()
}

// ── Arg parser ─────────────────────────────────────────────────────────

/// Parse a qualifier.
/// Mirrors `qualifier = { instance | witness | extra }`
fn qualifier_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<Qualifier>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    choice((
        just(Token::KwInstance).ignored().to(Qualifier::Instance),
        just(Token::KwWitness).ignored().to(Qualifier::Witness),
        just(Token::KwExtra).ignored().to(Qualifier::Extra),
    ))
    .map_with(|q, e| {
        let sp: SimpleSpan = e.span();
        Spanned::new(q, sp.into_range())
    })
}

/// Parse a distribution.
/// Mirrors `distribution = { "uniform" ~ star? }`
fn distribution_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<Distribution>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    just(Token::KwUniform)
        .ignored()
        .then(just(Token::Star).ignored().or_not())
        .map_with(|(_, star), e| {
            let dist = if star.is_some() {
                Distribution::UniformNonZero
            } else {
                Distribution::Uniform
            };
            let sp: SimpleSpan = e.span();
            Spanned::new(dist, sp.into_range())
        })
}

/// Parse an argument.
/// Mirrors `arg = { qualifier? ~ distribution? ~ id ~ ":" ~ typ }`
fn arg_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<GArg<Size>>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    qualifier_parser()
        .or_not()
        .then(distribution_parser().or_not())
        .then(id_tok())
        .then_ignore(just(Token::Colon).ignored())
        .then(typ_parser())
        .map_with(|(((qual, dist), id), typ), e| {
            let sp: SimpleSpan = e.span();
            Spanned::new(
                GArg {
                    qualifier: qual.unwrap_or(Spanned::dummy(Qualifier::Local)),
                    distribution: dist.unwrap_or(Spanned::dummy(Distribution::Nonuniform)),
                    id,
                    typ,
                },
                sp.into_range(),
            )
        })
        .labelled(Context::Argument)
        .as_context()
}

// ── Binary operator parser ─────────────────────────────────────────────

/// Parse a binary operator token.
/// Mirrors `bin_op = _{ concat_op | add_op | sub_op | mul_op | div_op | pow_op | rem_op }`
fn bin_op_parser<'src, I>() -> impl Parser<'src, I, BinOp, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    choice((
        just(Token::PlusPlus).ignored().to(BinOp::Concat),
        just(Token::Plus).ignored().to(BinOp::Add),
        just(Token::Minus).ignored().to(BinOp::Sub),
        just(Token::Star).ignored().to(BinOp::Mul),
        just(Token::Slash).ignored().to(BinOp::Div),
        just(Token::Caret).ignored().to(BinOp::Pow),
        just(Token::Percent).ignored().to(BinOp::Rem),
        just(Token::AmpAmp).ignored().to(BinOp::And),
    ))
}

// ── Expression parser ──────────────────────────────────────────────────

/// Type alias for a boxed expression parser — needed to break the mutual
/// recursion cycle between exp_atom, exp_no_seq, and exp.
type ExpParser<'src, I> = Boxed<'src, 'src, I, Spanned<UExp>, extra::Err<RichError<'src>>>;

/// Parse an expression atom (the primary/operand for pratt parsing).
/// Takes boxed recursive references to break the mutual recursion cycle.
/// Mirrors `exp_term` in the pest grammar (lines 65-90).
fn exp_atom<'src, I>(
    exp_no_seq: ExpParser<'src, I>,
    exp: ExpParser<'src, I>,
) -> impl Parser<'src, I, Spanned<UExp>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    choice((
        // Range expression: 0..N or 0,1..N
        // Must come before parenthesized expression so (M-1)..(M-1) is parsed as a range, not (M-1)
        range_parser().map_with(|r, e| {
            let sp: SimpleSpan = e.span();
            Spanned::new(UExp::Range(r), sp.into_range())
        }),
        // Unit value: ()
        just(Token::LParen)
            .ignored()
            .then(just(Token::RParen).ignored())
            .map_with(|_, e| {
                let sp: SimpleSpan = e.span();
                Spanned::new(UExp::Unit, sp.into_range())
            }),
        // Parenthesized expression: ( exp )
        just(Token::LParen)
            .ignored()
            .ignore_then(exp.clone())
            .then_ignore(just(Token::RParen).ignored()),
        // fun(x, y) => exp
        just(Token::KwFun)
            .ignored()
            .ignore_then(just(Token::LParen).ignored())
            .ignore_then(
                id_tok()
                    .separated_by(just(Token::Comma).ignored())
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::RParen).ignored())
            .then_ignore(just(Token::FatArrow).ignored())
            .then(exp.clone())
            .map_with(|(vars, body), e| {
                Spanned::new(UExp::Fun(vars, Box::new(body)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // interpolate(exp) or interpolate(exp, exp)
        just(Token::KwInterpolate)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(exp_no_seq.clone())
                    .then(
                        just(Token::Comma)
                            .ignored()
                            .ignore_then(exp_no_seq.clone())
                            .or_not(),
                    )
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|(first, second), e| {
                let node = match second {
                    None => UExp::Interpolate(None, Box::new(first)),
                    Some(s) => UExp::Interpolate(Some(Box::new(first)), Box::new(s)),
                };
                Spanned::new(node, {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // poly(exp)
        just(Token::KwPoly)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|e, sp| Spanned::new(UExp::Poly(Box::new(e)), sp.span().into_range())),
        // coef(exp)
        just(Token::KwCoef)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|e, sp| Spanned::new(UExp::Coef(Box::new(e)), sp.span().into_range())),
        // mle(exp)
        just(Token::KwMle)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|e, sp| Spanned::new(UExp::Mle(Box::new(e)), sp.span().into_range())),
        // dot(exp, exp) — dot product → Bin(Dot, a, b)
        just(Token::KwDot)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored())
                    .then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|(a, b), e| {
                Spanned::new(UExp::Bin(BinOp::Dot, Box::new(a), Box::new(b)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // random<T> or random<T*>
        just(Token::KwRandom)
            .ignored()
            .ignore_then(just(Token::LAngle).ignored())
            .ignore_then(tid_tok())
            .then(just(Token::Star).ignored().or_not())
            .then_ignore(just(Token::RAngle).ignored())
            .map_with(|(t, star), e| {
                Spanned::new(UExp::Random(t, star.is_some()), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // challenge<T> or challenge<T*>
        just(Token::KwChallenge)
            .ignored()
            .ignore_then(just(Token::LAngle).ignored())
            .ignore_then(tid_tok())
            .then(just(Token::Star).ignored().or_not())
            .then_ignore(just(Token::RAngle).ignored())
            .map_with(|(t, star), e| {
                Spanned::new(UExp::Challenge(t, star.is_some()), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // [exp for x in exp] (map comprehension)
        just(Token::LBrack)
            .ignored()
            .ignore_then(exp.clone())
            .then_ignore(just(Token::KwFor).ignored())
            .then(id_tok())
            .then_ignore(just(Token::KwIn).ignored())
            .then(exp_no_seq.clone())
            .then_ignore(just(Token::RBrack).ignored())
            .map_with(|((body, var), iter), e| {
                Spanned::new(UExp::Map(Box::new(body), var, Box::new(iter)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // reduce(op, exp)
        just(Token::KwReduce)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(bin_op_parser())
                    .then_ignore(just(Token::Comma).ignored())
                    .then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|(op, e), sp| {
                Spanned::new(UExp::Reduce(op, Box::new(e)), sp.span().into_range())
            }),
        // [exp, exp, ...] (vector)
        just(Token::LBrack)
            .ignored()
            .ignore_then(
                exp_no_seq
                    .clone()
                    .separated_by(just(Token::Comma).ignored())
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::RBrack).ignored())
            .map_with(|v: Vec<_>, e| {
                Spanned::new(UExp::Vec(Exps(v)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // pair(exp, exp)
        just(Token::KwPair)
            .ignored()
            .ignore_then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored())
                    .then(exp_no_seq.clone())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|(a, b), e| {
                Spanned::new(UExp::Pair(Box::new(a), Box::new(b)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // assert(exp) — single bool expression
        just(Token::KwAssert)
            .ignored()
            .ignore_then(just(Token::LParen).ignored())
            .ignore_then(exp_no_seq.clone())
            .then_ignore(just(Token::Comma).or_not().ignored())
            .then_ignore(just(Token::RParen).ignored())
            .map_with(|exp, e| {
                Spanned::new(UExp::Assert(Box::new(exp)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // verify(exp) — single bool expression
        just(Token::KwVerify)
            .ignored()
            .ignore_then(just(Token::LParen).ignored())
            .ignore_then(exp_no_seq.clone())
            .then_ignore(just(Token::Comma).or_not().ignored())
            .then_ignore(just(Token::RParen).ignored())
            .map_with(|exp, e| {
                Spanned::new(UExp::Verify(Box::new(exp)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // eval<range>(exp) or eval<size>(exp) or eval(exp) or eval(exp, exp)
        eval_exp_parser(exp_no_seq.clone()),
        // Record construction: {| field: val, ... |}
        just(Token::LBraceBar)
            .ignored()
            .ignore_then(
                id_tok()
                    .then_ignore(just(Token::Colon).ignored())
                    .then(exp_no_seq.clone())
                    .separated_by(just(Token::Comma).ignored())
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::BarRBrace).ignored())
            .map_with(|fields: Vec<(Spanned<Vid>, Spanned<UExp>)>, e| {
                let mut ctx = share::Ctx::new();
                for (name, val) in fields {
                    let field_name = Spanned::new(name.node.0.clone(), name.span.clone());
                    ctx.insert(&field_name, &val);
                }
                Spanned::new(UExp::Record(ctx), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // Positive literal
        positive_tok().map_with(|n, e| {
            Spanned::new(UExp::Lit(Size::Lit(n)), {
                let sp: SimpleSpan = e.span();
                sp.into_range()
            })
        }),
        // app_exp: id(exps) — function application
        id_tok()
            .then(
                just(Token::LParen)
                    .ignored()
                    .ignore_then(
                        exp_no_seq
                            .clone()
                            .separated_by(just(Token::Comma).ignored())
                            .allow_trailing()
                            .collect::<Vec<_>>(),
                    )
                    .then_ignore(just(Token::RParen).ignored())
                    .labelled(Context::CallArgs)
                    .as_context(),
            )
            .map_with(|(id, args), e| {
                Spanned::new(UExp::App(id, Exps(args)), {
                    let sp: SimpleSpan = e.span();
                    sp.into_range()
                })
            }),
        // ram_exp: id[exp] — array access
        id_tok()
            .map_with(|id, e| {
                let sp: SimpleSpan = e.span();
                Spanned::new(UExp::Var(id), sp.into_range())
            })
            .then_ignore(just(Token::LBrack).ignored())
            .then(exp_no_seq.clone())
            .then_ignore(just(Token::RBrack).ignored())
            .map_with(|(id_var, idx), e| {
                let sp: SimpleSpan = e.span();
                Spanned::new(UExp::Ram(Box::new(id_var), Box::new(idx)), sp.into_range())
            }),
        // Bare identifier: uppercase → Size::Var, lowercase → Exp::Var
        id_tok().map_with(|id, e| {
            let node = if id.node.0.starts_with(|c: char| c.is_uppercase()) {
                UExp::Lit(Size::Var(Tid::from(id.node.0.as_str())))
            } else {
                UExp::Var(id)
            };
            Spanned::new(node, {
                let sp: SimpleSpan = e.span();
                sp.into_range()
            })
        }),
    ))
}

/// eval<range>(exp) or eval<size>(exp) or eval(exp) or eval(exp, exp)
/// Mirrors `eval_exp = { "eval" ~ eval_selector? ~ "(" ~ exp_no_seq ~ ("," ~ exp_no_seq)? ~ ")" }`
fn eval_exp_parser<'src, I>(
    exp_no_seq: ExpParser<'src, I>,
) -> impl Parser<'src, I, Spanned<UExp>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    // The selector normalizes both range and size_ty to Range<Size>.
    let selector = just(Token::LAngle)
        .ignored()
        .ignore_then(choice((
            range_parser(),
            size_ty_parser().map_with(|s, e| {
                let sp: SimpleSpan = e.span();
                Range {
                    start: Spanned::new(s.node, sp.into_range()),
                    step: None,
                    end: None,
                }
            }),
        )))
        .then_ignore(just(Token::RAngle).ignored())
        .or_not();

    just(Token::KwEval)
        .ignored()
        .ignore_then(selector)
        .then(
            just(Token::LParen)
                .ignored()
                .ignore_then(exp_no_seq.clone())
                .then(
                    just(Token::Comma)
                        .ignored()
                        .ignore_then(exp_no_seq)
                        .or_not(),
                )
                .then_ignore(just(Token::Comma).ignored().or_not())
                .then_ignore(just(Token::RParen).ignored())
                .labelled(Context::CallArgs)
                .as_context(),
        )
        .map_with(|(sel, (poly, second)), e| {
            let node = match (sel, second) {
                (None, None) => UExp::Evaluate(Box::new(poly), None, None),
                (None, Some(s)) => UExp::Evaluate(Box::new(poly), None, Some(Box::new(s))),
                (Some(r), Some(f)) => UExp::Evaluate(Box::new(poly), Some(r), Some(Box::new(f))),
                (Some(_), None) => UExp::Evaluate(Box::new(poly), None, None),
            };
            Spanned::new(node, {
                let sp: SimpleSpan = e.span();
                sp.into_range()
            })
        })
}

/// Parse an expression without `;` sequencing, using pratt parsing.
/// Mirrors `exp_no_seq = { exp_term ~ (record_set_op | proj_op | bin_op ~ exp_term)* }`
fn exp_no_seq_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<UExp>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    recursive(|exp_no_seq_rec| {
        // Build the exp parser using the recursive exp_no_seq reference
        let exp = exp_parser_inner(exp_no_seq_rec.clone().boxed()).boxed();
        let atom = exp_atom(exp_no_seq_rec.clone().boxed(), exp);

        atom.pratt((
            // Lowest precedence first (matches AEXP_PARSER order)
            // && (logical AND) — precedence 0, left-associative
            pratt::infix(
                Associativity::Left(0),
                just(Token::AmpAmp).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::And, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            // == (equality) — precedence 1, left-associative
            pratt::infix(
                Associativity::Left(1),
                just(Token::EqEq).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Equ, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Left(2),
                just(Token::Plus).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Add, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Left(2),
                just(Token::Minus).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Sub, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Left(3),
                just(Token::Star).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Mul, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Left(3),
                just(Token::Slash).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Div, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Left(3),
                just(Token::Percent).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Rem, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Left(4),
                just(Token::PlusPlus).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Concat, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            pratt::infix(
                Associativity::Right(5),
                just(Token::Caret).ignored().labelled(Terminal::Operator),
                |a, _, b, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(
                        UExp::Bin(BinOp::Pow, Box::new(a), Box::new(b)),
                        sp.into_range(),
                    )
                },
            ),
            // Prefix: unary minus → Exp::Neg(x)
            // Precedence 4 — tighter than `*`/`/`/`%` (3), looser than `^` (5).
            // So `-a * b` = `(-a) * b` and `-a ^ 2` = `-(a ^ 2)`.
            pratt::prefix(
                4,
                just(Token::Minus).ignored().labelled(Terminal::Operator),
                |_, rhs, sp| {
                    let sp: SimpleSpan = sp.span();
                    Spanned::new(UExp::Neg(Box::new(rhs)), sp.into_range())
                },
            ),
            // Postfix: record set r.set(field, val) — must come before projection
            // so that `.set(` is not consumed as projection `.set`.
            // record_set_op = { "." ~ "set" ~ "(" ~ id ~ "," ~ exp_no_seq ~ ")" }
            pratt::postfix(
                6,
                just(Token::Dot)
                    .ignored()
                    .labelled(Terminal::Operator)
                    .ignore_then(
                        select! { Token::Id(s) => s }
                            .labelled(Terminal::Set)
                            .filter(|s: &Cow<'_, str>| s == "set"),
                    )
                    .ignore_then(just(Token::LParen).ignored())
                    .ignore_then(id_tok())
                    .then_ignore(just(Token::Comma).ignored())
                    .then(exp_no_seq_rec.clone().boxed())
                    .then_ignore(just(Token::Comma).ignored().or_not())
                    .then_ignore(just(Token::RParen).ignored()),
                |lhs, (field, val): (Spanned<Vid>, Spanned<UExp>), sp| {
                    let sp: SimpleSpan = sp.span();
                    let field_name = Spanned::new(field.node.0.clone(), field.span.clone());
                    Spanned::new(
                        UExp::SetRecord(Box::new(lhs), field_name, Box::new(val)),
                        sp.into_range(),
                    )
                },
            ),
            // Postfix: projection r.field
            pratt::postfix(
                6,
                just(Token::Dot)
                    .ignored()
                    .labelled(Terminal::Operator)
                    .ignore_then(id_tok()),
                |lhs, field: Spanned<Vid>, sp| {
                    let sp: SimpleSpan = sp.span();
                    let field_name = Spanned::new(field.node.0.clone(), field.span.clone());
                    Spanned::new(UExp::Proj(Box::new(lhs), field_name), sp.into_range())
                },
            ),
        ))
    })
    .labelled(Context::Expression)
    .as_context()
}

/// Inner exp parser — takes the recursive exp_no_seq reference.
/// Mirrors `exp = { let_exp | log_exp | seq_exp | exp_no_seq }`
fn exp_parser_inner<'src, I>(
    exp_no_seq: ExpParser<'src, I>,
) -> impl Parser<'src, I, Spanned<UExp>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    recursive(|exp_rec| {
        choice((
            // let x = exp_no_seq; exp?
            just(Token::KwLet)
                .ignored()
                .ignore_then(id_tok())
                .then(
                    just(Token::Colon)
                        .ignored()
                        .ignore_then(typ_parser())
                        .or_not(),
                )
                .then_ignore(just(Token::Eq).ignored())
                .then(exp_no_seq.clone())
                .then_ignore(just(Token::Semi).ignored())
                .then(exp_rec.clone().or_not())
                .map_with(|(((var, _typ), val), body), e| {
                    let sp: SimpleSpan = e.span();
                    Spanned::new(
                        UExp::Let(Some(var), Box::new(val), body.map(Box::new)),
                        sp.into_range(),
                    )
                }),
            // id <- exp_no_seq; exp?  (transcript log)
            id_tok()
                .then_ignore(just(Token::LArrow).ignored())
                .then(exp_no_seq.clone())
                .then_ignore(just(Token::Semi).ignored())
                .then(exp_rec.clone().or_not())
                .map_with(|((id, val), body), e| {
                    let sp: SimpleSpan = e.span();
                    Spanned::new(
                        UExp::Log(id, Box::new(val), body.map(Box::new)),
                        sp.into_range(),
                    )
                }),
            // exp_no_seq; exp?  (sequencing)
            exp_no_seq
                .clone()
                .then_ignore(just(Token::Semi).ignored())
                .then(exp_rec.clone().or_not())
                .map_with(|(lhs, rhs), e| {
                    let sp: SimpleSpan = e.span();
                    Spanned::new(
                        UExp::Let(None, Box::new(lhs), rhs.map(Box::new)),
                        sp.into_range(),
                    )
                }),
            // exp_no_seq (no sequencing)
            exp_no_seq.clone(),
        ))
    })
}

/// Parse a top-level expression (allows `;` sequencing).
/// Public entry point — builds the full exp parser from exp_no_seq.
fn exp_parser<'src, I>() -> impl Parser<'src, I, Spanned<UExp>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    exp_parser_inner(exp_no_seq_parser().boxed())
}

// ── Declaration parser ─────────────────────────────────────────────────

/// Parse a comma-separated argument list inside `(...)`.
/// Labelled with `Context::ArgumentList` so error reporting can distinguish
/// errors inside the argument list from errors in generic params or body.
fn arg_list_parser<'src, I>(
) -> impl Parser<'src, I, Vec<Spanned<GArg<Size>>>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    arg_parser()
        .separated_by(just(Token::Comma).ignored())
        .allow_trailing()
        .collect::<Vec<_>>()
        .labelled(Context::ArgumentList)
        .as_context()
}

/// Parse a declaration.
/// Mirrors `decl = { proto_decl | func_decl | type_decl }`
fn decl_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<UDecl>, extra::Err<RichError<'src>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    choice((
        // proto_decl = { "proto" ~ id ~ "<" ~ tvars ~ ">" ~ "(" ~ args ~ ")" ~ "where" ~ where_exp ~ "{" ~ exp ~ "}" }
        just(Token::KwProto)
            .ignored()
            .ignore_then(id_tok())
            .then_ignore(just(Token::LAngle).ignored())
            .then(tvars_parser())
            .then_ignore(just(Token::RAngle).ignored())
            .then_ignore(just(Token::LParen).ignored())
            .then(arg_list_parser())
            .then_ignore(just(Token::RParen).ignored())
            .then_ignore(just(Token::KwWhere).ignored())
            .then(exp_parser())
            .then_ignore(just(Token::LBrace).ignored())
            .then(exp_parser().or_not())
            .then_ignore(just(Token::RBrace).ignored())
            .map_with(|((((name, tvars), args), relation), body), e| {
                let span: SimpleSpan = e.span();
                let range = span.into_range();
                Spanned::new(
                    Decl::proto(
                        name,
                        tvars,
                        Spanned::new(Args(args), range.clone()),
                        relation,
                        body,
                    ),
                    range,
                )
            }),
        // func_decl = { "fn" ~ id ~ "<" ~ tvars ~ ">" ~ "(" ~ args ~ ")" ~ ("->" ~ typ)? ~ "{" ~ exp ~ "}" }
        just(Token::KwFn)
            .ignored()
            .ignore_then(id_tok())
            .then_ignore(just(Token::LAngle).ignored())
            .then(tvars_parser())
            .then_ignore(just(Token::RAngle).ignored())
            .then_ignore(just(Token::LParen).ignored())
            .then(arg_list_parser())
            .then_ignore(just(Token::RParen).ignored())
            .then(
                just(Token::Arrow)
                    .ignored()
                    .ignore_then(typ_parser())
                    .or_not(),
            )
            .then_ignore(just(Token::LBrace).ignored())
            .then(exp_parser().or_not())
            .then_ignore(just(Token::RBrace).ignored())
            .map_with(|((((name, tvars), args), ret), body), e| {
                let span: SimpleSpan = e.span();
                let range = span.into_range();
                Spanned::new(
                    Decl::func(
                        name,
                        tvars,
                        Spanned::new(Args(args), range.clone()),
                        ret,
                        body,
                    ),
                    range,
                )
            }),
        // type_decl = { "type" ~ id ~ "=" ~ typ ~ ";" }
        just(Token::KwType)
            .ignored()
            .ignore_then(tid_tok())
            .then_ignore(just(Token::Eq).ignored())
            .then(typ_parser())
            .then_ignore(just(Token::Semi).ignored())
            .map_with(|(name, typ), e| {
                let span: SimpleSpan = e.span();
                let range = span.into_range();
                Spanned::new(
                    Decl::type_alias(
                        Spanned::new(Vid(name.node.0.clone()), name.span.clone()),
                        typ,
                    ),
                    range,
                )
            })
            .labelled(Context::TypeAlias)
            .as_context(),
    ))
    .labelled(Context::Declaration)
    .as_context()
}

// ── Entry point ────────────────────────────────────────────────────────

/// Check if a token is a declaration-starting keyword (`fn`, `proto`, `type`).
fn is_decl_start(tok: &Token<'_>) -> bool {
    matches!(tok, Token::KwFn | Token::KwProto | Token::KwType)
}

/// Parse source text into a list of declarations.
///
/// This is the chumsky equivalent of `UModule::parse` (parse phase only).
///
/// **Error recovery**: If parsing a declaration fails, the error is
/// recorded and one token is skipped before retrying. This allows collecting
/// multiple errors in a single pass. Malformed declarations are absent from
/// the output.
pub fn parse_decls(src: &str) -> (Vec<Spanned<UDecl>>, Vec<Diagnostic>) {
    let eoi = SimpleSpan::new((), src.len()..src.len());
    let stream = Stream::from_iter(lex_iter(src).filter(|(t, _)| !t.is_trivia()));
    let input = stream.map(eoi, |(t, s)| (t, s));

    // Parse declarations with recovery: try decl_parser, on failure emit the
    // error and skip all non-declaration tokens (returning None). This produces
    // one error per malformed declaration, not one per skipped token.
    // via_parser emits the original error before trying the fallback.
    use chumsky::recovery::via_parser;

    // Skip one token (the malformed decl's starting keyword), then skip all
    // non-declaration tokens until we reach the next declaration keyword.
    // This ensures we make progress even when the current token is a decl keyword.
    let skip_to_decl = any()
        .ignored()
        .then(
            any()
                .filter(|t: &Token<'_>| !is_decl_start(t))
                .ignored()
                .repeated(),
        )
        .to(None::<Spanned<UDecl>>);

    let recovery_parser = decl_parser()
        .map(Some)
        .recover_with(via_parser(skip_to_decl))
        .repeated()
        .collect::<Vec<Option<Spanned<UDecl>>>>();

    let result = recovery_parser.parse(input);
    let (output, errs) = result.into_output_errors();
    let errors: Vec<Diagnostic> = errs.iter().map(rich_to_diagnostic).collect();

    let decls: Vec<Spanned<UDecl>> = output.unwrap_or_default().into_iter().flatten().collect();

    (decls, errors)
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

    // ── Error recovery tests ────────────────────────────────────────────

    #[test]
    fn recovery_skips_malformed_decl() {
        // Two valid decls with a malformed one in between.
        // The malformed decl `fn f<: Field>(` has a broken generic param.
        let src = "fn f<F: Field>(instance a: F) -> F { a }\n\
                   fn f<: Field>(instance a: F) -> F { a }\n\
                   fn g<F: Field>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert_eq!(
            decls.len(),
            2,
            "expected 2 valid decls, got {}",
            decls.len()
        );
        assert_eq!(errors.len(), 1, "expected 1 error, got {}", errors.len());
    }

    #[test]
    fn recovery_multiple_errors() {
        // Two malformed decls with valid ones in between
        let src = "fn f<: Field>(instance a: F) -> F { a }\n\
                   fn g<F: Field>(instance a: F) -> F { a }\n\
                   fn h<: Field>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert_eq!(decls.len(), 1, "expected 1 valid decl, got {}", decls.len());
        assert_eq!(errors.len(), 2, "expected 2 errors, got {}", errors.len());
    }

    #[test]
    fn parse_unary_minus_precedence() {
        // -a * a should parse as (-a) * a, not -(a * a)
        // Unary minus has precedence 3 (tighter than * = 2, looser than ^ = 4)
        let src = "fn f<F: Field>(instance a: F) -> F { -a * a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        use crate::ast::{BinOp, Body, Exp};
        match &decls[0].node.body {
            Body::Func { body: Some(body) } => {
                // Should be Mul(Neg(a), a) = (-a)*a
                // NOT Neg(Mul(a, a)) = -(a*a)
                match &body.node {
                    Exp::Bin(op, lhs, _) => {
                        assert_eq!(*op, BinOp::Mul, "top should be Mul");
                        match &**lhs.as_ref() {
                            Exp::Neg(_) => {}
                            other => panic!("expected Neg on lhs, got {:?}", other),
                        }
                    }
                    other => panic!("expected Bin(Mul), got {:?}", other),
                }
            }
            other => panic!("expected Func with body, got {:?}", other),
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
    fn parse_empty_body() {
        let src = "fn f<F: Field>(instance a: F) -> F {}";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
        use crate::ast::Body;
        match &decls[0].node.body {
            Body::Func { body: None } => {}
            other => panic!("expected Func with no body, got {:?}", other),
        }
    }

    #[test]
    fn parse_empty_proto_body() {
        let src = "proto p<F: Field>(instance a: F) where a == a {}";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
        use crate::ast::Body;
        match &decls[0].node.body {
            Body::Proto { body: None, .. } => {}
            other => panic!("expected Proto with no body, got {:?}", other),
        }
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
        // With the new design, the where clause uses the same parser as
        // the body, so bare expressions are syntactically valid.
        // Type checking (not parsing) determines if the relation is valid.
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
        let src = include_str!("../../../examples/schnorr/schnorr.zippel");
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

    // ── Span correctness tests ──────────────────────────────────────────

    #[test]
    fn span_decl_covers_full_source() {
        let src = "fn f<F: Field>(instance a: F) -> F { a }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 1);
        let span = &decls[0].span;
        assert_eq!(span.start, 0, "decl span should start at 0");
        assert_eq!(span.end, src.len(), "decl span should cover full source");
    }

    #[test]
    fn span_multiple_decls_nonzero() {
        let src =
            "fn f<F: Field>(instance a: F) -> F { a }\nfn g<F: Field>(instance b: F) -> F { b }";
        let (decls, errors) = parse_decls(src);
        assert!(errors.is_empty(), "errors: {:?}", errors);
        assert_eq!(decls.len(), 2);
        for d in &decls {
            assert!(d.span.start < d.span.end, "span should be non-empty");
        }
        // First decl starts at 0, second starts after first
        assert_eq!(decls[0].span.start, 0);
        assert!(decls[1].span.start > decls[0].span.start);
    }
}
