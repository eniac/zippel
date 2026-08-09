//! Expression formatting.

use lang::ast::exp::{BinOp, Exp, Exps};
use lang::ast::{Size, Spanned};
use lang::id::Tid;
use lang::parser::Token;
use share::DocAllocator;

use crate::ctx::{ALLOC, Doc, parenthesize};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::paren::{lhs_needs_paren, rhs_needs_paren};
use crate::size::format_range;
use crate::style::Style;
use crate::trivia::{
    TokenCursor, TriviaGap, format_gap, gap_hard, gap_none, gap_space, trim_if_clean,
};

fn format_exp(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let end = exp.span.end;
    match &exp.node {
        Exp::Lit(value) => crate::size::format_size(value, cursor, end, style),
        Exp::Unit => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let list = DelimList::new(style, ",", true);
            (gap, list.finish("(", ")", close_comments))
        }
        Exp::Var(var) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, ALLOC.text(var.to_string()))
        }
        Exp::Neg(inner) => {
            let minus_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Minus));
            let (inner_gap, inner_doc) = format_exp(inner, cursor, style);
            let inner = parenthesize(inner_doc, neg_needs_paren(&inner.node));
            (
                minus_gap,
                ALLOC.concat([
                    ALLOC.text("-"),
                    gap_none(trim_if_clean(inner_gap), style),
                    inner.group(),
                ]),
            )
        }
        Exp::Bin(BinOp::Dot, lhs, rhs) => format_binary_call("dot", lhs, rhs, cursor, end, style),
        Exp::Bin(op, lhs, rhs) => {
            // Flatten left-associative same-operator chain:
            //   a * b * c  =  Bin(*, Bin(*, a, b), c)  →  [a, b, c]
            // so all operators align at the same indent instead of nesting
            // deeper for each left-recursion level.
            let mut inner_rhs_list: Vec<&Spanned<Exp<Size>>> = Vec::new();
            let mut current: &Spanned<Exp<Size>> = lhs;
            while let Exp::Bin(inner_op, inner_lhs, inner_rhs) = &current.node {
                if inner_op == op {
                    inner_rhs_list.push(inner_rhs);
                    current = inner_lhs;
                } else {
                    break;
                }
            }
            inner_rhs_list.reverse();
            let mut chain: Vec<&Spanned<Exp<Size>>> = Vec::new();
            chain.push(current);
            chain.extend(inner_rhs_list);
            chain.push(rhs);

            let indent = style.indent_width() as isize;
            let mut parts = Vec::with_capacity(chain.len() * 3);

            // First operand — no operator before it.
            let (first_gap, first_doc) = format_exp(chain[0], cursor, style);
            let first = parenthesize(first_doc, lhs_needs_paren(*op, &chain[0].node));
            parts.push(ALLOC.concat([gap_none(trim_if_clean(first_gap), style), first]));

            // Remaining operands — each preceded by `op`.
            for operand in &chain[1..] {
                let op_gap = cursor.advance_to_token(end, |token| matches_binop(*op, token));
                let (operand_gap, operand_doc) = format_exp(operand, cursor, style);
                let operand = parenthesize(operand_doc, rhs_needs_paren(*op, &operand.node));
                parts.push(gap_space(trim_if_clean(op_gap), style));
                parts.push(
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text(binop_symbol(*op))])
                        .flat_alt(ALLOC.text(binop_text(*op))),
                );
                parts.push(ALLOC.concat([gap_space(trim_if_clean(operand_gap), style), operand]));
            }

            (
                TriviaGap::default(),
                ALLOC.concat(parts).nest(indent).group(),
            )
        }
        Exp::App(function, args) => {
            let function_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
                style,
            );
            let mut list = DelimList::new(style, ",", true);
            format_exps_items(args, cursor, end, style, &mut list);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let args = list.finish("(", ")", close_comments);

            (
                function_gap,
                ALLOC.concat([ALLOC.text(function.to_string()), open, args]),
            )
        }
        Exp::Interpolate(None, evals) => format_unary_call(
            "interpolate",
            |token| matches!(token, Token::KwInterpolate),
            evals,
            cursor,
            end,
            style,
        ),
        Exp::Interpolate(Some(points), evals) => {
            format_binary_call("interpolate", points, evals, cursor, end, style)
        }
        Exp::Poly(value) => format_unary_call(
            "poly",
            |token| matches!(token, Token::KwPoly),
            value,
            cursor,
            end,
            style,
        ),
        Exp::Coef(value) => format_unary_call(
            "coef",
            |token| matches!(token, Token::KwCoef),
            value,
            cursor,
            end,
            style,
        ),
        Exp::Mle(value) => format_unary_call(
            "mle",
            |token| matches!(token, Token::KwMle),
            value,
            cursor,
            end,
            style,
        ),
        Exp::Evaluate(poly, range, point) => {
            format_evaluate(poly, range.as_ref(), point.as_deref(), cursor, end, style)
        }
        Exp::Vec(values) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let mut list = DelimList::new(style, ",", true);
            format_exps_items(values, cursor, end, style, &mut list);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            (open_gap, list.finish("[", "]", close_comments))
        }
        Exp::Range(range) => format_range(range, cursor, end, style),
        Exp::Map(body, var, range) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let (body_gap, body_doc) = format_exp(body, cursor, style);
            let for_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFor));
            let var_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let in_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwIn));
            let (range_gap, range_doc) = format_exp(range, cursor, style);
            let close = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::RBrack))),
                style,
            );

            (
                open_gap,
                ALLOC.concat([
                    ALLOC.text("["),
                    ALLOC
                        .concat([
                            ALLOC.line_(),
                            ALLOC
                                .concat([gap_none(trim_if_clean(body_gap), style), body_doc])
                                .group(),
                            gap_space(trim_if_clean(for_gap), style),
                            ALLOC.line().flat_alt(ALLOC.nil()),
                            ALLOC
                                .concat([
                                    ALLOC.text("for"),
                                    gap_space(trim_if_clean(var_gap), style),
                                    ALLOC.text(var.to_string()),
                                    gap_space(trim_if_clean(in_gap), style),
                                    ALLOC.text("in"),
                                    gap_space(trim_if_clean(range_gap), style),
                                    range_doc,
                                ])
                                .group(),
                            ALLOC.line_(),
                        ])
                        .nest(style.indent_width() as isize)
                        .group(),
                    close,
                    ALLOC.text("]"),
                ]),
            )
        }
        Exp::Reduce(op, value) => {
            let keyword_gap =
                cursor.advance_to_token(end, |token| matches!(token, Token::KwReduce));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
                style,
            );
            let op_gap = cursor.advance_to_token(end, |token| matches_binop(*op, token));
            let (comma_b, comma_a) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let mut list = DelimList::new(style, ",", true);
            list.push_sep(op_gap, ALLOC.text(binop_symbol(*op)), comma_b, comma_a);
            list.push(value_gap, value_doc);
            let args = list.finish("(", ")", close_comments);

            (
                keyword_gap,
                ALLOC.concat([ALLOC.text("reduce"), open, args]),
            )
        }
        Exp::Ram(base, index) => {
            let (base_gap, base_doc) = format_exp(base, cursor, style);
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LBrack))),
                style,
            );
            let (index_gap, index_doc) = format_exp(index, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            let mut list = DelimList::new(style, ",", false);
            list.push(index_gap, index_doc);
            (
                base_gap,
                ALLOC.concat([
                    base_doc.group(),
                    open,
                    list.finish("[", "]", close_comments),
                ]),
            )
        }
        Exp::Pair(lhs, rhs) => format_binary_call("pair", lhs, rhs, cursor, end, style),
        Exp::Random(typ, star) => {
            format_sampling("random", Token::KwRandom, typ, *star, cursor, end, style)
        }
        Exp::Challenge(typ, star) => format_sampling(
            "challenge",
            Token::KwChallenge,
            typ,
            *star,
            cursor,
            end,
            style,
        ),
        Exp::Let(_, _, _) | Exp::Log(_, _, _) => {
            let doc = format_body_exp_inner(exp, cursor, style);
            (TriviaGap::default(), doc)
        }
        Exp::Assert(lhs, rhs) => {
            format_assertion("assert", Token::KwAssert, lhs, rhs, cursor, end, style)
        }
        Exp::Verify(lhs, rhs) => {
            format_assertion("verify", Token::KwVerify, lhs, rhs, cursor, end, style)
        }
        Exp::Fun(vars, body) => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFun));
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let mut list = DelimList::new(style, ",", true);
            for (index, var) in vars.iter().enumerate() {
                let var_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let var_doc = ALLOC.text(var.to_string());
                if index + 1 < vars.len() {
                    let (before, after) = take_separator_gap_split(cursor, end, |token| {
                        matches!(token, Token::Comma)
                    });
                    list.push_sep(var_gap, var_doc, before, after);
                } else {
                    list.push(var_gap, var_doc);
                }
            }
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let arrow_gap = cursor.advance_to_token(end, |token| matches!(token, Token::FatArrow));
            let (body_gap, body_doc) = format_exp(body, cursor, style);

            (
                keyword_gap,
                ALLOC.concat([
                    ALLOC.text("fun"),
                    gap_space(trim_if_clean(open_gap), style),
                    list.finish("(", ")", close_comments),
                    gap_space(trim_if_clean(arrow_gap), style),
                    ALLOC.text("=>"),
                    gap_space(trim_if_clean(body_gap), style),
                    body_doc.group(),
                ]),
            )
        }
        Exp::Record(fields) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBraceBar));
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, value)| value.span.start);
            let mut list = DelimList::new(style, ",", true);
            crate::typ::format_field_items(
                &fields,
                |exp, cursor, _end, style| format_exp(exp, cursor, style),
                cursor,
                end,
                style,
                &mut list,
            );
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::BarRBrace));
            (open_gap, list.finish("{|", "|}", close_comments))
        }
        Exp::Proj(base, field) => {
            let (base_gap, base_doc) = format_exp(base, cursor, style);
            let dot = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Dot))),
                style,
            );
            let field_comments = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)))),
                style,
            );
            (
                base_gap,
                ALLOC.concat([
                    base_doc.group(),
                    dot,
                    ALLOC.text("."),
                    field_comments,
                    ALLOC.text(field.to_string()),
                ]),
            )
        }
        Exp::SetRecord(record, field, value) => {
            let (record_gap, record_doc) = format_exp(record, cursor, style);
            let dot = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Dot))),
                style,
            );
            let set = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)))),
                style,
            );
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
                style,
            );
            let field_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let (comma_b, comma_a) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let mut list = DelimList::new(style, ",", true);
            list.push_sep(field_gap, ALLOC.text(field.to_string()), comma_b, comma_a);
            list.push(value_gap, value_doc);

            (
                record_gap,
                ALLOC.concat([
                    record_doc.group(),
                    dot,
                    ALLOC.text("."),
                    set,
                    ALLOC.text("set"),
                    open,
                    list.finish("(", ")", close_comments),
                ]),
            )
        }
    }
}

fn format_unary_call(
    name: &'static str,
    pred: impl Fn(&Token) -> bool,
    arg: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, pred);
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (arg_gap, arg_doc) = format_exp(arg, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let mut list = DelimList::new(style, ",", true);
    list.push(arg_gap, arg_doc);

    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

fn format_binary_call(
    name: &'static str,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| {
        matches!(
            token,
            Token::Id(_) | Token::KwInterpolate | Token::KwPair | Token::KwDot
        )
    });
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (lhs_gap, lhs_doc) = format_exp(lhs, cursor, style);
    let (comma_comments_b, comma_comments_a) =
        take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
    let (rhs_gap, rhs_doc) = format_exp(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let mut list = DelimList::new(style, ",", true);
    list.push_sep(lhs_gap, lhs_doc, comma_comments_b, comma_comments_a);
    list.push(rhs_gap, rhs_doc);

    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

fn format_evaluate(
    poly: &Spanned<Exp<Size>>,
    range: Option<&lang::ast::Range<Size>>,
    point: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwEval));
    let selector = if let Some(range) = range {
        let open = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
            style,
        );
        let (range_gap, range_doc) = format_range(range, cursor, end, style);
        let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
        let mut list = DelimList::new(style, ",", true);
        list.push(range_gap, range_doc);
        ALLOC.concat([open, list.finish("<", ">", close_comments)])
    } else {
        ALLOC.nil()
    };

    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (poly_gap, poly_doc) = format_exp(poly, cursor, style);

    let mut list = DelimList::new(style, ",", true);
    if let Some(point) = point {
        let (comma_comments_b, comma_comments_a) =
            take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
        list.push_sep(poly_gap, poly_doc, comma_comments_b, comma_comments_a);
        let (point_gap, point_doc) = format_exp(point, cursor, style);
        list.push(point_gap, point_doc);
    } else {
        list.push(poly_gap, poly_doc);
    }
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));

    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text("eval"),
            selector,
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

#[allow(clippy::too_many_arguments)]
fn format_sampling(
    name: &'static str,
    keyword: Token<'static>,
    typ: &Tid,
    star: bool,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    });
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
        style,
    );
    let typ_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let star = if star {
        let comments = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Star))),
            style,
        );
        ALLOC.concat([comments, ALLOC.text("*")])
    } else {
        ALLOC.nil()
    };
    let content = ALLOC.concat([ALLOC.text(typ.to_string()), star]);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));

    let mut list = DelimList::new(style, ",", true);
    list.push(typ_gap, content);
    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("<", ">", close_comments),
        ]),
    )
}

#[allow(clippy::too_many_arguments)]
fn format_assertion(
    name: &'static str,
    keyword: Token<'static>,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    });
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (lhs_gap, lhs_doc) = format_exp(lhs, cursor, style);
    let eq_gap = cursor.advance_to_token(end, |token| matches!(token, Token::EqEq));
    let (rhs_gap, rhs_doc) = format_exp(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));

    let content = ALLOC
        .concat([
            lhs_doc,
            gap_space(trim_if_clean(eq_gap), style),
            ALLOC
                .concat([ALLOC.line(), ALLOC.text("==")])
                .flat_alt(ALLOC.text("==")),
            gap_space(trim_if_clean(rhs_gap), style),
            rhs_doc,
        ])
        .nest(style.indent_width() as isize)
        .group();

    let mut list = DelimList::new(style, ",", true);
    list.push(lhs_gap, content);
    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

fn format_exps_items(
    exps: &Exps<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
    list: &mut DelimList<'_>,
) {
    for (index, exp) in exps.0.iter().enumerate() {
        let (exp_gap, exp_doc) = format_exp(exp, cursor, style);
        if index + 1 < exps.0.len() {
            let (before, after) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            list.push_sep(exp_gap, exp_doc, before, after);
        } else {
            list.push(exp_gap, exp_doc);
        }
    }
}

pub(crate) fn format_relation(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    match &exp.node {
        Exp::Assert(lhs, rhs) => {
            let (lhs_gap, lhs_doc) = format_exp(lhs, cursor, style);
            let eq_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::EqEq));
            let (rhs_gap, rhs_doc) = format_exp(rhs, cursor, style);
            ALLOC
                .concat([
                    ALLOC.concat([gap_none(trim_if_clean(lhs_gap), style), lhs_doc]),
                    gap_space(trim_if_clean(eq_gap), style),
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text("==")])
                        .flat_alt(ALLOC.text("==")),
                    gap_space(trim_if_clean(rhs_gap), style),
                    rhs_doc,
                ])
                .nest(style.indent_width() as isize)
                .group()
        }
        Exp::Let(Some(var), value, body) => {
            let keyword = gap_none(
                trim_if_clean(
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
                ),
                style,
            );
            let name_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq_gap = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let body = if let Some(body) = body.as_ref() {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                let after_semi = cursor.advance_to(body.span.start);
                ALLOC.concat([
                    gap_before_semi(before_semi, style),
                    ALLOC.text(";"),
                    gap_hard(after_semi, style),
                    format_relation(body, cursor, style),
                ])
            } else {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                ALLOC.concat([gap_before_semi(before_semi, style), ALLOC.text(";")])
            };

            ALLOC.concat([
                keyword,
                ALLOC.text("let"),
                gap_space(trim_if_clean(name_gap), style),
                ALLOC.text(var.to_string()),
                gap_space(trim_if_clean(eq_gap), style),
                ALLOC.text("="),
                gap_space(trim_if_clean(value_gap), style),
                value_doc,
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let value = format_relation(value, cursor, style);
            let body = if let Some(body) = body.as_ref() {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                let after_semi = cursor.advance_to(body.span.start);
                ALLOC.concat([
                    gap_before_semi(before_semi, style),
                    ALLOC.text(";"),
                    gap_hard(after_semi, style),
                    format_relation(body, cursor, style),
                ])
            } else {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                ALLOC.concat([gap_before_semi(before_semi, style), ALLOC.text(";")])
            };

            ALLOC.concat([value, body])
        }
        _ => {
            let (gap, doc) = format_exp(exp, cursor, style);
            ALLOC.concat([gap_none(trim_if_clean(gap), style), doc])
        }
    }
}

pub(crate) fn format_body_exp(
    body: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let Some(body) = body else {
        // Empty body — comments between `{` and `}`. Empty gap → nil.
        let inner_comments = cursor
            .advance_to_token(end, |token| matches!(token, Token::RBrace))
            .trim();
        let needs_break = inner_comments.needs_line_break();
        let (open, end_sep) = if needs_break {
            (Some(ALLOC.hardline()), Some(ALLOC.hardline()))
        } else {
            (Some(ALLOC.text(" ")), Some(ALLOC.text(" ")))
        };
        return format_gap(inner_comments, open, end_sep, Some(ALLOC.nil()), style);
    };

    // Gap after `{` — strip blank lines. `sep = hardline` provides
    // the structural break for empty gaps; `open = hardline` puts
    // comments on their own line; `end = hardline` breaks after.
    let body_leading = format_gap(
        cursor.advance_to(body.span.start).trim_start(),
        Some(ALLOC.hardline()),
        Some(ALLOC.hardline()),
        Some(ALLOC.hardline()),
        style,
    );
    let body_doc = format_body_exp_inner(body, cursor, style);

    // Gap before `}` — strip blank lines (structural hardline precedes).
    let close_comments = cursor
        .advance_to_token(end, |token| matches!(token, Token::RBrace))
        .trim_end();

    ALLOC.concat([body_leading, body_doc, gap_hard(close_comments, style)])
}

fn format_body_exp_inner(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    match &exp.node {
        Exp::Let(Some(var), value, body) => {
            let keyword = gap_none(
                trim_if_clean(
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
                ),
                style,
            );
            let name_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq_gap = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                keyword,
                ALLOC.text("let"),
                gap_space(trim_if_clean(name_gap), style),
                ALLOC.text(var.to_string()),
                gap_space(trim_if_clean(eq_gap), style),
                ALLOC.text("="),
                gap_space(trim_if_clean(value_gap), style),
                value_doc,
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([gap_none(trim_if_clean(value_gap), style), value_doc, body])
        }
        Exp::Log(var, value, body) => {
            let name = gap_none(
                trim_if_clean(
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
                ),
                style,
            );
            let arrow_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::LArrow));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                name,
                ALLOC.text(var.to_string()),
                gap_space(trim_if_clean(arrow_gap), style),
                ALLOC.text("<-"),
                gap_space(trim_if_clean(value_gap), style),
                value_doc,
                body,
            ])
        }
        _ => {
            let (gap, doc) = format_exp(exp, cursor, style);
            ALLOC.concat([gap_none(trim_if_clean(gap), style), doc])
        }
    }
}

/// Render the gap before `;`. Inline comments get no trailing space
/// (`;` follows immediately); line comments get a hardline after
/// (`;` goes on the next line).
fn gap_before_semi(gap: TriviaGap, style: &Style) -> Doc<'static> {
    let needs_break = gap.needs_line_break();
    let end = if needs_break {
        Some(ALLOC.hardline())
    } else {
        Some(ALLOC.nil())
    };
    format_gap(trim_if_clean(gap), None, end, None, style)
}

fn format_body_tail(
    before_semi: TriviaGap,
    body: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let before = gap_before_semi(before_semi, style);
    let Some(body) = body else {
        return ALLOC.concat([before, ALLOC.text(";")]);
    };

    let after_semi = cursor.advance_to(body.span.start);
    ALLOC.concat([
        before,
        ALLOC.text(";"),
        gap_hard(after_semi, style),
        format_body_exp_inner(body, cursor, style),
    ])
}

fn matches_binop(op: BinOp, token: &Token) -> bool {
    match op {
        BinOp::Add => matches!(token, Token::Plus),
        BinOp::Sub => matches!(token, Token::Minus),
        BinOp::Mul => matches!(token, Token::Star),
        BinOp::Div => matches!(token, Token::Slash),
        BinOp::Pow => matches!(token, Token::Caret),
        BinOp::Dot => false,
        BinOp::Concat => matches!(token, Token::PlusPlus),
        BinOp::Rem => matches!(token, Token::Percent),
    }
}

fn binop_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Pow => "^",
        BinOp::Dot => unreachable!(),
        BinOp::Concat => "++",
        BinOp::Rem => "%",
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Pow => "^",
        BinOp::Dot => "dot",
        BinOp::Concat => "++",
        BinOp::Rem => "%",
    }
}

fn neg_needs_paren(exp: &Exp<Size>) -> bool {
    matches!(exp, Exp::Bin(op, _, _) if op.parser_precedence() <= 3)
}
