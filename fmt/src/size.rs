//! Size expression formatting.

use lang::ast::{Range, Size, Spanned};
use lang::parser::Token;
use share::DocAllocator;

use crate::ctx::{ALLOC, Doc, parenthesize};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::style::Style;
use crate::trivia::{TokenCursor, TriviaGap, gap_none, gap_space, trim_if_clean};

pub(crate) fn format_size(
    size: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    match size {
        Size::Var(id) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, ALLOC.text(id.to_string()))
        }
        Size::Lit(value) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_)));
            (gap, ALLOC.text(value.to_string()))
        }
        Size::Add(lhs, rhs) => format_size_binary(lhs, rhs, "+", cursor, end, style),
        Size::Sub(lhs, rhs) => format_size_binary(lhs, rhs, "-", cursor, end, style),
        Size::Mul(lhs, rhs) => format_size_binary(lhs, rhs, "*", cursor, end, style),
        Size::Div(lhs, rhs) => format_size_binary(lhs, rhs, "/", cursor, end, style),
        Size::Pow(lhs, rhs) => format_size_binary(lhs, rhs, "^", cursor, end, style),
        Size::Max(lhs, rhs) => format_size_call("max", lhs, rhs, cursor, end, style),
        Size::Min(lhs, rhs) => format_size_call("min", lhs, rhs, cursor, end, style),
    }
}

fn format_size_binary(
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    op: &'static str,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let (precedence, right_assoc) = match op {
        "+" | "-" => (1, false),
        "*" | "/" => (2, false),
        "^" => (3, true),
        _ => unreachable!(),
    };
    let (lhs_gap, lhs_doc) = format_size(&lhs.node, cursor, lhs.span.end, style);
    let lhs = parenthesize(
        lhs_doc,
        size_lhs_needs_paren(&lhs.node, precedence, right_assoc),
    );
    let op_gap = cursor.advance_to_token(end, |token| matches_size_op(op, token));
    let (rhs_gap, rhs_doc) = format_size(&rhs.node, cursor, rhs.span.end, style);
    let rhs = parenthesize(
        rhs_doc,
        size_rhs_needs_paren(&rhs.node, precedence, right_assoc),
    );

    let doc = ALLOC.concat([
        lhs,
        gap_space(trim_if_clean(op_gap), style),
        ALLOC.text(op),
        gap_space(trim_if_clean(rhs_gap), style),
        rhs,
    ]);
    (lhs_gap, doc)
}

fn format_size_call(
    name: &'static str,
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (lhs_gap, lhs_doc) = format_size(&lhs.node, cursor, lhs.span.end, style);
    let (comma_b, comma_a) =
        take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
    let (rhs_gap, rhs_doc) = format_size(&rhs.node, cursor, rhs.span.end, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let mut list = DelimList::new(style, ",", true);
    list.push_sep(lhs_gap, lhs_doc, comma_b, comma_a);
    list.push(rhs_gap, rhs_doc);
    let args = list.finish("(", ")", close_comments);

    (name_gap, ALLOC.concat([ALLOC.text(name), open, args]))
}

pub(crate) fn format_range(
    range: &Range<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let (start_gap, start_doc) = format_range_size(&range.start, cursor, end, style);
    if let Some(step) = &range.step {
        let comma = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Comma))),
            style,
        );
        let (step_gap, step_doc) = format_range_size(step, cursor, end, style);
        let dots = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::DotDot))),
            style,
        );
        let last = range.end.as_ref().expect("stepped ranges have an end");
        let (last_gap, last_doc) = format_range_size(last, cursor, end, style);
        let doc = ALLOC.concat([
            start_doc,
            comma,
            ALLOC.text(","),
            gap_space(trim_if_clean(step_gap), style),
            step_doc,
            dots,
            ALLOC.text(".."),
            gap_none(trim_if_clean(last_gap), style),
            last_doc,
        ]);
        (start_gap, doc)
    } else if let Some(last) = &range.end {
        let dots = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::DotDot))),
            style,
        );
        let (last_gap, last_doc) = format_range_size(last, cursor, end, style);
        let doc = ALLOC.concat([
            start_doc,
            dots,
            ALLOC.text(".."),
            gap_none(trim_if_clean(last_gap), style),
            last_doc,
        ]);
        (start_gap, doc)
    } else {
        (start_gap, start_doc)
    }
}

fn format_range_size(
    size: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    if size.span.start == size.span.end {
        format_size(&size.node, cursor, end, style)
    } else {
        format_size(&size.node, cursor, size.span.end, style)
    }
}

fn matches_size_op(op: &str, token: &Token) -> bool {
    match op {
        "+" => matches!(token, Token::Plus),
        "-" => matches!(token, Token::Minus),
        "*" => matches!(token, Token::Star),
        "/" => matches!(token, Token::Slash),
        "^" => matches!(token, Token::Caret),
        _ => false,
    }
}

fn size_lhs_needs_paren(size: &Size, precedence: usize, right_assoc: bool) -> bool {
    let child = size.precedence();
    child < precedence || (child == precedence && right_assoc)
}

fn size_rhs_needs_paren(size: &Size, precedence: usize, right_assoc: bool) -> bool {
    let child = size.precedence();
    child < precedence || (child == precedence && !right_assoc)
}
