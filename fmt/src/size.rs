//! Size expression formatting.

use lang::ast::{Range, Size, Spanned};
use lang::parser::Token;
use pretty::DocAllocator;

use crate::ctx::{Arena, Doc, parenthesize};
use crate::style::Style;
use crate::trivia::{TokenCursor, TriviaGap, gap_none, gap_space};

pub(crate) fn format_size<'doc>(
    alloc: &'doc Arena<'doc>,
    size: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'doc>) {
    match size {
        Size::Var(id) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, alloc.as_string(id))
        }
        Size::Lit(value) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_)));
            (gap, alloc.as_string(value))
        }
        Size::Add(lhs, rhs) => format_size_binary(alloc, lhs, rhs, size, cursor, end, style),
        Size::Sub(lhs, rhs) => format_size_binary(alloc, lhs, rhs, size, cursor, end, style),
        Size::Mul(lhs, rhs) => format_size_binary(alloc, lhs, rhs, size, cursor, end, style),
        Size::Div(lhs, rhs) => format_size_binary(alloc, lhs, rhs, size, cursor, end, style),
        Size::Pow(lhs, rhs) => format_size_binary(alloc, lhs, rhs, size, cursor, end, style),
    }
}

fn size_op_str(size: &Size) -> &'static str {
    match size {
        Size::Add(_, _) => "+",
        Size::Sub(_, _) => "-",
        Size::Mul(_, _) => "*",
        Size::Div(_, _) => "/",
        Size::Pow(_, _) => "^",
        _ => unreachable!(),
    }
}

fn format_size_binary<'doc>(
    alloc: &'doc Arena<'doc>,
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    parent: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'doc>) {
    let op = size_op_str(parent);
    let (lhs_gap, lhs_doc) = format_size(alloc, &lhs.node, cursor, lhs.span.end, style);
    let lhs = parenthesize(alloc, lhs_doc, parent.lhs_needs_paren(&lhs.node));
    let op_gap = cursor.advance_to_token(end, |token| matches_size_op(op, token));
    let (rhs_gap, rhs_doc) = format_size(alloc, &rhs.node, cursor, rhs.span.end, style);
    let rhs = parenthesize(alloc, rhs_doc, parent.rhs_needs_paren(&rhs.node));

    let doc = alloc.concat([
        lhs,
        gap_space(alloc, op_gap, style),
        alloc.text(op),
        gap_space(alloc, rhs_gap, style),
        rhs,
    ]);
    (lhs_gap, doc)
}

pub(crate) fn format_range<'doc>(
    alloc: &'doc Arena<'doc>,
    range: &Range<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'doc>) {
    let (start_gap, start_doc) = format_range_size(alloc, &range.start, cursor, end, style);
    if let Some(step) = &range.step {
        let comma = gap_none(
            alloc,
            cursor.advance_to_token(end, |token| matches!(token, Token::Comma)),
            style,
        );
        let (step_gap, step_doc) = format_range_size(alloc, step, cursor, end, style);
        let dots = gap_none(
            alloc,
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
            style,
        );
        let last = range.end.as_ref().expect("stepped ranges have an end");
        let (last_gap, last_doc) = format_range_size(alloc, last, cursor, end, style);
        let doc = alloc.concat([
            start_doc,
            comma,
            alloc.text(","),
            gap_space(alloc, step_gap, style),
            step_doc,
            dots,
            alloc.text(".."),
            gap_none(alloc, last_gap, style),
            last_doc,
        ]);
        (start_gap, doc)
    } else if let Some(last) = &range.end {
        let dots = gap_none(
            alloc,
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
            style,
        );
        let (last_gap, last_doc) = format_range_size(alloc, last, cursor, end, style);
        let doc = alloc.concat([
            start_doc,
            dots,
            alloc.text(".."),
            gap_none(alloc, last_gap, style),
            last_doc,
        ]);
        (start_gap, doc)
    } else {
        (start_gap, start_doc)
    }
}

fn format_range_size<'doc>(
    alloc: &'doc Arena<'doc>,
    size: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'doc>) {
    if size.span.start == size.span.end {
        format_size(alloc, &size.node, cursor, end, style)
    } else {
        format_size(alloc, &size.node, cursor, size.span.end, style)
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
