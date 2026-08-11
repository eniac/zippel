//! Size expression formatting.

use lang::ast::{Range, Size, Spanned};
use lang::parser::Token;
use share::DocAllocator;

use crate::ctx::{ALLOC, Doc, parenthesize};
use crate::style::Style;
use crate::trivia::{TokenCursor, TriviaGap, gap_none, gap_space};

pub(crate) fn format_size(
    size: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    match size {
        Size::Var(id) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, ALLOC.as_string(id))
        }
        Size::Lit(value) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_)));
            (gap, ALLOC.as_string(value))
        }
        Size::Add(lhs, rhs) => format_size_binary(lhs, rhs, size, cursor, end, style),
        Size::Sub(lhs, rhs) => format_size_binary(lhs, rhs, size, cursor, end, style),
        Size::Mul(lhs, rhs) => format_size_binary(lhs, rhs, size, cursor, end, style),
        Size::Div(lhs, rhs) => format_size_binary(lhs, rhs, size, cursor, end, style),
        Size::Pow(lhs, rhs) => format_size_binary(lhs, rhs, size, cursor, end, style),
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

fn format_size_binary(
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    parent: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let op = size_op_str(parent);
    let (lhs_gap, lhs_doc) = format_size(&lhs.node, cursor, lhs.span.end, style);
    let lhs = parenthesize(lhs_doc, size_lhs_needs_paren(parent, &lhs.node));
    let op_gap = cursor.advance_to_token(end, |token| matches_size_op(op, token));
    let (rhs_gap, rhs_doc) = format_size(&rhs.node, cursor, rhs.span.end, style);
    let rhs = parenthesize(rhs_doc, size_rhs_needs_paren(parent, &rhs.node));

    let doc = ALLOC.concat([
        lhs,
        gap_space(op_gap, style),
        ALLOC.text(op),
        gap_space(rhs_gap, style),
        rhs,
    ]);
    (lhs_gap, doc)
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
            cursor.advance_to_token(end, |token| matches!(token, Token::Comma)),
            style,
        );
        let (step_gap, step_doc) = format_range_size(step, cursor, end, style);
        let dots = gap_none(
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
            style,
        );
        let last = range.end.as_ref().expect("stepped ranges have an end");
        let (last_gap, last_doc) = format_range_size(last, cursor, end, style);
        let doc = ALLOC.concat([
            start_doc,
            comma,
            ALLOC.text(","),
            gap_space(step_gap, style),
            step_doc,
            dots,
            ALLOC.text(".."),
            gap_none(last_gap, style),
            last_doc,
        ]);
        (start_gap, doc)
    } else if let Some(last) = &range.end {
        let dots = gap_none(
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
            style,
        );
        let (last_gap, last_doc) = format_range_size(last, cursor, end, style);
        let doc = ALLOC.concat([
            start_doc,
            dots,
            ALLOC.text(".."),
            gap_none(last_gap, style),
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

fn size_lhs_needs_paren(parent: &Size, lhs: &Size) -> bool {
    let parent_prec = parent.precedence();
    let right_assoc = parent.is_right_assoc();
    let child = lhs.precedence();
    child < parent_prec || (child == parent_prec && right_assoc)
}

fn size_rhs_needs_paren(parent: &Size, rhs: &Size) -> bool {
    let parent_prec = parent.precedence();
    let right_assoc = parent.is_right_assoc();
    let child = rhs.precedence();
    child < parent_prec || (child == parent_prec && !right_assoc)
}
