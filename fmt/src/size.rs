//! Size expression formatting.

use lang::ast::{Range, Size, Spanned};
use lang::parser::Token;
use lang::stack_guard;
use pretty::DocAllocator;

use crate::ctx::{Doc, Formatter, parenthesize};
use crate::trivia::{TriviaGap, gap_none, gap_space};

impl<'doc> Formatter<'doc, '_> {
    #[stack_guard]
    pub(crate) fn format_size(&mut self, size: &Size, end: usize) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        match size {
            Size::Var(id) => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                (gap, alloc.as_string(id))
            }
            Size::Lit(value) => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Positive(_)));
                (gap, alloc.as_string(value))
            }
            Size::Add(lhs, rhs) => self.format_size_binary(lhs, rhs, size, end),
            Size::Sub(lhs, rhs) => self.format_size_binary(lhs, rhs, size, end),
            Size::Mul(lhs, rhs) => self.format_size_binary(lhs, rhs, size, end),
            Size::Div(lhs, rhs) => self.format_size_binary(lhs, rhs, size, end),
            Size::Pow(lhs, rhs) => self.format_size_binary(lhs, rhs, size, end),
        }
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

impl<'doc> Formatter<'doc, '_> {
    fn format_size_binary(
        &mut self,
        lhs: &Spanned<Size>,
        rhs: &Spanned<Size>,
        parent: &Size,
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let op = size_op_str(parent);
        let (lhs_gap, lhs_doc) = self.format_size(&lhs.node, lhs.span.end);
        let lhs = parenthesize(alloc, lhs_doc, parent.lhs_needs_paren(&lhs.node));
        let op_gap = self
            .cursor
            .advance_to_token(end, |token| matches_size_op(op, token));
        let (rhs_gap, rhs_doc) = self.format_size(&rhs.node, rhs.span.end);
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

    pub(crate) fn format_range(
        &mut self,
        range: &Range<Size>,
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let (start_gap, start_doc) = self.format_range_size(&range.start, end);
        if let Some(step) = &range.step {
            let comma = gap_none(
                alloc,
                self.cursor
                    .advance_to_token(end, |token| matches!(token, Token::Comma)),
                style,
            );
            let (step_gap, step_doc) = self.format_range_size(step, end);
            let dots = gap_none(
                alloc,
                self.cursor
                    .advance_to_token(end, |token| matches!(token, Token::DotDot)),
                style,
            );
            let last = range.end.as_ref().expect("stepped ranges have an end");
            let (last_gap, last_doc) = self.format_range_size(last, end);
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
                self.cursor
                    .advance_to_token(end, |token| matches!(token, Token::DotDot)),
                style,
            );
            let (last_gap, last_doc) = self.format_range_size(last, end);
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

    fn format_range_size(&mut self, size: &Spanned<Size>, end: usize) -> (TriviaGap, Doc<'doc>) {
        if size.span.start == size.span.end {
            self.format_size(&size.node, end)
        } else {
            self.format_size(&size.node, size.span.end)
        }
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
