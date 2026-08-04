//! Comment cursor and token stream for the formatter.

use lang::parser::Token;
use share::{BoxAllocator, DocAllocator, DocBuilder};
use std::ops::Range;

const ALLOC: BoxAllocator = BoxAllocator;
type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

#[derive(Debug, Clone)]
pub struct Comment {
    pub text: String,
    pub is_block: bool,
    pub start: usize,
    pub end: usize,
}

pub struct CommentCursor<'a> {
    comments: &'a [Comment],
    printed: usize,
}

impl<'a> CommentCursor<'a> {
    fn new(comments: &'a [Comment]) -> Self {
        Self {
            comments,
            printed: 0,
        }
    }

    fn take_until(&mut self, pos: usize) -> Vec<Comment> {
        let mut result = Vec::new();
        while self.printed < self.comments.len() && self.comments[self.printed].end <= pos {
            result.push(self.comments[self.printed].clone());
            self.printed += 1;
        }
        result
    }
}

pub struct TokenCursor<'a> {
    tokens: &'a TokenStream,
    comments: CommentCursor<'a>,
    line_starts: &'a [usize],
    pos: usize,
}

impl<'a> TokenCursor<'a> {
    pub fn new(tokens: &'a TokenStream, comments: &'a [Comment], line_starts: &'a [usize]) -> Self {
        Self {
            tokens,
            comments: CommentCursor::new(comments),
            line_starts,
            pos: 0,
        }
    }

    pub fn advance_to(&mut self, target: usize) -> Doc<'static> {
        debug_assert!(
            target >= self.pos,
            "advance_to cannot move backward: {} < {}",
            target,
            self.pos
        );
        let comments = self.comments.take_until(target);
        self.pos = target;
        format_comments(comments, target, self.line_starts)
    }

    pub fn advance_to_token(&mut self, end: usize, pred: impl Fn(&Token) -> bool) -> Doc<'static> {
        for (token, span) in &self.tokens.tokens {
            if span.start < self.pos || span.end > end || token.is_trivia() {
                continue;
            }
            if pred(token) {
                let comments = self.comments.take_until(span.start);
                self.pos = span.end;
                return format_comments(comments, span.start, self.line_starts);
            }
        }
        ALLOC.nil()
    }
}

fn format_comments(comments: Vec<Comment>, target: usize, line_starts: &[usize]) -> Doc<'static> {
    let target_line = line_of(target, line_starts);
    let mut parts = Vec::new();
    for comment in comments {
        let comment_line = line_of(comment.end, line_starts);
        parts.push(ALLOC.text(comment.text));
        if comment_line < target_line || !comment.is_block {
            parts.push(ALLOC.hardline());
        } else {
            parts.push(ALLOC.text(" "));
        }
    }
    ALLOC.concat(parts)
}

fn line_of(offset: usize, line_starts: &[usize]) -> usize {
    match line_starts.binary_search(&offset) {
        Ok(index) => index,
        Err(index) => index.saturating_sub(1),
    }
}

pub fn compute_line_starts(src: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (index, byte) in src.bytes().enumerate() {
        if byte == b'\n' {
            starts.push(index + 1);
        }
    }
    starts
}

pub struct TokenStream {
    tokens: Vec<(Token<'static>, Range<usize>)>,
}

impl TokenStream {
    pub fn new(src: &str) -> Self {
        Self {
            tokens: lang::parser::lex_iter(src)
                .map(|(token, span)| (token.into_owned(), span.start..span.end))
                .collect(),
        }
    }
}

pub fn extract_comments(src: &str) -> Vec<Comment> {
    lang::parser::lex_iter(src)
        .filter(|(token, _)| matches!(token, Token::LineComment | Token::BlockComment))
        .map(|(token, span)| Comment {
            text: src[span.start..span.end].to_string(),
            is_block: matches!(token, Token::BlockComment),
            start: span.start,
            end: span.end,
        })
        .collect()
}
