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
    pub at_line_start: bool,
    pub at_line_end: bool,
    pub start: usize,
    pub end: usize,
}

/// Lossless trivia between two semantic source anchors.
#[derive(Debug, Clone, Default)]
pub struct TriviaGap {
    comments: Vec<Comment>,
}

impl TriviaGap {
    pub fn join(mut self, other: Self) -> Self {
        self.comments.extend(other.comments);
        self
    }

    /// Whether the last comment in this gap forces a line break.
    ///
    /// Callers passing a soft separator (one that may not break, like `nil`,
    /// `line`, or `line_`) to `format_delimiter_gap` should upgrade to a
    /// `hardline` when this returns `true`.
    pub fn needs_line_break(&self) -> bool {
        self.comments.last().is_some_and(|c| c.forces_line_break())
    }
}

impl Comment {
    fn forces_line_break(&self) -> bool {
        !self.is_block || self.at_line_start || self.at_line_end
    }
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

struct SourceLayout {
    line_starts: Vec<usize>,
    blank_lines: Vec<bool>,
}

impl SourceLayout {
    fn new(src: &str, comment_spans: &[Range<usize>]) -> Self {
        let line_starts = compute_line_starts(src);
        let mut blank_lines = Vec::with_capacity(line_starts.len());
        for (line, &start) in line_starts.iter().enumerate() {
            let end = line_starts
                .get(line + 1)
                .copied()
                .unwrap_or(src.len())
                .min(src.len());
            let overlaps_comment = comment_spans
                .iter()
                .any(|span| span.start < end && span.end > start);
            blank_lines.push(!overlaps_comment && src[start..end].trim().is_empty());
        }
        Self {
            line_starts,
            blank_lines,
        }
    }

    fn line_of(&self, offset: usize) -> usize {
        line_of(offset, &self.line_starts)
    }

    fn blank_lines_between(&self, from: usize, to: usize) -> Vec<usize> {
        let from_line = self.line_of(from);
        let to_line = self.line_of(to);
        (from_line + 1..to_line)
            .filter(|&line| self.blank_lines[line])
            .map(|line| self.line_starts[line])
            .collect()
    }
}

pub struct TokenCursor<'a> {
    tokens: &'a TokenStream,
    comments: CommentCursor<'a>,
    pos: usize,
}

impl<'a> TokenCursor<'a> {
    pub fn new(tokens: &'a TokenStream, comments: &'a [Comment]) -> Self {
        Self {
            tokens,
            comments: CommentCursor::new(comments),
            pos: 0,
        }
    }

    pub fn advance_to(&mut self, target: usize) -> TriviaGap {
        debug_assert!(
            target >= self.pos,
            "advance_to cannot move backward: {} < {}",
            target,
            self.pos
        );
        let comments = self.comments.take_until(target);
        self.pos = target;
        TriviaGap { comments }
    }

    pub fn advance_to_token(&mut self, end: usize, pred: impl Fn(&Token) -> bool) -> TriviaGap {
        for (token, span) in &self.tokens.tokens {
            if span.start < self.pos || span.end > end || token.is_trivia() {
                continue;
            }
            if pred(token) {
                let comments = self.comments.take_until(span.start);
                self.pos = span.end;
                return TriviaGap { comments };
            }
        }
        TriviaGap::default()
    }

    /// Returns the end position of the next non-trivia token matching `pred`,
    /// without advancing the cursor. Returns None if not found within `end`.
    pub fn peek_token(&self, end: usize, pred: impl Fn(&Token) -> bool) -> Option<Range<usize>> {
        for (token, span) in &self.tokens.tokens {
            if span.start < self.pos || span.end > end || token.is_trivia() {
                continue;
            }
            if pred(token) {
                return Some(span.clone());
            }
        }
        None
    }

    pub fn position(&self) -> usize {
        self.pos
    }

    pub fn blank_lines_between(&self, from: usize, to: usize) -> Vec<usize> {
        self.tokens.layout.blank_lines_between(from, to)
    }
}

/// Render a gap before an ordinary grammar token.
pub fn format_leading_gap(gap: TriviaGap) -> Doc<'static> {
    let mut parts = Vec::new();
    let mut after_hardline = false;
    for comment in gap.comments {
        if comment.is_block && !comment.at_line_start {
            // Same-line block comment: space before (unless after hardline), no space after
            if !after_hardline {
                parts.push(ALLOC.text(" "));
            }
            parts.push(ALLOC.text(comment.text));
            after_hardline = false;
        } else {
            // Line comment or different-line block: no space before, hardline after
            parts.push(ALLOC.text(comment.text));
            parts.push(ALLOC.hardline());
            after_hardline = true;
        }
    }
    ALLOC.concat(parts)
}

/// Render a gap after punctuation and own the one separator that follows it.
///
/// The separator always carries the line break after the last comment — the
/// last comment does not emit its own hardline. Callers passing a soft
/// separator (`nil`, `line`, `line_`, `text`) should upgrade to `hardline`
/// when `gap.needs_line_break()` returns `true`.
pub fn format_delimiter_gap(gap: TriviaGap, separator: Doc<'static>) -> Doc<'static> {
    if gap.comments.is_empty() {
        return separator;
    }

    let last_idx = gap.comments.len() - 1;
    let mut parts = Vec::new();
    let mut after_hardline = false;
    for (index, comment) in gap.comments.into_iter().enumerate() {
        if index == 0 {
            if comment.at_line_start {
                parts.push(ALLOC.hardline());
            } else {
                parts.push(ALLOC.text(" "));
            }
        } else if comment.at_line_start {
            if !after_hardline {
                parts.push(ALLOC.hardline());
            }
        } else if !after_hardline {
            parts.push(ALLOC.text(" "));
        }

        let breaks = comment.forces_line_break();
        parts.push(ALLOC.text(comment.text));
        if breaks && index != last_idx {
            parts.push(ALLOC.hardline());
        }
        after_hardline = breaks;
    }
    parts.push(separator);
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
    layout: SourceLayout,
}

impl TokenStream {
    pub fn new(src: &str) -> Self {
        let tokens: Vec<_> = lang::parser::lex_iter(src)
            .map(|(token, span)| (token.into_owned(), span.start..span.end))
            .collect();
        let comment_spans = tokens
            .iter()
            .filter(|(token, _)| matches!(token, Token::LineComment | Token::BlockComment))
            .map(|(_, span)| span.clone())
            .collect::<Vec<_>>();
        Self {
            layout: SourceLayout::new(src, &comment_spans),
            tokens,
        }
    }
}

pub fn extract_comments(src: &str) -> Vec<Comment> {
    let line_starts = compute_line_starts(src);
    lang::parser::lex_iter(src)
        .filter(|(token, _)| matches!(token, Token::LineComment | Token::BlockComment))
        .map(|(token, span)| {
            let line_idx = line_of(span.start, &line_starts);
            let line_start = line_starts[line_idx];
            let at_line_start = src[line_start..span.start].trim().is_empty();
            let line_end = src[span.end..]
                .find('\n')
                .map(|offset| span.end + offset)
                .unwrap_or(src.len());
            let at_line_end = src[span.end..line_end].trim().is_empty();
            Comment {
                text: src[span.start..span.end].to_string(),
                is_block: matches!(token, Token::BlockComment),
                at_line_start,
                at_line_end,
                start: span.start,
                end: span.end,
            }
        })
        .collect()
}
