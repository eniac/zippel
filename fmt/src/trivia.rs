//! Comment cursor and token stream for the formatter.

use crate::style::Style;
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

/// One element of trivia between two semantic source anchors.
#[derive(Debug, Clone)]
pub enum TriviaElement {
    /// One or more consecutive blank lines.
    BlankLines(usize),
    /// A single comment (line or block).
    Comment(Comment),
}

/// Lossless trivia between two semantic source anchors.
#[derive(Debug, Clone, Default)]
pub struct TriviaGap {
    layout: Vec<TriviaElement>,
}

impl TriviaGap {
    pub fn is_empty(&self) -> bool {
        self.layout.is_empty()
    }

    pub fn join(mut self, other: Self) -> Self {
        if let (Some(TriviaElement::BlankLines(n)), Some(TriviaElement::BlankLines(m))) =
            (self.layout.last(), other.layout.first())
        {
            *self.layout.last_mut().unwrap() = TriviaElement::BlankLines(n + m);
            self.layout.extend(other.layout.into_iter().skip(1));
        } else {
            self.layout.extend(other.layout);
        }
        self
    }

    /// Whether the last element is a Comment that forces a line break,
    /// or a BlankLines (which always implies a break).
    pub fn needs_line_break(&self) -> bool {
        match self.layout.last() {
            Some(TriviaElement::Comment(c)) => c.forces_line_break(),
            Some(TriviaElement::BlankLines(_)) => true,
            None => false,
        }
    }

    /// The first element of the gap, or `None` if empty.
    pub fn first(&self) -> Option<&TriviaElement> {
        self.layout.first()
    }

    /// Strip leading `BlankLines`, preserving inter-comment and trailing
    /// blank lines.
    ///
    /// Use this when a structural hardline precedes the gap (after `{`,
    /// after `where`, after `)`) — leading blank lines are noise, but
    /// blank lines between comments and after the last comment are
    /// meaningful.
    pub fn trim_start(mut self) -> Self {
        while matches!(self.layout.first(), Some(TriviaElement::BlankLines(_))) {
            self.layout.remove(0);
        }
        self
    }

    /// Strip trailing `BlankLines`, preserving inter-comment and leading
    /// blank lines.
    ///
    /// Use this when a structural hardline follows the gap (before `}`) —
    /// trailing blank lines are noise, but blank lines between comments
    /// and before the first comment are meaningful.
    pub fn trim_end(mut self) -> Self {
        while matches!(self.layout.last(), Some(TriviaElement::BlankLines(_))) {
            self.layout.pop();
        }
        self
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

    /// Merge comments and blank lines between two offsets into an ordered
    /// layout, coalescing consecutive blank lines.
    fn layout_between(&self, comments: Vec<Comment>, from: usize, to: usize) -> Vec<TriviaElement> {
        let blank_offsets = self.blank_line_offsets(from, to);
        let mut layout = Vec::new();

        // Merge comments and blank-line offsets in source order.
        let mut ci = 0;
        let mut bi = 0;
        while ci < comments.len() || bi < blank_offsets.len() {
            let next_comment = comments.get(ci).map(|c| c.start);
            let next_blank = blank_offsets.get(bi).copied();
            match (next_comment, next_blank) {
                (Some(cs), Some(bs)) => {
                    if cs <= bs {
                        layout.push(TriviaElement::Comment(comments[ci].clone()));
                        ci += 1;
                    } else {
                        push_blank_lines(&mut layout, &mut bi, &blank_offsets, Some(cs));
                    }
                }
                (Some(_), None) => {
                    layout.push(TriviaElement::Comment(comments[ci].clone()));
                    ci += 1;
                }
                (None, Some(_)) => {
                    push_blank_lines(&mut layout, &mut bi, &blank_offsets, None);
                }
                (None, None) => break,
            }
        }
        layout
    }

    /// Start offsets of blank lines between `from` and `to`.
    fn blank_line_offsets(&self, from: usize, to: usize) -> Vec<usize> {
        let from_line = self.line_of(from);
        let to_line = self.line_of(to);
        (from_line + 1..to_line)
            .filter(|&line| self.blank_lines[line])
            .map(|line| self.line_starts[line])
            .collect()
    }
}

/// Coalesce consecutive blank-line offsets into a single BlankLines element.
/// Consumes all blank offsets from `*bi` up to (but not including) the offset
/// at `limit`, or all remaining if `limit` is None.
fn push_blank_lines(
    layout: &mut Vec<TriviaElement>,
    bi: &mut usize,
    offsets: &[usize],
    limit: Option<usize>,
) {
    let start = *bi;
    while *bi < offsets.len() && limit.is_none_or(|lim| offsets[*bi] < lim) {
        *bi += 1;
    }
    let count = *bi - start;
    if count > 0 {
        layout.push(TriviaElement::BlankLines(count));
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
        let layout = self
            .tokens
            .layout
            .layout_between(comments, self.pos, target);
        self.pos = target;
        TriviaGap { layout }
    }

    pub fn advance_to_token(&mut self, end: usize, pred: impl Fn(&Token) -> bool) -> TriviaGap {
        for (token, span) in &self.tokens.tokens {
            if span.start < self.pos || span.end > end || token.is_trivia() {
                continue;
            }
            if pred(token) {
                let comments = self.comments.take_until(span.start);
                let layout = self
                    .tokens
                    .layout
                    .layout_between(comments, self.pos, span.start);
                self.pos = span.end;
                return TriviaGap { layout };
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
}

/// Render a gap's layout.
///
/// `open` is emitted only if the first element is a `Comment` — it positions
/// the first comment relative to whatever came before. `end` is emitted only
/// if the last element is a `Comment` — it positions whatever comes after
/// relative to the last comment. If the first/last element is `BlankLines`,
/// the blank lines carry the positioning and `open`/`end` are skipped.
///
/// A comment suppresses its own ending hardline when the next element is
/// `BlankLines` — `BlankLines` owns the line break.
fn format_gap(
    gap: TriviaGap,
    open: Doc<'static>,
    end: Doc<'static>,
    style: &Style,
) -> Doc<'static> {
    if gap.layout.is_empty() {
        return end;
    }

    let last_is_comment = matches!(gap.layout.last(), Some(TriviaElement::Comment(_)));
    let last_index = gap.layout.len() - 1;
    let mut parts = Vec::new();
    let mut after_hardline = false;
    let mut open = Some(open);

    let mut iter = gap.layout.into_iter().peekable();
    let mut index = 0;
    while let Some(element) = iter.next() {
        match element {
            TriviaElement::Comment(comment) => {
                if index == 0 {
                    if let Some(open) = open.take() {
                        parts.push(open);
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

                let is_last = index == last_index;
                let next_is_blank = matches!(iter.peek(), Some(TriviaElement::BlankLines(_)));
                if breaks && !is_last && !next_is_blank {
                    parts.push(ALLOC.hardline());
                }
                after_hardline = breaks;
            }
            TriviaElement::BlankLines(n) => {
                let capped = n.min(style.max_blank_lines);
                parts.push(hardlines(1 + capped));
                after_hardline = true;
            }
        }
        index += 1;
    }

    if last_is_comment {
        parts.push(end);
    }
    ALLOC.concat(parts)
}

/// Render a gap before an ordinary grammar token.
pub fn format_leading_gap(gap: TriviaGap, style: &Style) -> Doc<'static> {
    let open = match gap.first() {
        Some(TriviaElement::Comment(c)) if c.is_block && !c.at_line_start => ALLOC.text(" "),
        _ => ALLOC.nil(),
    };
    let end = if gap.needs_line_break() {
        ALLOC.hardline()
    } else {
        ALLOC.nil()
    };
    format_gap(gap, open, end, style)
}

/// Render a gap after punctuation and own the one separator that follows it.
///
/// The separator is emitted only if the last element is a `Comment`. If the
/// last element is `BlankLines`, the blank lines carry the break and the
/// separator is skipped. Callers passing a soft separator (`nil`, `line`,
/// `line_`, `text`) should upgrade to `hardline` when `gap.needs_line_break()`
/// returns `true`.
pub fn format_delimiter_gap(
    gap: TriviaGap,
    separator: Doc<'static>,
    style: &Style,
) -> Doc<'static> {
    let open = match gap.first() {
        Some(TriviaElement::Comment(c)) if c.at_line_start => ALLOC.hardline(),
        _ => ALLOC.text(" "),
    };
    format_gap(gap, open, separator, style)
}

fn hardlines(count: usize) -> Doc<'static> {
    ALLOC.concat((0..count).map(|_| ALLOC.hardline()))
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
