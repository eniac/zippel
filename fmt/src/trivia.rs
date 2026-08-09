//! Comment cursor and token stream for the formatter.

use crate::ctx::hardlines;
use crate::style::Style;
use lang::parser::Token;
use share::{BoxAllocator, DocAllocator, DocBuilder};
use std::ops::Range;

const ALLOC: BoxAllocator = BoxAllocator;
type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CommentKind {
    /// `// comment`
    Line,
    /// `/* comment */` on a single source line.
    Block,
    /// `/* multi\nline */` spanning multiple source lines.
    MultilineBlock,
}

#[derive(Debug, Clone)]
pub(crate) struct Comment {
    pub(crate) text: String,
    pub(crate) kind: CommentKind,
    pub(crate) at_line_start: bool,
    pub(crate) at_line_end: bool,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

impl Comment {
    fn is_multiline_block(&self) -> bool {
        self.kind == CommentKind::MultilineBlock
    }
}

/// One element of trivia between two semantic source anchors.
#[derive(Debug, Clone)]
pub(crate) enum TriviaElement {
    /// One or more consecutive blank lines.
    BlankLines(usize),
    /// A single comment (line or block).
    Comment(Comment),
}

/// Lossless trivia between two semantic source anchors.
#[derive(Debug, Clone, Default)]
pub(crate) struct TriviaGap {
    layout: Vec<TriviaElement>,
}

impl TriviaGap {
    pub(crate) fn is_empty(&self) -> bool {
        self.layout.is_empty()
    }

    /// Whether the gap contains any comments (line or block).
    pub(crate) fn has_comments(&self) -> bool {
        self.layout
            .iter()
            .any(|e| matches!(e, TriviaElement::Comment(_)))
    }

    pub(crate) fn join(mut self, other: Self) -> Self {
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
    pub(crate) fn needs_line_break(&self) -> bool {
        match self.layout.last() {
            Some(TriviaElement::Comment(c)) => c.forces_line_break(),
            Some(TriviaElement::BlankLines(_)) => true,
            None => false,
        }
    }

    /// Whether the gap spans multiple source lines — i.e. the source
    /// had a structural line break between the two anchors. Used to
    /// distinguish inline gaps (Case 1) from multiline gaps (Case 2).
    pub(crate) fn has_source_line_break(&self) -> bool {
        self.layout.iter().any(|e| match e {
            TriviaElement::BlankLines(n) => *n >= 1,
            TriviaElement::Comment(c) => c.at_line_start || c.at_line_end || c.is_multiline_block(),
        })
    }

    /// The first element of the gap, or `None` if empty.
    pub(crate) fn first(&self) -> Option<&TriviaElement> {
        self.layout.first()
    }

    /// The last element of the gap, or `None` if empty.
    pub(crate) fn last(&self) -> Option<&TriviaElement> {
        self.layout.last()
    }

    /// Strip leading `BlankLines`, preserving inter-comment and trailing
    /// blank lines.
    ///
    /// Use this when a structural hardline precedes the gap (after `{`,
    /// after `where`, after `)`) — leading blank lines are noise, but
    /// blank lines between comments and after the last comment are
    /// meaningful.
    pub(crate) fn trim_start(mut self) -> Self {
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
    pub(crate) fn trim_end(mut self) -> Self {
        while matches!(self.layout.last(), Some(TriviaElement::BlankLines(_))) {
            self.layout.pop();
        }
        self
    }

    /// Strip both leading and trailing `BlankLines`.
    ///
    /// Use this when blank lines around a token are noise (e.g. around `=`
    /// in `let x = expr`) but comments should still be preserved.
    pub(crate) fn trim(self) -> Self {
        self.trim_start().trim_end()
    }
}

/// Trim blank lines from a gap when it has no comments.
///
/// Use this at call sites where blank lines are noise (intra-expression
/// gaps around `=`, `->`, `==`, etc.) but should be preserved when
/// comments are present.
pub(crate) fn trim_if_clean(gap: TriviaGap) -> TriviaGap {
    if !gap.has_comments() { gap.trim() } else { gap }
}

impl Comment {
    fn forces_line_break(&self) -> bool {
        match self.kind {
            CommentKind::Line => true,
            CommentKind::Block | CommentKind::MultilineBlock => {
                self.at_line_start || self.at_line_end
            }
        }
    }
}

struct CommentCursor<'a> {
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

pub(crate) struct TokenCursor<'a> {
    tokens: &'a TokenStream,
    comments: CommentCursor<'a>,
    pos: usize,
}

impl<'a> TokenCursor<'a> {
    pub(crate) fn new(tokens: &'a TokenStream, comments: &'a [Comment]) -> Self {
        Self {
            tokens,
            comments: CommentCursor::new(comments),
            pos: 0,
        }
    }

    pub(crate) fn advance_to(&mut self, target: usize) -> TriviaGap {
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

    pub(crate) fn advance_to_token(
        &mut self,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> TriviaGap {
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
    pub(crate) fn peek_token(
        &self,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> Option<Range<usize>> {
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
}

/// Render a gap's trivia layout with positioning control.
///
/// `open` controls what goes before the first comment. `None` = auto
/// (hardline for line-start comments, space for inline, nil for
/// BlankLines). `end` controls what goes after the last comment. `None` =
/// auto (hardline if the last comment forces a line break, nil otherwise,
/// nil if the last element is BlankLines). `sep` controls what goes when
/// the gap is empty (no comments, no blank lines). `None` = nil.
///
/// `open` is emitted only if the first element is a `Comment`. `end` is
/// emitted only if the last element is a `Comment`. If the first/last
/// element is `BlankLines`, the blank lines carry the positioning.
///
/// A comment suppresses its own ending hardline when the next element is
/// `BlankLines` — `BlankLines` owns the line break.
///
/// Prefer the `gap_none` / `gap_space` / `gap_hard` wrappers
/// for standard call sites. Use this directly only when you need custom
/// `open`/`end` positioning that the wrappers don't provide.
pub(crate) fn format_gap(
    gap: TriviaGap,
    open: Option<Doc<'static>>,
    end: Option<Doc<'static>>,
    sep: Option<Doc<'static>>,
    style: &Style,
) -> Doc<'static> {
    if gap.layout.is_empty() {
        return sep.unwrap_or_else(|| ALLOC.nil());
    }

    // Compute auto open if not explicitly provided. For at_line_start
    // comments, use `hardline` — the comment starts a new line. For
    // inline comments, use `space`.
    let open = open.or_else(|| match gap.first() {
        Some(TriviaElement::Comment(c)) if c.at_line_start => Some(ALLOC.hardline()),
        Some(TriviaElement::Comment(_)) => Some(ALLOC.text(" ")),
        _ => None,
    });

    // Compute auto end if not explicitly provided. Breaking comments
    // get an automatic hardline. Non-breaking comments get a space.
    // Non-comment gaps get nil unless the caller passes `end` explicitly.
    let end = end.or_else(|| match gap.last() {
        Some(TriviaElement::Comment(c)) if c.forces_line_break() => Some(ALLOC.hardline()),
        Some(TriviaElement::Comment(_)) => Some(ALLOC.text(" ")),
        _ => None,
    });

    let last_is_comment = matches!(gap.layout.last(), Some(TriviaElement::Comment(_)));
    let last_index = gap.layout.len() - 1;
    let mut parts = Vec::new();
    let mut after_hardline = false;
    let mut open = open;

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

    if last_is_comment && let Some(end) = end {
        parts.push(end);
    }
    ALLOC.concat(parts)
}

/// Empty gap → nil. Comments → auto open/end.
pub(crate) fn gap_none(gap: TriviaGap, style: &Style) -> Doc<'static> {
    format_gap(gap, None, None, None, style)
}

/// Empty gap → space. Comments → auto open, space after (non-breaking)
/// or hardline after (breaking).
pub(crate) fn gap_space(gap: TriviaGap, style: &Style) -> Doc<'static> {
    format_gap(gap, None, None, Some(ALLOC.text(" ")), style)
}

/// Empty gap → hardline. Comments → auto open (space for inline, nil
/// for at_line_start), hardline after. Use for structural breaks and
/// after punctuation (after `;`, between decls) where a line break is
/// always wanted after the gap but inline comments should stay inline.
pub(crate) fn gap_hard(gap: TriviaGap, style: &Style) -> Doc<'static> {
    format_gap(
        gap,
        None,
        Some(ALLOC.hardline()),
        Some(ALLOC.hardline()),
        style,
    )
}

/// Like `gap_none` but comments get `nil` open (no space/hardline before
/// the comment). Use inside `delimited_list` items where `line_()` or the
/// open delimiter already provides positioning — avoids double spaces
/// after `<`, `(`, `[`, `{`.
pub(crate) fn gap_list(gap: TriviaGap, style: &Style) -> Doc<'static> {
    let open = match gap.first() {
        Some(TriviaElement::Comment(_)) => Some(ALLOC.nil()),
        _ => None,
    };
    format_gap(gap, open, None, None, style)
}

fn line_of(offset: usize, line_starts: &[usize]) -> usize {
    match line_starts.binary_search(&offset) {
        Ok(index) => index,
        Err(index) => index.saturating_sub(1),
    }
}

fn compute_line_starts(src: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (index, byte) in src.bytes().enumerate() {
        if byte == b'\n' {
            starts.push(index + 1);
        }
    }
    starts
}

pub(crate) struct TokenStream {
    tokens: Vec<(Token<'static>, Range<usize>)>,
    layout: SourceLayout,
}

impl TokenStream {
    pub(crate) fn new(src: &str) -> Self {
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

pub(crate) fn extract_comments(src: &str) -> Vec<Comment> {
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
            let text = src[span.start..span.end].to_string();
            let kind = match token {
                Token::LineComment => CommentKind::Line,
                Token::BlockComment => {
                    // A block comment is multiline if it contains a
                    // newline between the opening /* and closing */.
                    let inner = &text[2..text.len().saturating_sub(2)];
                    if inner.contains('\n') {
                        CommentKind::MultilineBlock
                    } else {
                        CommentKind::Block
                    }
                }
                _ => CommentKind::Block,
            };
            Comment {
                text,
                kind,
                at_line_start,
                at_line_end,
                start: span.start,
                end: span.end,
            }
        })
        .collect()
}
