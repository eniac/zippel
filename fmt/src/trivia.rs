//! Comment cursor and token stream for the formatter.
//!
//! # Idempotency
//!
//! Formatting is idempotent: `format(format(src)) == format(src)`. This
//! is not trivial because the formatter moves comments (dropping
//! redundant parens, applying sugar, merging gaps from skipped tokens),
//! which can change `at_line_start` / `at_line_end` — properties
//! computed from source positions that the formatter relies on.
//!
//! ## Why it works: self-stabilizing decisions
//!
//! Every layout decision in `format_gap` is one of:
//!
//! 1. **Inter-comment separator** (between elements A and B):
//!    `prev.needs_end_newline() || B.needs_start_newline()` → hardline,
//!    else space.
//! 2. **Auto `open`** (before first element, when caller passes
//!    `open=None`): `first.needs_start_newline()` → hardline, else
//!    space.
//! 3. **Auto `end`** (after last element, when caller passes
//!    `end=None`): `last.needs_end_newline()` → hardline, else space.
//!
//! Each decision produces output that *reinforces the conditions that
//! justified it*:
//!
//! - **Hardline emitted** → the preceding element ends a line
//!   (`at_line_end→true`), the following element starts a line
//!   (`at_line_start→true`). On re-parse, the same conditions hold →
//!   same decision.
//! - **Space emitted** → the preceding element is inline
//!   (`at_line_end→false`), the following element is inline
//!   (`at_line_start→false`). On re-parse, the same conditions hold →
//!   same decision.
//!
//! ## Explicit `open` / `end`
//!
//! When callers pass explicit `open`/`end` (e.g. `gap_hard` passes
//! `end=hardline`), the same value is used on both passes because the
//! code path and AST structure are the same after the first pass
//! (parens already dropped, sugar already applied). The comment's
//! `at_line_start`/`at_line_end` may change, but it doesn't matter —
//! the explicit value overrides the auto decision.
//!
//! ## External use of `needs_end_newline`
//!
//! Callers outside this module use `TriviaGap::needs_end_newline()` to
//! choose between a hardline and a softer separator (`nil`, `space`,
//! `line_`, `line`). The hardline case is self-stabilizing (hardline →
//! comment at line end → `needs_end_newline` true → hardline). The
//! softer case is self-stabilizing when no break is emitted (comment
//! stays inline → `at_line_end` false → `needs_end_newline` false →
//! same choice). Callers using `line_()` / `line()` (conditional
//! breaks) should verify idempotency for their specific case.

use crate::ctx::hardlines;
use crate::style::Style;
use lang::parser::Token;
use pretty::{BoxAllocator, DocAllocator, DocBuilder};
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
    text: String,
    kind: CommentKind,
    at_line_start: bool,
    at_line_end: bool,
    start: usize,
    end: usize,
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

impl TriviaElement {
    /// Whether this element needs to begin on a new line.
    ///
    /// Used to decide the separator *before* this element.
    pub(crate) fn needs_start_newline(&self) -> bool {
        match self {
            TriviaElement::BlankLines(_) => true,
            TriviaElement::Comment(c) => c.at_line_start,
        }
    }

    /// Whether a newline must follow this element.
    ///
    /// Used to decide the separator *after* this element (i.e. before
    /// the next element, or the `end` doc). Uses `at_line_end` (stable
    /// across formats), never `at_line_start` (unstable).
    fn needs_end_newline(&self) -> bool {
        match self {
            TriviaElement::BlankLines(_) => false,
            TriviaElement::Comment(c) => match c.kind {
                CommentKind::Line => true,
                CommentKind::Block | CommentKind::MultilineBlock => c.at_line_end,
            },
        }
    }
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

    /// Whether the last element needs a newline after it.
    ///
    /// Callers can use this to make layout decisions (e.g. whether to
    /// break a delimited list). See the module-level documentation for
    /// idempotency requirements — callers must ensure their decisions
    /// are self-stabilizing.
    pub fn needs_end_newline(&self) -> bool {
        match self.layout.last() {
            Some(e) => e.needs_end_newline(),
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
        let first_non_blank = self
            .layout
            .iter()
            .position(|e| !matches!(e, TriviaElement::BlankLines(_)));
        match first_non_blank {
            Some(0) => {}
            Some(idx) => {
                self.layout.drain(0..idx);
            }
            None => self.layout.clear(),
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

    /// Trim blank lines when the gap has no comments.
    ///
    /// Used internally by `advance_to_token`. Also used by
    /// `take_separator_gap_split` for the after-separator gap (sourced
    /// from `advance_to` because it must not consume the next token).
    /// Callers of `advance_to` trim explicitly via `.trim_start()` /
    /// `.trim_end()` / `.trim()` or `.trim_if_clean()`.
    pub(crate) fn trim_if_clean(self) -> Self {
        if !self.has_comments() {
            self.trim()
        } else {
            self
        }
    }
}

struct CommentCursor {
    comments: Vec<Comment>,
    /// Index of the first unconsumed comment. Comments before this
    /// index have been returned by `take_until`. Using an index
    /// instead of `drain` avoids O(N) shifting of remaining elements.
    printed: usize,
}

impl CommentCursor {
    fn new(comments: Vec<Comment>) -> Self {
        Self {
            comments,
            printed: 0,
        }
    }

    fn take_until(&mut self, pos: usize) -> Vec<Comment> {
        let start = self.printed;
        while self.printed < self.comments.len() && self.comments[self.printed].end <= pos {
            self.printed += 1;
        }
        self.comments[start..self.printed].to_vec()
    }
}

struct SourceLayout {
    line_starts: Vec<usize>,
    blank_lines: Vec<bool>,
}

impl SourceLayout {
    fn new(src: &str, line_starts: &[usize], comment_spans: &[Range<usize>]) -> Self {
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
            line_starts: line_starts.to_vec(),
            blank_lines,
        }
    }

    fn line_of(&self, offset: usize) -> usize {
        line_of(offset, &self.line_starts)
    }

    /// Merge comments and blank lines between two offsets into an ordered
    /// layout, coalescing consecutive blank lines.
    fn layout_between(&self, comments: Vec<Comment>, from: usize, to: usize) -> Vec<TriviaElement> {
        // Fast path: no comments → only blank lines matter. Skip the
        // merge entirely and just count blank lines in the range.
        if comments.is_empty() {
            let from_line = self.line_of(from);
            let to_line = self.line_of(to);
            let count = (from_line + 1..to_line)
                .filter(|&line| self.blank_lines[line])
                .count();
            if count == 0 {
                return Vec::new();
            }
            return vec![TriviaElement::BlankLines(count)];
        }

        let from_line = self.line_of(from);
        let to_line = self.line_of(to);
        let blank_offsets: Vec<usize> = (from_line + 1..to_line)
            .filter(|&line| self.blank_lines[line])
            .map(|line| self.line_starts[line])
            .collect();

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

pub(crate) struct TokenCursor {
    tokens: TokenStream,
    comments: CommentCursor,
    pos: usize,
    /// Index into `tokens.tokens` — all tokens before this index have
    /// been consumed or skipped. Avoids rescanning from 0 on every
    /// `advance_to_token` / `peek_token` call.
    token_idx: usize,
}

impl TokenCursor {
    /// Build a cursor from source text: lexes, extracts comments, and
    /// computes source layout in a single pass.
    pub(crate) fn new(src: &str) -> Self {
        let line_starts = compute_line_starts(src);

        let mut tokens = Vec::new();
        let mut comment_spans = Vec::new();
        let mut comments = Vec::new();

        for (token, span) in lang::parser::lex_iter(src) {
            let span = span.start..span.end;
            if matches!(token, Token::LineComment | Token::BlockComment) {
                comment_spans.push(span.clone());
                comments.push(build_comment(&token, &span, src, &line_starts));
            }
            tokens.push((token.into_owned(), span));
        }

        let layout = SourceLayout::new(src, &line_starts, &comment_spans);
        Self {
            tokens: TokenStream { layout, tokens },
            comments: CommentCursor::new(comments),
            pos: 0,
            token_idx: 0,
        }
    }

    /// Advance the cursor to a byte position, returning the gap
    /// (comments and blank lines) between the current position and
    /// `target`.
    ///
    /// **Does not consume a token** — the cursor lands at `target`,
    /// which is typically the *start* of the next AST node's span.
    /// The caller is responsible for consuming tokens within that node
    /// (usually via `advance_to_token`).
    ///
    /// **Does not trim** — the returned gap is raw. Use this for
    /// inter-node gaps (between decls, after `;` in statement
    /// sequences, trailing file gap) where blank lines may be
    /// meaningful. Trim explicitly with `.trim_start()`,
    /// `.trim_end()`, `.trim()`, or `.trim_if_clean()` when blank
    /// lines are noise in that position.
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

    /// Advance the cursor to the next token matching `pred`, consuming
    /// it and returning the gap (comments and blank lines) between the
    /// current position and the token's start.
    ///
    /// **Consumes the token** — the cursor lands at the token's *end*,
    /// so the next call starts after this token. The token itself is
    /// not included in the returned gap.
    ///
    /// **Trims blank lines** — the returned gap has blank lines
    /// removed when no comments are present (via `trim_if_clean`).
    /// This is correct for all intra-expression gaps (between tokens
    /// like `=`, `->`, operators, keywords) where blank lines are
    /// noise. Callers never need to wrap the result with
    /// `trim_if_clean`.
    ///
    /// Returns an empty gap if no matching token is found within
    /// `end`.
    pub(crate) fn advance_to_token(
        &mut self,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> TriviaGap {
        let tokens = &self.tokens.tokens;
        for (i, (token, span)) in tokens.iter().enumerate().skip(self.token_idx) {
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
                self.token_idx = i + 1;
                return TriviaGap { layout }.trim_if_clean();
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
        let tokens = &self.tokens.tokens;
        for (_i, (token, span)) in tokens.iter().enumerate().skip(self.token_idx) {
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
/// Prefer the `gap_none` / `gap_space` / `gap_hard` / `gap_list`
/// wrappers for standard call sites. Use this directly only when you
/// need custom `open`/`end` positioning that the wrappers don't
/// provide. See the module-level documentation for idempotency
/// guarantees.
pub fn format_gap(
    gap: TriviaGap,
    open: Option<Doc<'static>>,
    end: Option<Doc<'static>>,
    sep: Option<Doc<'static>>,
    style: &Style,
) -> Doc<'static> {
    if gap.layout.is_empty() {
        return sep.unwrap_or_else(|| ALLOC.nil());
    }

    // Compute auto open if not explicitly provided. Only applies when
    // the first element is a Comment (BlankLines provides its own break).
    let open = open.or_else(|| match gap.first() {
        Some(e @ TriviaElement::Comment(_)) => {
            if e.needs_start_newline() {
                Some(ALLOC.hardline())
            } else {
                Some(ALLOC.text(" "))
            }
        }
        _ => None,
    });

    // Compute auto end if not explicitly provided. Only applies when
    // the last element is a Comment (BlankLines provides its own break).
    let end = end.or_else(|| match gap.last() {
        Some(e @ TriviaElement::Comment(_)) => {
            if e.needs_end_newline() {
                Some(ALLOC.hardline())
            } else {
                Some(ALLOC.text(" "))
            }
        }
        _ => None,
    });

    let last_is_comment = matches!(gap.layout.last(), Some(TriviaElement::Comment(_)));
    // Each layout element pushes 1-3 parts (text + optional hardline +
    // optional separator). Pre-allocate to avoid reallocation for gaps
    // with multiple comments.
    let mut parts = Vec::with_capacity(gap.layout.len() * 2 + 1);
    let mut open = open;

    let mut layout = gap.layout;
    let n = layout.len();
    for index in 0..n {
        let element = &layout[index];
        // Separator before this element (not for the first).
        if index > 0 {
            let prev = &layout[index - 1];
            let is_blank = matches!(element, TriviaElement::BlankLines(_));
            let prev_is_blank = matches!(prev, TriviaElement::BlankLines(_));
            if !is_blank && !prev_is_blank {
                if prev.needs_end_newline() || element.needs_start_newline() {
                    parts.push(ALLOC.hardline());
                } else {
                    parts.push(ALLOC.text(" "));
                }
            }
        } else if let Some(open) = open.take()
            && matches!(element, TriviaElement::Comment(_))
        {
            parts.push(open);
        }

        match &mut layout[index] {
            TriviaElement::Comment(comment) => {
                if comment.is_multiline_block() {
                    // Split multiline block comments into lines so the
                    // doc builder applies indentation to each line via
                    // hardlines. Strip source whitespace from inner
                    // lines — the doc builder's nesting handles indent.
                    let text = std::mem::take(&mut comment.text);
                    let mut lines = text.split('\n');
                    parts.push(ALLOC.as_string(lines.next().unwrap()));
                    for line in lines {
                        parts.push(ALLOC.hardline());
                        parts.push(ALLOC.as_string(line.trim_start()));
                    }
                } else {
                    parts.push(ALLOC.text(std::mem::take(&mut comment.text)));
                }
            }
            TriviaElement::BlankLines(blanks) => {
                let capped = (*blanks).min(style.max_blank_lines);
                parts.push(hardlines(1 + capped));
            }
        }
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

struct TokenStream {
    tokens: Vec<(Token<'static>, Range<usize>)>,
    layout: SourceLayout,
}

fn build_comment(token: &Token, span: &Range<usize>, src: &str, line_starts: &[usize]) -> Comment {
    let line_idx = line_of(span.start, line_starts);
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
}
