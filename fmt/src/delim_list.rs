//! Delimited list builder and separator-gap utilities.

use share::DocAllocator;

use crate::ctx::{ALLOC, Doc};
use crate::style::Style;
use crate::trivia::TriviaElement;
use crate::trivia::{TokenCursor, TriviaGap, format_gap, gap_none};

/// Builder for items inside a delimited list.
///
/// Automatically picks the right gap function for each item's leading
/// gap:
/// - **First item**: `gap_list` — no space before a comment (it's
///   right after the open delimiter: `</* c */ F>`, not `< /* c */ F>`).
/// - **Subsequent items**: `gap_none` — space before a comment (it's
///   after a comma: `, /* c */ G>`).
///
/// The close-delimiter trailing (no space after comment before `>`/`)`) is
/// handled by `close_end = nil`.
///
/// All gaps passed to `push` and `push_sep` (leading gap, `before_sep`,
/// `after_sep`) are already trimmed at the source (`advance_to_token`
/// trims internally; `take_separator_gap_split` trims the after-sep
/// gap). Blank lines around separators and delimiters are treated as
/// noise when no comments are present.
pub(crate) struct DelimList<'a> {
    items: Vec<Doc<'static>>,
    is_first: bool,
    separator: &'static str,
    trailing_sep: bool,
    style: &'a Style,
}

impl<'a> DelimList<'a> {
    /// Create a new `DelimList`.
    ///
    /// - `separator`: the delimiter between items (e.g. `","`, `";"`).
    /// - `trailing_sep`: whether to emit a trailing separator in broken mode
    ///   (e.g. trailing comma in multi-line arg lists).
    pub(crate) fn new(style: &'a Style, separator: &'static str, trailing_sep: bool) -> Self {
        Self {
            items: Vec::new(),
            is_first: true,
            separator,
            trailing_sep,
            style,
        }
    }

    /// Push an item with a leading gap. The gap is rendered with
    /// `gap_list` for the first item (with `trim_start` to strip blank
    /// lines after the open delimiter), `gap_none` for subsequent items.
    pub(crate) fn push(&mut self, gap: TriviaGap, doc: Doc<'static>) {
        let gap = if self.is_first {
            gap_list(gap.trim_start(), self.style)
        } else {
            gap_none(gap, self.style)
        };
        self.items.push(ALLOC.concat([gap, doc]));
        self.is_first = false;
    }

    /// Push an item with a leading gap, followed by the separator.
    /// `before_sep` and `after_sep` are the gaps around the separator,
    /// passed to `sep_terminated_item`.
    pub(crate) fn push_sep(
        &mut self,
        gap: TriviaGap,
        doc: Doc<'static>,
        before_sep: TriviaGap,
        after_sep: TriviaGap,
    ) {
        let gap = if self.is_first {
            gap_list(gap.trim_start(), self.style)
        } else {
            gap_none(gap, self.style)
        };
        let item = ALLOC.concat([gap, doc]);
        self.items.push(sep_terminated_item(
            item,
            self.separator,
            before_sep,
            after_sep,
            self.style,
        ));
        self.is_first = false;
    }

    /// Build the final delimited-list doc.
    ///
    /// Flat mode (fits on one line): `open item1, item2 close`
    /// Broken mode (doesn't fit):
    /// ```text
    /// open
    ///     item1,
    ///     item2,
    /// close
    /// ```
    pub(crate) fn finish(
        self,
        open: &'static str,
        close: &'static str,
        close_comments: TriviaGap,
    ) -> Doc<'static> {
        self.finish_impl(open, close, close_comments, true)
    }

    /// Like `finish` but without the inner `.group()`.
    /// The caller is responsible for wrapping the result (plus any
    /// sibling content that should break together) in a `.group()`.
    pub(crate) fn finish_ungrouped(
        self,
        open: &'static str,
        close: &'static str,
        close_comments: TriviaGap,
    ) -> Doc<'static> {
        self.finish_impl(open, close, close_comments, false)
    }

    fn finish_impl(
        self,
        open: &'static str,
        close: &'static str,
        close_comments: TriviaGap,
        grouped: bool,
    ) -> Doc<'static> {
        let style = self.style;
        let items = self.items;
        let indent = style.indent_width() as isize;

        let close_comments = close_comments.trim_end();
        let close_needs_break = close_comments.needs_end_newline();
        let close_sep = if close_needs_break {
            ALLOC.hardline()
        } else {
            ALLOC.line_()
        };
        let close_end = if close_needs_break {
            Some(ALLOC.hardline())
        } else {
            Some(ALLOC.line_())
        };
        // Before close delimiter: auto open (hardline for at_line_start,
        // space for inline). The `line_()` sep is inside the group and may
        // not break in flat mode, but auto open provides explicit `hardline`
        // for at_line_start comments regardless.
        let close_gap = format_gap(close_comments, None, close_end, Some(close_sep), style);

        let trailing = if self.trailing_sep {
            ALLOC.text(self.separator).flat_alt(ALLOC.nil())
        } else {
            ALLOC.nil()
        };

        let inner = ALLOC.concat([ALLOC
            .concat([ALLOC.line_(), ALLOC.concat(items), trailing, close_gap])
            .nest(indent)]);
        let inner = if grouped { inner.group() } else { inner };
        ALLOC.text(open).append(inner).append(ALLOC.text(close))
    }
}

/// Format a single item followed by its separator, with comments around
/// the separator split into `before_sep` and `after_sep`.
///
/// Three cases:
/// 1. **Multiline gap** — comma first, all comments after.
/// 2. **Inline gap, flat mode** — preserve source positions.
/// 3. **Inline gap, broken mode** — comma first, A on same line, B on own line.
fn sep_terminated_item(
    item: Doc<'static>,
    separator: &'static str,
    before_sep: TriviaGap,
    after_sep: TriviaGap,
    style: &Style,
) -> Doc<'static> {
    // Check multiline without cloning — has_source_line_break on the
    // joined gap is equivalent to checking each gap separately (join
    // only coalesces adjacent BlankLines at the boundary, which doesn't
    // affect the any() check).
    let is_multiline = before_sep.has_source_line_break() || after_sep.has_source_line_break();

    if is_multiline {
        // Rule 1: Multiline gap — comma first, all comments after.
        let combined = before_sep.join(after_sep);
        let needs_break = combined.needs_end_newline();
        let sep = if needs_break {
            ALLOC.hardline()
        } else {
            ALLOC.line()
        };
        let end = if needs_break {
            Some(ALLOC.hardline())
        } else {
            Some(ALLOC.line())
        };
        ALLOC.concat([
            item,
            ALLOC.text(separator),
            format_gap(combined, None, end, Some(sep), style),
        ])
    } else {
        // Rule 2/3: Inline gap. Use flat_alt to switch between
        // preserve-positions (flat) and comma-first-split (broken).
        //
        // Flat:   item /*A*/, /*B*/
        // Broken: item, /*A*/
        //         /*B*/
        //         (next item on its own line via DelimList)

        // --- Flat layout: preserve source positions ---
        let before_flat = format_gap(
            before_sep.clone(),
            Some(ALLOC.text(" ")), // space before /*A*/
            Some(ALLOC.nil()),     // no trailing space — comma follows
            Some(ALLOC.nil()),     // no sep — separator text follows
            style,
        );
        let after_flat = format_gap(
            after_sep.clone(),
            Some(ALLOC.text(" ")), // space before /*B*/
            None,                  // auto end (space for inline block)
            Some(ALLOC.line()),    // space after comma for empty gap
            style,
        );
        let flat = ALLOC.concat([item.clone(), before_flat, ALLOC.text(separator), after_flat]);

        // --- Broken layout: comma first, A on same line, B on own line ---
        //
        // Four cases depending on which gaps have comments:
        // 1. Both empty:   `item,\n` — after_broken provides the hardline.
        // 2. Both used:    `item, /*A*/\n/*B*/\n` — after_broken's open
        //    hardline separates A from B; its end hardline separates B
        //    from the next item.
        // 3. Before only:  `item, /*A*/\n` — after_broken (empty) provides
        //    the hardline to the next item.
        // 4. After only:   `item,\n/*B*/\n` — after_broken's open hardline
        //    puts B on its own line.
        //
        // Key: before_broken uses `end = nil` (not hardline) to avoid a
        // double hardline with after_broken's open. after_broken always
        // provides the break — either via its open hardline (when comments
        // are present) or as a bare hardline (when empty).
        let before_broken = if before_sep.is_empty() {
            ALLOC.nil()
        } else {
            format_gap(
                before_sep,
                Some(ALLOC.text(" ")), // space before /*A*/ after comma
                Some(ALLOC.nil()),     // no trailing break — after_broken provides it
                Some(ALLOC.nil()),
                style,
            )
        };
        let after_broken = if after_sep.is_empty() {
            ALLOC.hardline()
        } else {
            format_gap(
                after_sep,
                Some(ALLOC.hardline()), // /*B*/ on its own line
                Some(ALLOC.hardline()), // hardline after /*B*/
                Some(ALLOC.nil()),
                style,
            )
        };
        let broken = ALLOC.concat([item, ALLOC.text(separator), before_broken, after_broken]);

        broken.flat_alt(flat)
    }
}

/// Returns the before-separator and after-separator gaps separately,
/// so callers can distinguish comments before the separator (/*A*/)
/// from comments after it (/*B*/).
pub(crate) fn take_separator_gap_split(
    cursor: &mut TokenCursor,
    end: usize,
    pred: impl Fn(&lang::parser::Token) -> bool,
) -> (TriviaGap, TriviaGap) {
    let before = cursor.advance_to_token(end, &pred);
    // `after` is the gap between the separator and the next item —
    // advance to the start of the next token (without consuming it)
    // and trim blank lines (intra-expression position).
    let next_start = cursor
        .peek_token(end, |_| true)
        .map(|r| r.start)
        .unwrap_or(end);
    let after = cursor.advance_to(next_start).trim_if_clean();
    (before, after)
}

/// Like `gap_none` but comments get `nil` open (no space/hardline before
/// the comment). Safe to use inside `DelimList` where the list's break
/// mode always provides a hardline when needed — a line comment forces
/// `has_source_line_break()` which forces the list to break.
fn gap_list(gap: TriviaGap, style: &Style) -> Doc<'static> {
    let open = match gap.first() {
        Some(TriviaElement::Comment(_)) => Some(ALLOC.nil()),
        _ => None,
    };
    format_gap(gap, open, None, None, style)
}
