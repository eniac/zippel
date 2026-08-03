//! CST construction with comment attachment.
//!
//! Builds a Concrete Syntax Tree from the AST + token stream, with
//! comments attached to nodes via tree-walk correlation (Bazel/buildtools
//! approach). Every comment belongs to exactly one node.

use lang::ast::arg::Arg;
use lang::ast::decl::{Body, Decl};
use lang::ast::exp::Exp;
use lang::ast::spanned::Spanned;
use lang::parser::{Token, lex_iter};
use lang::typ::Size;
use share::{BoxAllocator, DocAllocator, DocBuilder};
use std::ops::Range;

const ALLOC: BoxAllocator = BoxAllocator;
type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

// ── Comment types ──────────────────────────────────────────────────────

/// A comment extracted from the source.
#[derive(Debug, Clone)]
pub struct Comment {
    /// The comment text including `//` or `/* */` delimiters.
    pub text: String,
    /// Whether this is a block comment (vs a line comment).
    pub is_block: bool,
    /// Byte offset of the start of the comment in the source.
    pub start: usize,
    /// Byte offset of the end of the comment in the source.
    pub end: usize,
}

/// Comments attached to a CST node.
#[derive(Debug, Clone, Default)]
pub struct CommentAttachment {
    /// Comments on their own line before this node.
    /// Ordered top-to-bottom as they appear in source.
    pub leading: Vec<Comment>,
    /// A single end-of-line comment on the same line as this node's end.
    pub trailing: Option<Comment>,
}

// ── CST types ──────────────────────────────────────────────────────────

/// Source positions of tokens within an argument.
/// Used to locate inline comments between arg components.
#[derive(Debug, Clone, Default)]
pub struct ArgTokenSpans {
    /// Start position of the qualifier keyword (witness/instance/etc).
    /// 0 if the qualifier is implicit (Local).
    pub qualifier_start: usize,
    /// Start position of the identifier.
    pub id_start: usize,
    /// Start position of the colon.
    pub colon_start: usize,
    /// Start position of the type.
    pub typ_start: usize,
}

/// A CST argument — an AST arg with token spans for inline comment support.
#[derive(Debug, Clone)]
pub struct CstArg {
    pub arg: Arg<lang::id::Tid, Size>,
    pub span: Range<usize>,
    pub comments: CommentAttachment,
    /// Source positions of component tokens, for inline comment lookup.
    pub token_spans: ArgTokenSpans,
}

/// A declaration with comments, wrapping the spanned AST decl.
pub struct CstDecl {
    pub decl: Spanned<Decl<Size>>,
    /// Comments before this declaration.
    pub comments: CommentAttachment,
    /// Arguments with their own comment attachments and token spans.
    pub args: Vec<CstArg>,
    /// Body (for func/proto) with comment-annotated expressions.
    pub body: CstBody,
}

/// CST body — mirrors `Body` but with comment-annotated expressions.
pub enum CstBody {
    Func {
        body: Box<CstExp>,
    },
    Proto {
        relation: Box<CstExp>,
        body: Box<CstExp>,
    },
    TypeAlias,
}

/// CST expression — an expression with span and comments.
/// For Let/Log nodes, `body` is the next statement in the chain (as a
/// `Box<CstExp>`). For terminal expressions, `body` is None.
pub struct CstExp {
    /// The "header" of this statement: the let/log binding or the
    /// terminal expression. For Let/Log, this is the Exp with the body
    /// replaced by a placeholder — use `body` for the continuation.
    pub exp: Exp<Size>,
    pub span: Range<usize>,
    pub comments: CommentAttachment,
    /// The continuation (next statement) for Let/Log, or None for terminal.
    pub body: Option<Box<CstExp>>,
}

// ── Line table ─────────────────────────────────────────────────────────

/// Maps byte offset → line number (0-indexed).
struct LineTable {
    starts: Vec<usize>,
}

impl LineTable {
    fn new(src: &str) -> Self {
        let mut starts = vec![0];
        for (i, b) in src.bytes().enumerate() {
            if b == b'\n' {
                starts.push(i + 1);
            }
        }
        LineTable { starts }
    }

    fn line_of(&self, offset: usize) -> usize {
        match self.starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i.saturating_sub(1),
        }
    }
}

// ── Comment map ────────────────────────────────────────────────────────

/// Maps each token's start position to the comments that appear before it
/// (between the previous significant token and this one).
///
/// This is the key data structure for inline comment support. When the
/// formatter emits a token, it looks up `comments_before(token_start)` to
/// find any inline comments that should be emitted first.
#[derive(Debug)]
pub struct CommentMap {
    /// Sorted by position. Each entry: (token_start, comments_before_this_token).
    entries: Vec<(usize, Vec<Comment>)>,
    /// Line start offsets for line-of computation.
    line_starts: Vec<usize>,
    /// Comment start positions that have been consumed (e.g. as trailing
    /// on an arg). The formatter should skip these when emitting inline.
    /// Uses RefCell so `TokenCursor::advance_to` can consume through &CommentMap.
    consumed: std::cell::RefCell<std::collections::HashSet<usize>>,
}

impl CommentMap {
    /// Build a comment map from the token stream.
    fn new(tokens: &[(Token<'static>, Range<usize>)], src: &str) -> Self {
        let mut entries: Vec<(usize, Vec<Comment>)> = Vec::new();
        let mut pending_comments: Vec<Comment> = Vec::new();

        for (tok, span) in tokens {
            match tok {
                Token::LineComment | Token::BlockComment => {
                    let is_block = matches!(tok, Token::BlockComment);
                    pending_comments.push(Comment {
                        text: String::new(),
                        is_block,
                        start: span.start,
                        end: span.end,
                    });
                }
                Token::Whitespace => {}
                _ => {
                    if !pending_comments.is_empty() {
                        entries.push((span.start, std::mem::take(&mut pending_comments)));
                    }
                }
            }
        }

        entries.sort_by_key(|(pos, _)| *pos);

        // Build line starts for line-of computation.
        let mut line_starts = vec![0];
        for (i, b) in src.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }

        CommentMap {
            entries,
            line_starts,
            consumed: std::cell::RefCell::new(std::collections::HashSet::new()),
        }
    }

    /// Fill in comment text from the source string.
    fn fill_text(&mut self, src: &str) {
        for (_, comments) in &mut self.entries {
            for c in comments {
                c.text = src[c.start..c.end].to_string();
            }
        }
    }

    /// Mark a comment as consumed (e.g. it was used as a trailing comment).
    pub fn consume(&mut self, comment_start: usize) {
        self.consumed.get_mut().insert(comment_start);
    }

    /// Get comments that appear before the token at `pos`, excluding consumed ones.
    pub fn comments_before(&self, pos: usize) -> &[Comment] {
        match self.entries.binary_search_by_key(&pos, |(k, _)| *k) {
            Ok(i) => &self.entries[i].1,
            Err(_) => &[],
        }
    }

    /// Get unconsumed comments that appear before the token at `pos`.
    pub fn unconsumed_comments_before(&self, pos: usize) -> Vec<&Comment> {
        match self.entries.binary_search_by_key(&pos, |(k, _)| *k) {
            Ok(i) => self.entries[i]
                .1
                .iter()
                .filter(|c| !self.consumed.borrow().contains(&c.start))
                .collect(),
            Err(_) => Vec::new(),
        }
    }

    /// Check if there are unconsumed comments before `pos`.
    pub fn has_comments_before(&self, pos: usize) -> bool {
        !self.unconsumed_comments_before(pos).is_empty()
    }

    /// Get unconsumed comments before `pos` and mark them as consumed.
    /// Returns owned Comments so the caller can use them after the borrow ends.
    pub fn take_comments_before(&self, pos: usize) -> Vec<Comment> {
        match self.entries.binary_search_by_key(&pos, |(k, _)| *k) {
            Ok(i) => self.entries[i]
                .1
                .iter()
                .filter(|c| {
                    let mut consumed = self.consumed.borrow_mut();
                    if consumed.contains(&c.start) {
                        false
                    } else {
                        consumed.insert(c.start);
                        true
                    }
                })
                .cloned()
                .collect(),
            Err(_) => Vec::new(),
        }
    }

    /// Get the line number (0-indexed) of a byte offset.
    pub fn line_of(&self, offset: usize) -> usize {
        match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i.saturating_sub(1),
        }
    }
}

// ── TokenCursor ───────────────────────────────────────────────────────

/// A position-based cursor over the token stream that automatically
/// emits comments before tokens.
///
/// The cursor tracks a byte position in the source. As format functions
/// emit tokens left-to-right, they advance the cursor, which emits any
/// comments that appear between the old and new positions.
///
/// The `advance_to` / `skip_to` API centralizes comment emission and
/// token-finding into a single cursor object.
pub struct TokenCursor<'a> {
    tokens: &'a TokenStream,
    comment_map: &'a CommentMap,
    /// Current byte position — everything before this has been consumed.
    pos: usize,
}

impl<'a> TokenCursor<'a> {
    pub fn new(tokens: &'a TokenStream, comment_map: &'a CommentMap) -> Self {
        TokenCursor {
            tokens,
            comment_map,
            pos: 0,
        }
    }

    /// Current cursor position.
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// Borrow the underlying TokenStream (for creating sub-cursors).
    pub fn tokens_ref(&self) -> &'a TokenStream {
        self.tokens
    }

    /// Borrow the underlying CommentMap (for creating sub-cursors).
    pub fn comment_map_ref(&self) -> &'a CommentMap {
        self.comment_map
    }

    /// Advance to byte position `target`, emitting comments before `target`.
    /// Comments between `self.pos` and `target` that haven't been consumed
    /// are emitted and marked as consumed.
    ///
    /// This is the primary method for emitting comments before a token.
    /// The caller advances to the token's start position, gets back a Doc
    /// with the comments, then emits the token text itself.
    pub fn advance_to(&mut self, target: usize) -> Doc<'static> {
        let doc = self.emit_comments_before(target);
        self.pos = target;
        doc
    }

    /// Skip to byte position `target` without emitting comments.
    /// Used after a recursive call has already consumed tokens/comments
    /// for a sub-expression.
    pub fn skip_to(&mut self, target: usize) {
        self.pos = target;
    }

    /// Emit all unconsumed comments before `target` as leading comments
    /// (each on its own line). Used to flush remaining comments before
    /// a closing delimiter like `}`.
    pub fn flush_comments_before(&mut self, target: usize) -> Doc<'static> {
        let comments = self.comment_map.take_comments_before(target);
        if comments.is_empty() {
            return ALLOC.nil();
        }
        let mut parts = Vec::new();
        for c in &comments {
            parts.push(ALLOC.text(c.text.clone()));
            parts.push(ALLOC.hardline());
        }
        self.pos = target;
        ALLOC.concat(parts)
    }

    /// Check if there are unconsumed comments before `target` position.
    pub fn has_comments_before(&self, target: usize) -> bool {
        self.comment_map.has_comments_before(target)
    }

    /// Emit unconsumed comments before `target` position.
    /// Comments on a different line than the token → leading (hardline).
    /// Comments on the same line as the token → inline (space).
    fn emit_comments_before(&self, target: usize) -> Doc<'static> {
        let comments = self.comment_map.take_comments_before(target);
        if comments.is_empty() {
            return ALLOC.nil();
        }
        let token_line = self.comment_map.line_of(target);
        let mut parts = Vec::new();
        for c in &comments {
            let comment_end_line = self.comment_map.line_of(c.end.saturating_sub(1));
            if comment_end_line < token_line {
                parts.push(ALLOC.text(c.text.clone()));
                parts.push(ALLOC.hardline());
            } else {
                parts.push(ALLOC.text(c.text.clone()));
                if !c.is_block {
                    parts.push(ALLOC.hardline());
                }
                parts.push(ALLOC.text(" "));
            }
        }
        ALLOC.concat(parts)
    }

    // ── Token-finding helpers (delegate to TokenStream) ───────────────

    /// Find the first significant token at depth 0 within [self.pos, end)
    /// matching `pred`. Returns its start position.
    pub fn find_at_depth0(&self, end: usize, pred: impl Fn(&Token) -> bool) -> Option<usize> {
        self.tokens.find_first_at_depth0(self.pos, end, pred)
    }

    /// Find matching open/close brackets at depth 0 within [self.pos, end).
    /// Returns (open_start, open_end, close_start, close_end).
    pub fn find_brackets(
        &self,
        end: usize,
        open_pred: impl Fn(&Token) -> bool,
        close_pred: impl Fn(&Token) -> bool,
    ) -> Option<(usize, usize, usize, usize)> {
        self.tokens
            .find_brackets(self.pos, end, open_pred, close_pred)
    }

    /// Find all token start positions at depth 0 matching `pred`
    /// within [self.pos, end).
    pub fn find_all_at_depth0(&self, end: usize, pred: impl Fn(&Token) -> bool) -> Vec<usize> {
        self.tokens.find_all_at_depth0(self.pos, end, pred)
    }

    /// Find the first significant token within [self.pos, end).
    /// Returns its start position.
    pub fn first_significant(&self, end: usize) -> Option<usize> {
        self.tokens.first_significant(self.pos, end)
    }

    /// Find the end of the last significant token within [self.pos, end).
    pub fn last_significant_end(&self, end: usize) -> Option<usize> {
        self.tokens.last_significant_end(self.pos, end)
    }

    /// Get the token at a given start position.
    pub fn token_at(&self, pos: usize) -> Option<&Token<'_>> {
        self.tokens.token_at(pos)
    }

    /// Get the end position of the token starting at `pos`.
    pub fn token_end(&self, pos: usize) -> Option<usize> {
        self.tokens.token_end(pos)
    }

    /// Get the line number of a byte offset.
    pub fn line_of(&self, offset: usize) -> usize {
        self.comment_map.line_of(offset)
    }
}

// ── Token cursor ───────────────────────────────────────────────────────

/// A cached token stream with cursor operations.
pub struct TokenStream {
    tokens: Vec<(Token<'static>, Range<usize>)>,
}

impl TokenStream {
    fn new(src: &str) -> Self {
        let tokens: Vec<(Token<'static>, Range<usize>)> = lex_iter(src)
            .map(|(tok, span)| (tok.into_owned(), span.start..span.end))
            .collect();
        TokenStream { tokens }
    }

    /// Iterate over all tokens.
    fn tokens_iter(&self) -> std::slice::Iter<'_, (Token<'static>, Range<usize>)> {
        self.tokens.iter()
    }

    /// Find all token positions matching `pred` at brace depth 0 within
    /// [start, end).
    fn find_at_depth0(
        &self,
        start: usize,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> Vec<usize> {
        let mut result = Vec::new();
        let mut depth = 0i32;
        for (tok, span) in &self.tokens {
            if span.start < start {
                continue;
            }
            if span.end > end {
                break;
            }
            match tok {
                Token::LBrace | Token::LParen | Token::LBrack | Token::LAngle => depth += 1,
                Token::RBrace | Token::RParen | Token::RBrack | Token::RAngle => depth -= 1,
                _ => {}
            }
            if depth == 0 && pred(tok) {
                result.push(span.end);
            }
        }
        result
    }

    /// Find matching `{` and `}` at depth 0 within [start, end).
    /// Returns (open_brace_end, close_brace_start).
    fn find_body_braces(&self, start: usize, end: usize) -> Option<(usize, usize)> {
        let mut open_brace = None;
        let mut depth = 0i32;
        for (tok, span) in &self.tokens {
            if span.start < start {
                continue;
            }
            if span.end > end {
                break;
            }
            match tok {
                Token::LBrace => {
                    if depth == 0 {
                        open_brace = Some(span.end);
                    }
                    depth += 1;
                }
                Token::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return Some((open_brace?, span.start));
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Find matching `(` and `)` at depth 0 within [start, end).
    /// Returns (open_paren_end, close_paren_start).
    fn find_parens(&self, start: usize, end: usize) -> Option<(usize, usize)> {
        let mut open_paren = None;
        let mut depth = 0i32;
        for (tok, span) in &self.tokens {
            if span.start < start {
                continue;
            }
            if span.end > end {
                break;
            }
            match tok {
                Token::LParen => {
                    if depth == 0 {
                        open_paren = Some(span.end);
                    }
                    depth += 1;
                }
                Token::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return Some((open_paren?, span.start));
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Find the end of the last non-trivia token before `offset`.
    /// Trivia = whitespace, line comments, block comments.
    fn last_token_end_before(&self, offset: usize) -> Option<usize> {
        self.tokens
            .iter()
            .rev()
            .find(|(tok, span)| {
                span.end <= offset
                    && !matches!(
                        tok,
                        Token::Whitespace | Token::LineComment | Token::BlockComment
                    )
            })
            .map(|(_, span)| span.end)
    }

    // ── Public helpers for the formatter ────────────────────────────────

    /// Find the first significant (non-trivia) token within [start, end).
    /// Returns the token's start position.
    pub fn first_significant(&self, start: usize, end: usize) -> Option<usize> {
        self.tokens.iter().find_map(|(tok, span)| {
            if span.start >= start && span.end <= end && !tok.is_trivia() {
                Some(span.start)
            } else {
                None
            }
        })
    }

    /// Find the end position of the last significant token within [start, end).
    pub fn last_significant_end(&self, start: usize, end: usize) -> Option<usize> {
        self.tokens.iter().rev().find_map(|(tok, span)| {
            if span.start >= start && span.end <= end && !tok.is_trivia() {
                Some(span.end)
            } else {
                None
            }
        })
    }

    /// Find the first token at depth 0 within [start, end) matching `pred`.
    /// Returns the token's start position.
    pub fn find_first_at_depth0(
        &self,
        start: usize,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> Option<usize> {
        let mut depth = 0i32;
        for (tok, span) in &self.tokens {
            if span.start < start {
                continue;
            }
            if span.end > end {
                break;
            }
            if tok.is_trivia() {
                continue;
            }
            match tok {
                Token::LBrace | Token::LParen | Token::LBrack | Token::LAngle => depth += 1,
                Token::RBrace | Token::RParen | Token::RBrack | Token::RAngle => depth -= 1,
                _ => {}
            }
            if depth == 0 && pred(tok) {
                return Some(span.start);
            }
        }
        None
    }

    /// Find all token start positions matching `pred` at depth 0 within
    /// [start, end), excluding trivia.
    pub fn find_all_at_depth0(
        &self,
        start: usize,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> Vec<usize> {
        let mut result = Vec::new();
        let mut depth = 0i32;
        for (tok, span) in &self.tokens {
            if span.start < start {
                continue;
            }
            if span.end > end {
                break;
            }
            if tok.is_trivia() {
                continue;
            }
            match tok {
                Token::LBrace | Token::LParen | Token::LBrack | Token::LAngle => depth += 1,
                Token::RBrace | Token::RParen | Token::RBrack | Token::RAngle => depth -= 1,
                _ => {}
            }
            if depth == 0 && pred(tok) {
                result.push(span.start);
            }
        }
        result
    }

    /// Find matching open/close brackets at depth 0 within [start, end).
    /// `open_pred` and `close_pred` identify the bracket types.
    /// Returns (open_start, open_end, close_start, close_end).
    pub fn find_brackets(
        &self,
        start: usize,
        end: usize,
        open_pred: impl Fn(&Token) -> bool,
        close_pred: impl Fn(&Token) -> bool,
    ) -> Option<(usize, usize, usize, usize)> {
        let mut open_span = None;
        let mut depth = 0i32;
        for (tok, span) in &self.tokens {
            if span.start < start {
                continue;
            }
            if span.end > end {
                break;
            }
            if tok.is_trivia() {
                continue;
            }
            if open_pred(tok) {
                if depth == 0 {
                    open_span = Some((span.start, span.end));
                }
                depth += 1;
            } else if close_pred(tok) {
                depth -= 1;
                if depth == 0 {
                    let (os, oe) = open_span?;
                    return Some((os, oe, span.start, span.end));
                }
            }
        }
        None
    }

    /// Get the token at a given start position (first token whose span
    /// starts at exactly `pos`).
    pub fn token_at(&self, pos: usize) -> Option<&Token<'_>> {
        self.tokens
            .iter()
            .find(|(_, span)| span.start == pos)
            .map(|(tok, _)| tok)
    }

    /// Get the end position of the token starting at `pos`.
    pub fn token_end(&self, pos: usize) -> Option<usize> {
        self.tokens
            .iter()
            .find(|(_, span)| span.start == pos)
            .map(|(_, span)| span.end)
    }

    /// Find the position of the first significant token at any depth
    /// within [start, end) that matches `pred`.
    pub fn find_first_significant(
        &self,
        start: usize,
        end: usize,
        pred: impl Fn(&Token) -> bool,
    ) -> Option<usize> {
        self.tokens.iter().find_map(|(tok, span)| {
            if span.start >= start && span.end <= end && !tok.is_trivia() && pred(tok) {
                Some(span.start)
            } else {
                None
            }
        })
    }
}

// ── Comment extraction ─────────────────────────────────────────────────

fn extract_comments(src: &str) -> Vec<Comment> {
    lex_iter(src)
        .filter(|(tok, _)| matches!(tok, Token::LineComment | Token::BlockComment))
        .map(|(tok, span)| Comment {
            text: src[span.start..span.end].to_string(),
            is_block: matches!(tok, Token::BlockComment),
            start: span.start,
            end: span.end,
        })
        .collect()
}

// ── CST construction ───────────────────────────────────────────────────

/// Build a CST from the source text and parsed declarations.
///
/// Returns the CST declarations, a comment map for inline comment lookup,
/// the token stream, and file-level leading/trailing comments.
pub fn build_cst(
    src: &str,
    decls: &[Spanned<Decl<Size>>],
) -> (
    Vec<CstDecl>,
    CommentMap,
    TokenStream,
    Vec<Comment>,
    Vec<Comment>,
) {
    let comments = extract_comments(src);
    let lines = LineTable::new(src);
    let tokens = TokenStream::new(src);

    // Build the comment map for inline comment support.
    let mut comment_map = CommentMap::new(&tokens.tokens, src);
    comment_map.fill_text(src);

    if decls.is_empty() {
        return (vec![], comment_map, tokens, comments, vec![]);
    }

    // File-level leading: before the first declaration.
    let file_leading: Vec<Comment> = comments
        .iter()
        .filter(|c| c.end <= decls[0].span.start)
        .cloned()
        .collect();

    // Consume file-level leading comments so they don't get re-emitted
    // by the cursor when formatting the first decl.
    for c in &file_leading {
        comment_map.consume(c.start);
    }

    // File-level trailing: after the last declaration.
    let file_trailing: Vec<Comment> = comments
        .iter()
        .filter(|c| c.start >= decls[decls.len() - 1].span.end)
        .cloned()
        .collect();

    let mut result = Vec::with_capacity(decls.len());

    for (i, decl) in decls.iter().enumerate() {
        // Leading comments for this decl: between prev decl end and this decl start.
        let leading: Vec<Comment> = if i == 0 {
            Vec::new() // handled by file_leading
        } else {
            let prev_end = decls[i - 1].span.end;
            comments
                .iter()
                .filter(|c| c.start >= prev_end && c.end <= decl.span.start)
                .filter(|c| {
                    let prev_end_line = lines.line_of(prev_end);
                    let comment_line = lines.line_of(c.start);
                    comment_line > prev_end_line
                })
                .cloned()
                .collect()
        };

        // Consume decl leading comments so they don't get re-emitted
        // by the cursor when formatting the decl's first token.
        for c in &leading {
            comment_map.consume(c.start);
        }

        // Trailing comment for this decl: on the same line as decl end.
        let trailing = comments
            .iter()
            .find(|c| {
                c.start >= decl.span.end && lines.line_of(c.start) == lines.line_of(decl.span.end)
            })
            .cloned();

        // Consume decl trailing comment.
        if let Some(ref c) = trailing {
            comment_map.consume(c.start);
        }

        // Build arg CST nodes with comment attachments.
        let args = build_cst_args(&tokens, decl, &comments, &lines);

        // Consume trailing comments from the comment map so they don't
        // get re-emitted as inline/leading comments on the next token.
        for a in &args {
            if let Some(trailing) = &a.comments.trailing {
                comment_map.consume(trailing.start);
            }
        }

        // Build body CST.
        let body = build_cst_body(&tokens, decl, &comments, &lines, &mut comment_map);

        result.push(CstDecl {
            decl: decl.clone(),
            comments: CommentAttachment { leading, trailing },
            args,
            body,
        });
    }

    (result, comment_map, tokens, file_leading, file_trailing)
}

/// Build CST arg nodes with comment attachments and token spans.
fn build_cst_args(
    tokens: &TokenStream,
    decl: &Spanned<Decl<Size>>,
    comments: &[Comment],
    lines: &LineTable,
) -> Vec<CstArg> {
    let arg_count = decl.node.sig.args.0.len();
    if arg_count == 0 {
        return Vec::new();
    }

    // Find the argument list parens within the decl span.
    let Some((paren_start, paren_end)) = tokens.find_parens(decl.span.start, decl.span.end) else {
        return Vec::new();
    };

    // Find comma positions at depth 0 within the parens.
    let comma_ends: Vec<usize> =
        tokens.find_at_depth0(paren_start, paren_end, |t| matches!(t, Token::Comma));

    // Derive arg spans from comma positions.
    let last_token_end = tokens.last_token_end_before(paren_end).unwrap_or(paren_end);

    let mut boundaries = vec![paren_start];
    boundaries.extend(comma_ends);
    boundaries.push(last_token_end);

    let actual_args = &decl.node.sig.args.0;

    // Build CstArg for each arg with derived span and token spans.
    let mut arg_nodes: Vec<CstArg> = Vec::new();
    for (j, arg) in actual_args.iter().enumerate() {
        let span_start = boundaries.get(j).copied().unwrap_or(paren_start);
        let span_end = boundaries.get(j + 1).copied().unwrap_or(paren_end);
        let span = span_start..span_end;

        // Find token positions within this arg for inline comment support.
        let token_spans = find_arg_token_spans(&tokens.tokens, &span, &arg.qualifier);

        arg_nodes.push(CstArg {
            arg: arg.clone(),
            span,
            comments: CommentAttachment::default(),
            token_spans,
        });
    }

    // Precompute spans for boundary lookups.
    let spans: Vec<Range<usize>> = arg_nodes.iter().map(|n| n.span.clone()).collect();

    // Classify comments for each arg:
    // - Leading: on their own line before the first significant token of the arg.
    // - Trailing: after the last significant token of the arg (before comma or `)`).
    // - Inline: between tokens within the arg (handled by CommentMap, not here).
    for (j, arg_node) in arg_nodes.iter_mut().enumerate() {
        let span = &spans[j];
        // Find the first significant token in this arg.
        let first_tok_start = tokens
            .tokens_iter()
            .find(|(tok, ts)| {
                ts.start >= span.start
                    && ts.end <= span.end
                    && !matches!(
                        tok,
                        Token::Whitespace | Token::LineComment | Token::BlockComment
                    )
            })
            .map(|(_, ts)| ts.start);
        // Find the last significant token in this arg.
        let last_tok_end = tokens
            .tokens_iter()
            .rev()
            .find(|(tok, ts)| {
                ts.start >= span.start
                    && ts.end <= span.end
                    && !matches!(
                        tok,
                        Token::Whitespace | Token::LineComment | Token::BlockComment
                    )
            })
            .map(|(_, ts)| ts.end);

        let Some(_first_start) = first_tok_start else {
            continue;
        };
        let Some(last_end) = last_tok_end else {
            continue;
        };

        // Comments within this arg's span.
        let arg_comments: Vec<&Comment> = comments
            .iter()
            .filter(|c| c.start >= span.start && c.end <= span.end)
            .collect();

        for c in arg_comments {
            if c.start >= last_end {
                // Comment after the last token → trailing.
                if arg_node.comments.trailing.is_none() {
                    arg_node.comments.trailing = Some(c.clone());
                }
            }
            // Otherwise (before first token or between tokens) → handled by CommentMap.
        }

        // For the last arg, also check for comments after the span end
        // but before `)` (the span end is the last token, not `)`).
        if j == spans.len() - 1 {
            let last_tok_line = lines.line_of(last_end);
            let after_comments: Vec<&Comment> = comments
                .iter()
                .filter(|c| {
                    c.start >= span.end
                        && c.end <= paren_end
                        && lines.line_of(c.start) == last_tok_line
                })
                .collect();
            for c in after_comments {
                if arg_node.comments.trailing.is_none() {
                    arg_node.comments.trailing = Some(c.clone());
                }
            }
        }

        // Also handle trailing comments after this arg's last token but
        // before the next arg's first token (e.g., after the comma).
        if j + 1 < spans.len() {
            let next_span = &spans[j + 1];
            let last_tok_line = lines.line_of(last_end);
            // Find the first significant token in the next arg.
            let next_first_start = tokens
                .tokens_iter()
                .find(|(tok, ts)| {
                    ts.start >= next_span.start
                        && ts.end <= next_span.end
                        && !matches!(
                            tok,
                            Token::Whitespace | Token::LineComment | Token::BlockComment
                        )
                })
                .map(|(_, ts)| ts.start)
                .unwrap_or(next_span.end);
            let after_comments: Vec<&Comment> = comments
                .iter()
                .filter(|c| {
                    c.start >= span.end
                        && c.end <= next_first_start
                        && lines.line_of(c.start) == last_tok_line
                })
                .collect();

            for c in after_comments {
                if arg_node.comments.trailing.is_none() {
                    arg_node.comments.trailing = Some(c.clone());
                }
            }
        }
    }

    arg_nodes
}

/// Find the source positions of component tokens within an arg.
///
/// Walks the token stream within the arg's span and identifies:
/// - qualifier_start: position of the qualifier keyword (witness/instance/etc)
/// - id_start: position of the identifier
/// - colon_start: position of the colon
/// - typ_start: position of the first token of the type
fn find_arg_token_spans(
    tokens: &[(Token<'static>, Range<usize>)],
    span: &Range<usize>,
    qualifier: &lang::typ::Qualifier,
) -> ArgTokenSpans {
    let mut spans = ArgTokenSpans::default();

    // Skip leading comments and whitespace to find the first significant token.
    let mut found_qualifier = false;
    let mut found_id = false;
    let mut found_colon = false;

    for (tok, tok_span) in tokens {
        if tok_span.start < span.start || tok_span.end > span.end {
            continue;
        }

        // Skip trivia.
        if matches!(
            tok,
            Token::Whitespace | Token::LineComment | Token::BlockComment
        ) {
            continue;
        }

        if !found_qualifier {
            // The first significant token should be the qualifier keyword
            // (or the identifier if the qualifier is implicit/Local).
            if matches!(qualifier, lang::typ::Qualifier::Local) {
                // No qualifier keyword — the first token is the identifier.
                found_qualifier = true;
                found_id = true;
                spans.id_start = tok_span.start;
            } else {
                spans.qualifier_start = tok_span.start;
                found_qualifier = true;
            }
            continue;
        }

        if !found_id {
            // Skip distribution keywords (uniform) and the * after uniform*.
            if matches!(tok, Token::KwUniform | Token::Star) {
                continue;
            }
            // This should be the identifier.
            spans.id_start = tok_span.start;
            found_id = true;
            continue;
        }

        if !found_colon && matches!(tok, Token::Colon) {
            spans.colon_start = tok_span.start;
            found_colon = true;
            continue;
        }

        if found_colon && spans.typ_start == 0 {
            // The first significant token after the colon is the start of the type.
            spans.typ_start = tok_span.start;
            break;
        }
    }

    spans
}

/// Build CST body with comment-annotated expressions.
fn build_cst_body(
    tokens: &TokenStream,
    decl: &Spanned<Decl<Size>>,
    comments: &[Comment],
    lines: &LineTable,
    comment_map: &mut CommentMap,
) -> CstBody {
    match &decl.node.body {
        Body::Func { body } => {
            let Some((brace_start, brace_end)) =
                tokens.find_body_braces(decl.span.start, decl.span.end)
            else {
                return CstBody::Func {
                    body: Box::new(CstExp {
                        exp: body.clone(),
                        span: decl.span.start..decl.span.end,
                        comments: CommentAttachment::default(),
                        body: None,
                    }),
                };
            };
            let cst_exp = build_cst_exp_chain(
                tokens,
                body,
                brace_start,
                brace_end,
                comments,
                lines,
                comment_map,
            );
            CstBody::Func {
                body: Box::new(cst_exp),
            }
        }
        Body::Proto { relation, body } => {
            let Some((brace_start, brace_end)) =
                tokens.find_body_braces(decl.span.start, decl.span.end)
            else {
                return CstBody::Proto {
                    relation: Box::new(CstExp {
                        exp: relation.clone(),
                        span: decl.span.start..decl.span.end,
                        comments: CommentAttachment::default(),
                        body: None,
                    }),
                    body: Box::new(CstExp {
                        exp: body.clone(),
                        span: decl.span.start..decl.span.end,
                        comments: CommentAttachment::default(),
                        body: None,
                    }),
                };
            };
            let cst_body = build_cst_exp_chain(
                tokens,
                body,
                brace_start,
                brace_end,
                comments,
                lines,
                comment_map,
            );
            // Relation doesn't have its own brace scope — use the decl span.
            let cst_relation = CstExp {
                exp: relation.clone(),
                span: decl.span.start..brace_start,
                comments: CommentAttachment::default(),
                body: None,
            };
            CstBody::Proto {
                relation: Box::new(cst_relation),
                body: Box::new(cst_body),
            }
        }
        Body::TypeAlias => CstBody::TypeAlias,
    }
}

/// Build a CstExp chain from a Let/Log expression chain.
///
/// Walks the Let/Log chain, deriving each statement's span from the token
/// stream (using `;` positions at depth 0), and attaches comments.
fn build_cst_exp_chain(
    tokens: &TokenStream,
    exp: &Exp<Size>,
    body_start: usize,
    body_end: usize,
    comments: &[Comment],
    lines: &LineTable,
    comment_map: &mut CommentMap,
) -> CstExp {
    // Find all `;` at depth 0 within the body.
    let semi_ends: Vec<usize> =
        tokens.find_at_depth0(body_start, body_end, |t| matches!(t, Token::Semi));

    // For the last boundary, use the end of the last non-comment token
    // before `}`, not `body_end` itself (which is the position of `}`
    // and may be on a different line than the last statement).
    let last_token_end = tokens.last_token_end_before(body_end).unwrap_or(body_end);

    // The first boundary should be the first significant token position
    // (e.g. `let`), not `body_start` (which is after `{`). This ensures
    // leading comments between `{` and the first statement fall BEFORE
    // the first node's span, so attach_comments_to_cst_exps attaches them
    // as leading rather than treating them as inline within the span.
    let first_sig = tokens
        .first_significant(body_start, body_end)
        .unwrap_or(body_start);

    // Build a flat list of statement spans.
    let mut boundaries = vec![first_sig];
    boundaries.extend(&semi_ends);
    boundaries.push(last_token_end);

    // Walk the Let/Log chain to collect (exp, span) pairs.
    let mut stmts: Vec<(Exp<Size>, Range<usize>)> = Vec::new();
    collect_stmts(exp, &boundaries, 0, &mut stmts);

    // Build flat CstExp nodes (without body links, without comments).
    let mut nodes: Vec<CstExp> = stmts
        .into_iter()
        .map(|(e, span)| CstExp {
            exp: e,
            span,
            comments: CommentAttachment::default(),
            body: None,
        })
        .collect();

    // Filter comments to the body span.
    let body_comments: Vec<Comment> = comments
        .iter()
        .filter(|c| c.start >= body_start && c.end <= body_end)
        .cloned()
        .collect();

    // Attach comments to the flat list using the same tree-walk logic.
    attach_comments_to_cst_exps(&mut nodes, &body_comments, lines, tokens);

    // Consume comments from the CommentMap so they don't get re-emitted
    // by the cursor's advance_to. We consume only comments that were
    // explicitly attached as leading/trailing on CstExp nodes.
    // Comments WITHIN a node's span that were NOT attached (inline comments)
    // stay in the map for the cursor to emit.
    // Comments NOT within any node's span (between nodes, before first,
    // after last) also stay in the map — the cursor will emit them when
    // advancing past the relevant positions.
    for node in &nodes {
        for c in &node.comments.leading {
            comment_map.consume(c.start);
        }
        if let Some(ref c) = node.comments.trailing {
            comment_map.consume(c.start);
        }
    }

    // Link the CstExp nodes into a chain.
    link_cst_exp_chain(nodes)
}

/// Walk a Let/Log chain and collect (exp, span) pairs for each statement.
fn collect_stmts(
    exp: &Exp<Size>,
    boundaries: &[usize],
    idx: usize,
    out: &mut Vec<(Exp<Size>, Range<usize>)>,
) {
    let span_start = boundaries.get(idx).copied().unwrap_or(0);
    let span_end = boundaries.get(idx + 1).copied().unwrap_or(0);
    let span = span_start..span_end;
    match exp {
        Exp::Let(x, val, body) => {
            out.push((
                Exp::Let(x.clone(), val.clone(), Box::new((**body).clone())),
                span,
            ));
            collect_stmts(body, boundaries, idx + 1, out);
        }
        Exp::Log(x, val, body) => {
            out.push((
                Exp::Log(x.clone(), val.clone(), Box::new((**body).clone())),
                span,
            ));
            collect_stmts(body, boundaries, idx + 1, out);
        }
        _ => {
            out.push((exp.clone(), span));
        }
    }
}

/// Link a flat list of CstExp nodes into a chain by setting `body` fields.
fn link_cst_exp_chain(mut nodes: Vec<CstExp>) -> CstExp {
    if nodes.len() == 1 {
        return nodes.into_iter().next().unwrap();
    }
    // Link in reverse: each node's body is the next node.
    let mut tail = nodes.pop().unwrap();
    while let Some(mut head) = nodes.pop() {
        head.body = Some(Box::new(tail));
        tail = head;
    }
    tail
}

/// Attach comments to a slice of CstExp nodes by tree-walk correlation.
fn attach_comments_to_cst_exps(
    nodes: &mut [CstExp],
    comments: &[Comment],
    lines: &LineTable,
    tokens: &TokenStream,
) {
    if nodes.is_empty() || comments.is_empty() {
        return;
    }

    let first_start = nodes[0].span.start;
    let last_end = nodes[nodes.len() - 1].span.end;

    for comment in comments {
        let comment_line = lines.line_of(comment.start);

        // Comment before the first node → leading on first node.
        if comment.end <= first_start {
            nodes[0].comments.leading.push(comment.clone());
            continue;
        }

        // Comment after the last node → trailing on last node.
        if comment.start >= last_end {
            if nodes.last().unwrap().comments.trailing.is_none() {
                nodes.last_mut().unwrap().comments.trailing = Some(comment.clone());
            }
            continue;
        }

        // Check if comment is on the same line as a previous node's span end.
        // This handles trailing comments after `;`: the comment falls within
        // the NEXT statement's span, but is on the same line as the `;`.
        let mut assigned = false;
        for node in nodes.iter_mut() {
            let prev_end_line = lines.line_of(node.span.end);
            if comment_line == prev_end_line && comment.start >= node.span.end {
                if node.comments.trailing.is_none() {
                    node.comments.trailing = Some(comment.clone());
                    assigned = true;
                }
                break;
            }
        }
        if assigned {
            continue;
        }

        // Find which node's span contains this comment.
        // Comments WITHIN a node's span are inline comments (e.g. `a /* c */ + b`).
        // Leave them in the comment map for the cursor to handle —
        // do NOT attach them as leading/trailing on the CstExp node.
        // Only attach as leading if the comment is on a different line than
        // the node's first significant token (true leading comment on its own line).
        for node in nodes.iter_mut() {
            if comment.start >= node.span.start && comment.end <= node.span.end {
                // Find the first significant token within this node's span.
                let first_sig = tokens
                    .first_significant(node.span.start, node.span.end)
                    .unwrap_or(node.span.start);
                let first_sig_line = lines.line_of(first_sig);
                if comment_line < first_sig_line {
                    // Comment is on its own line before the node's first token.
                    node.comments.leading.push(comment.clone());
                }
                // Otherwise: inline comment within the expression — skip.
                // It stays in the comment map for the cursor to emit.
                break;
            }
        }
    }
}
