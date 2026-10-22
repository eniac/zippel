//! Declaration formatting.

use lang::ast::arg::Arg;
use lang::ast::decl::{Body, Decl};
use lang::ast::sig::Sig;
use lang::ast::{Size, Spanned};
use lang::id::Tid;
use lang::parser::Token;
use lang::typ::Qualifier;
use pretty::DocAllocator;

use crate::ctx::{Arena, Doc, Formatter, hardlines};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::style::Style;
use crate::trivia::{
    TokenCursor, TriviaElement, TriviaGap, format_gap, gap_hard, gap_none, gap_space,
};

pub fn format_decls(decls: &[Spanned<Decl<Size>>], src: &str, style: &Style) -> String {
    let arena = Arena::new();
    let alloc = &arena;
    let src_len = src.len();
    let mut fmt = Formatter {
        alloc,
        cursor: TokenCursor::new(src),
        style,
    };
    let mut parts = Vec::new();

    for (index, decl) in decls.iter().enumerate() {
        let gap = fmt.cursor.advance_to(decl.span.start);
        if index > 0 {
            if gap.is_empty() {
                parts.push(hardlines(alloc, 1 + style.max_blank_lines.min(1)));
            } else if matches!(gap.first(), Some(TriviaElement::BlankLines(_)))
                || matches!(gap.last(), Some(TriviaElement::BlankLines(_)))
            {
                // Gap contains blank lines — they carry the separation.
                parts.push(gap_none(alloc, gap, style));
            } else {
                // Gap is all comments, no blank lines — force one blank
                // line after the comment. `gap_hard` provides the
                // hardline after the comment; add an extra hardline for
                // the blank line.
                parts.push(gap_hard(alloc, gap, style));
                parts.push(hardlines(alloc, style.max_blank_lines.min(1)));
            }
        } else {
            // First decl — gap before it is the file header. `nil` open:
            // nothing precedes the comment, so no space/hardline needed.
            parts.push(format_gap(alloc, gap, Some(alloc.nil()), None, None, style));
        }
        parts.push(fmt.format_decl(decl));
    }

    if !decls.is_empty() {
        // Trailing gap after last decl — `sep = hardline` provides the
        // structural break; auto open/end handle comments.
        let trailing = fmt.cursor.advance_to(src_len);
        parts.push(format_gap(
            alloc,
            trailing,
            None,
            None,
            Some(alloc.hardline()),
            style,
        ));
    } else {
        // No decls — entire file is comments. `nil` open: nothing
        // precedes the first comment.
        parts.push(format_gap(
            alloc,
            fmt.cursor.advance_to(src_len),
            Some(alloc.nil()),
            None,
            None,
            style,
        ));
    }

    let mut output = String::new();
    alloc
        .concat(parts)
        .1
        .render_fmt(style.width, &mut output)
        .expect("rendering failed");

    // Trim trailing whitespace from each line, strip trailing blank
    // lines, and ensure exactly one trailing newline.
    trim_lines(&mut output);
    output
}

/// Trim trailing whitespace from each line, strip trailing blank
/// lines, and ensure exactly one trailing newline.
fn trim_lines(s: &mut String) {
    // Trim trailing whitespace from each line.
    let mut result = String::with_capacity(s.len());
    for line in s.lines() {
        result.push_str(line.trim_end());
        result.push('\n');
    }
    // Strip trailing blank lines, leaving exactly one trailing newline.
    while result.ends_with("\n\n") {
        result.pop();
    }
    *s = result;
}

impl<'doc> Formatter<'doc, '_> {
    fn format_decl(&mut self, decl: &Spanned<Decl<Size>>) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        let end = decl.span.end;
        match &decl.node.body {
            Body::Proto { relation, body } => {
                let keyword_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwProto));
                let (sig_gap, name_typevars, args) = self.format_sig(&decl.node.sig, end);
                let where_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwWhere))
                    .trim_start();

                // When comments are present between `)` and `where`, use
                // `format_gap` with `open = hardline()` so the comment starts
                // on a new line (not glued to `)`), and `where` follows on
                // its own line without a leading space.
                let has_where_comments = where_gap.has_comments();
                let where_comments = if has_where_comments {
                    format_gap(
                        alloc,
                        where_gap,
                        Some(alloc.hardline()),
                        Some(alloc.hardline()),
                        None,
                        style,
                    )
                } else {
                    gap_space(alloc, where_gap, style)
                };

                let relation = self.format_relation(relation.root());

                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBrace));

                // Comments before `{` go inside the where group's nest so they
                // align with the relation body, not at column 0. Same pattern
                // as the leading gap in `format_relation`.
                let open = match open_gap.first() {
                    Some(e) if !e.needs_start_newline() => Some(alloc.line()),
                    _ => None,
                };
                let open_comments =
                    format_gap(alloc, open_gap, open, None, Some(alloc.line()), style);

                let body = self.format_body(body.as_ref().map(|b| b.root()), end);

                alloc.concat([
                    gap_none(alloc, keyword_gap, style),
                    alloc.text("proto"),
                    gap_space(alloc, sig_gap, style),
                    name_typevars,
                    // Group args so they break as a unit. The `where` clause is
                    // separate and should not force args to break.
                    args.group(),
                    where_comments,
                    alloc
                        .concat([
                            alloc.text("where"),
                            alloc.concat([relation]).nest(style.indent_width() as isize),
                            open_comments.nest(style.indent_width() as isize),
                        ])
                        .group(),
                    alloc.text("{"),
                    body.nest(style.indent_width() as isize),
                    alloc.text("}"),
                ])
            }
            Body::Func { body } => {
                let keyword_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwFn));
                let (sig_gap, name_typevars, args) = self.format_sig(&decl.node.sig, end);
                let ret = if let Some(ret) = &decl.node.sig.ret {
                    // Gap after `)` — strip blank lines (structural position).
                    let arrow_gap = self
                        .cursor
                        .advance_to_token(end, |token| matches!(token, Token::Arrow))
                        .trim_start();
                    let (ret_gap, ret_doc) = self.format_typ(&ret.node, ret.span.end);
                    alloc.concat([
                        gap_space(alloc, arrow_gap, style),
                        alloc.text("->"),
                        gap_space(alloc, ret_gap, style),
                        ret_doc,
                    ])
                } else {
                    alloc.nil()
                };
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBrace));

                // Gap before `{` — strip blank lines on both ends (rustfmt
                // behavior: `{` stays on the same line as the signature, blank
                // lines are noise). Comments are preserved.
                let open_comments = gap_space(alloc, open_gap.trim(), style);

                // Group args + ret so they break together: when the group
                // breaks, args go on separate lines (via line_() in the
                // ungrouped DelimList) and ret stays on the same line as `)`.
                // Typevars are outside this group — they break independently
                // via their own inner group.
                let args_ret = alloc.concat([args, ret]).group();

                let body = self.format_body(body.as_ref().map(|b| b.root()), end);

                alloc.concat([
                    gap_none(alloc, keyword_gap, style),
                    alloc.text("fn"),
                    gap_space(alloc, sig_gap, style),
                    name_typevars,
                    args_ret,
                    open_comments,
                    alloc.text("{"),
                    body.nest(style.indent_width() as isize),
                    alloc.text("}"),
                ])
            }
            Body::TypeAlias => {
                let keyword_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwType));
                let name_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let eq_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Eq));
                let typ = decl
                    .node
                    .sig
                    .ret
                    .as_ref()
                    .expect("type aliases have a type");
                let (typ_gap, typ_doc) = self.format_typ(&typ.node, typ.span.end);
                let semi = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::Semi)),
                    style,
                );
                alloc.concat([
                    gap_none(alloc, keyword_gap, style),
                    alloc.text("type"),
                    gap_space(alloc, name_gap, style),
                    alloc.as_string(&decl.node.sig.name.node),
                    gap_space(alloc, eq_gap, style),
                    alloc.text("="),
                    gap_space(alloc, typ_gap, style),
                    typ_doc,
                    semi,
                    alloc.text(";"),
                ])
            }
        }
    }

    fn format_sig(&mut self, sig: &Sig<Size>, end: usize) -> (TriviaGap, Doc<'doc>, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let name_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::Id(_)));
        let typevars = self.format_typevars(&sig.typevars.node, end);
        let arg_open_comments = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LParen)),
            style,
        );

        let mut list = DelimList::new(alloc, style, ",", true);
        let args_len = sig.args.node.0.len();
        for (index, arg) in sig.args.node.0.iter().enumerate() {
            let (arg_gap, arg_doc) = self.format_arg(arg);
            if index + 1 < args_len {
                let (before, after) = take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
                list.push_sep(arg_gap, arg_doc, before, after);
            } else {
                list.push(arg_gap, arg_doc);
            }
        }

        // Advance to `)`. If a trailing comma exists, it's a non-trivia token
        // that advance_to_token skips — comments around it become close_comments,
        // rendered after finish_ungrouped's trailing comma. Same as all other DelimList users.
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RParen));

        // Use finish_ungrouped so the caller can wrap (args) + ret in a single
        // group, ensuring args and ret break together (args break first, ret
        // stays on the same line as `)`).
        let args = list.finish_ungrouped("(", ")", close_comments);

        let name_typevars =
            alloc.concat([alloc.as_string(&sig.name.node), typevars, arg_open_comments]);

        (name_gap, name_typevars, args)
    }

    fn format_arg(&mut self, arg: &Spanned<Arg<Tid, Size>>) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let end = arg.span.end;
        let mut parts = Vec::new();
        let mut has_prefix = false;
        let mut leading_gap = TriviaGap::default();

        if !matches!(arg.node.qualifier.node, Qualifier::Local) {
            let qualifier_gap =
                self.cursor
                    .advance_to_token(end, |token| match arg.node.qualifier.node {
                        Qualifier::Witness => matches!(token, Token::KwWitness),
                        Qualifier::Extra => matches!(token, Token::KwExtra),
                        Qualifier::Instance => matches!(token, Token::KwInstance),
                        Qualifier::Local => false,
                    });
            leading_gap = qualifier_gap;
            parts.push(alloc.text(qualifier_text(arg.node.qualifier.node)));
            has_prefix = true;
        }

        let name_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::Id(_)));
        if has_prefix {
            parts.push(gap_space(alloc, name_gap, style));
        } else {
            leading_gap = name_gap;
        }
        parts.push(alloc.as_string(&arg.node.id));
        let colon_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::Colon));
        parts.push(gap_none(alloc, colon_gap, style));
        parts.push(alloc.text(":"));
        let (typ_gap, typ_doc) = self.format_typ(&arg.node.typ, end);
        parts.push(gap_space(alloc, typ_gap, style));
        parts.push(typ_doc);
        (leading_gap, alloc.concat(parts))
    }
}

fn qualifier_text(qualifier: Qualifier) -> &'static str {
    match qualifier {
        Qualifier::Witness => "witness",
        Qualifier::Local => "local",
        Qualifier::Extra => "extra",
        Qualifier::Instance => "instance",
    }
}
