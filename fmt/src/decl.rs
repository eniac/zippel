//! Declaration formatting.

use lang::ast::arg::Arg;
use lang::ast::decl::{Body, Decl};
use lang::ast::sig::Sig;
use lang::ast::{Size, Spanned};
use lang::id::Tid;
use lang::parser::Token;
use lang::typ::{Distribution, Qualifier};
use share::DocAllocator;

use crate::ctx::{ALLOC, Doc, hardlines};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::exp::{format_body, format_relation};
use crate::style::Style;
use crate::trivia::{
    TokenCursor, TriviaElement, TriviaGap, format_gap, gap_hard, gap_none, gap_space,
};
use crate::typ::{format_typ, format_typevars};

pub fn format_decls(decls: &[Spanned<Decl<Size>>], src: &str, style: &Style) -> String {
    let src_len = src.len();
    let mut cursor = TokenCursor::new(src);
    let mut parts = Vec::new();

    for (index, decl) in decls.iter().enumerate() {
        let gap = cursor.advance_to(decl.span.start);
        if index > 0 {
            if gap.is_empty() {
                parts.push(hardlines(1 + style.max_blank_lines.min(1)));
            } else if matches!(gap.first(), Some(TriviaElement::BlankLines(_)))
                || matches!(gap.last(), Some(TriviaElement::BlankLines(_)))
            {
                // Gap contains blank lines — they carry the separation.
                parts.push(gap_none(gap, style));
            } else {
                // Gap is all comments, no blank lines — force one blank
                // line after the comment. `gap_hard` provides the
                // hardline after the comment; add an extra hardline for
                // the blank line.
                parts.push(gap_hard(gap, style));
                parts.push(hardlines(style.max_blank_lines.min(1)));
            }
        } else {
            // First decl — gap before it is the file header. `nil` open:
            // nothing precedes the comment, so no space/hardline needed.
            parts.push(format_gap(gap, Some(ALLOC.nil()), None, None, style));
        }
        parts.push(format_decl(decl, &mut cursor, style));
    }

    if !decls.is_empty() {
        // Trailing gap after last decl — `sep = hardline` provides the
        // structural break; auto open/end handle comments.
        let trailing = cursor.advance_to(src_len);
        parts.push(format_gap(
            trailing,
            None,
            None,
            Some(ALLOC.hardline()),
            style,
        ));
    } else {
        // No decls — entire file is comments. `nil` open: nothing
        // precedes the first comment.
        parts.push(format_gap(
            cursor.advance_to(src_len),
            Some(ALLOC.nil()),
            None,
            None,
            style,
        ));
    }

    let mut output = String::new();
    ALLOC
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

fn format_decl(
    decl: &Spanned<Decl<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let end = decl.span.end;
    match &decl.node.body {
        Body::Proto { relation, body } => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwProto));
            let (sig_gap, name_typevars, args) = format_sig(&decl.node.sig, cursor, end, style);
            let where_gap = cursor
                .advance_to_token(end, |token| matches!(token, Token::KwWhere))
                .trim_start();

            // When comments are present between `)` and `where`, use
            // `format_gap` with `open = hardline()` so the comment starts
            // on a new line (not glued to `)`), and `where` follows on
            // its own line without a leading space.
            let has_where_comments = where_gap.has_comments();
            let where_comments = if has_where_comments {
                format_gap(
                    where_gap,
                    Some(ALLOC.hardline()),
                    Some(ALLOC.hardline()),
                    None,
                    style,
                )
            } else {
                gap_space(where_gap, style)
            };

            let relation = format_relation(relation, cursor, style);

            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));

            // Comments before `{` go inside the where group's nest so they
            // align with the relation body, not at column 0. Same pattern
            // as relation_leading above.
            let open = match open_gap.first() {
                Some(e) if !e.needs_start_newline() => Some(ALLOC.line()),
                _ => None,
            };
            let open_comments = format_gap(open_gap, open, None, Some(ALLOC.line()), style);

            let body = format_body(body.as_ref(), cursor, end, style);

            ALLOC.concat([
                gap_none(keyword_gap, style),
                ALLOC.text("proto"),
                gap_space(sig_gap, style),
                name_typevars,
                // Group args so they break as a unit. The `where` clause is
                // separate and should not force args to break.
                args.group(),
                where_comments,
                ALLOC
                    .concat([
                        ALLOC.text("where"),
                        ALLOC.concat([relation]).nest(style.indent_width() as isize),
                        open_comments.nest(style.indent_width() as isize),
                    ])
                    .group(),
                ALLOC.text("{"),
                body.nest(style.indent_width() as isize),
                ALLOC.text("}"),
            ])
        }
        Body::Func { body } => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFn));
            let (sig_gap, name_typevars, args) = format_sig(&decl.node.sig, cursor, end, style);
            let ret = if let Some(ret) = &decl.node.sig.ret {
                // Gap after `)` — strip blank lines (structural position).
                let arrow_gap = cursor
                    .advance_to_token(end, |token| matches!(token, Token::Arrow))
                    .trim_start();
                let (ret_gap, ret_doc) = format_typ(&ret.node, cursor, ret.span.end, style);
                ALLOC.concat([
                    gap_space(arrow_gap, style),
                    ALLOC.text("->"),
                    gap_space(ret_gap, style),
                    ret_doc,
                ])
            } else {
                ALLOC.nil()
            };
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));

            // Gap before `{` — strip blank lines on both ends (rustfmt
            // behavior: `{` stays on the same line as the signature, blank
            // lines are noise). Comments are preserved.
            let open_comments = gap_space(open_gap.trim(), style);

            // Group args + ret so they break together: when the group
            // breaks, args go on separate lines (via line_() in the
            // ungrouped DelimList) and ret stays on the same line as `)`.
            // Typevars are outside this group — they break independently
            // via their own inner group.
            let args_ret = ALLOC.concat([args, ret]).group();

            let body = format_body(body.as_ref(), cursor, end, style);

            ALLOC.concat([
                gap_none(keyword_gap, style),
                ALLOC.text("fn"),
                gap_space(sig_gap, style),
                name_typevars,
                args_ret,
                open_comments,
                ALLOC.text("{"),
                body.nest(style.indent_width() as isize),
                ALLOC.text("}"),
            ])
        }
        Body::TypeAlias => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwType));
            let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let eq_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Eq));
            let typ = decl
                .node
                .sig
                .ret
                .as_ref()
                .expect("type aliases have a type");
            let (typ_gap, typ_doc) = format_typ(&typ.node, cursor, typ.span.end, style);
            let semi = gap_none(
                cursor.advance_to_token(end, |token| matches!(token, Token::Semi)),
                style,
            );
            ALLOC.concat([
                gap_none(keyword_gap, style),
                ALLOC.text("type"),
                gap_space(name_gap, style),
                ALLOC.text(decl.node.sig.name.node.to_string()),
                gap_space(eq_gap, style),
                ALLOC.text("="),
                gap_space(typ_gap, style),
                typ_doc,
                semi,
                ALLOC.text(";"),
            ])
        }
    }
}

fn format_sig(
    sig: &Sig<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>, Doc<'static>) {
    let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let typevars = format_typevars(&sig.typevars.node, cursor, end, style);
    let arg_open_comments = gap_none(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );

    let mut list = DelimList::new(style, ",", true);
    let args_len = sig.args.node.0.len();
    for (index, arg) in sig.args.node.0.iter().enumerate() {
        let (arg_gap, arg_doc) = format_arg(arg, cursor, style);
        if index + 1 < args_len {
            let (before, after) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            list.push_sep(arg_gap, arg_doc, before, after);
        } else {
            list.push(arg_gap, arg_doc);
        }
    }

    // Advance to `)`. If a trailing comma exists, it's a non-trivia token
    // that advance_to_token skips — comments around it become close_comments,
    // rendered after finish_ungrouped's trailing comma. Same as all other DelimList users.
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));

    // Use finish_ungrouped so the caller can wrap (args) + ret in a single
    // group, ensuring args and ret break together (args break first, ret
    // stays on the same line as `)`).
    let args = list.finish_ungrouped("(", ")", close_comments);

    let name_typevars = ALLOC.concat([
        ALLOC.text(sig.name.node.to_string()),
        typevars,
        arg_open_comments,
    ]);

    (name_gap, name_typevars, args)
}

fn format_arg(
    arg: &Spanned<Arg<Tid, Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let end = arg.span.end;
    let mut parts = Vec::new();
    let mut has_prefix = false;
    let mut leading_gap = TriviaGap::default();

    if !matches!(arg.node.qualifier, Qualifier::Local) {
        let qualifier_gap = cursor.advance_to_token(end, |token| match arg.node.qualifier {
            Qualifier::Witness => matches!(token, Token::KwWitness),
            Qualifier::Extra => matches!(token, Token::KwExtra),
            Qualifier::Instance => matches!(token, Token::KwInstance),
            Qualifier::Local => false,
        });
        leading_gap = qualifier_gap;
        parts.push(ALLOC.text(qualifier_text(arg.node.qualifier)));
        has_prefix = true;
    }

    if !matches!(arg.node.distribution, Distribution::Nonuniform) {
        let uniform_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwUniform));
        if has_prefix {
            parts.push(gap_space(uniform_gap, style));
        } else {
            leading_gap = uniform_gap;
        }
        parts.push(ALLOC.text("uniform"));
        if matches!(arg.node.distribution, Distribution::UniformNonZero) {
            let star_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Star));
            parts.push(gap_space(star_gap, style));
            parts.push(ALLOC.text("*"));
        }
        has_prefix = true;
    }

    let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    if has_prefix {
        parts.push(gap_space(name_gap, style));
    } else {
        leading_gap = name_gap;
    }
    parts.push(ALLOC.text(arg.node.id.to_string()));
    let colon_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Colon));
    parts.push(gap_none(colon_gap, style));
    parts.push(ALLOC.text(":"));
    let (typ_gap, typ_doc) = format_typ(&arg.node.typ, cursor, end, style);
    parts.push(gap_space(typ_gap, style));
    parts.push(typ_doc);
    (leading_gap, ALLOC.concat(parts))
}

fn qualifier_text(qualifier: Qualifier) -> &'static str {
    match qualifier {
        Qualifier::Witness => "witness",
        Qualifier::Local => "local",
        Qualifier::Extra => "extra",
        Qualifier::Instance => "instance",
    }
}
