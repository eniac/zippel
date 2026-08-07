//! Wadler doc builders for the Zippel AST.

use lang::ast::arg::Arg;
use lang::ast::decl::{Body, Decl};
use lang::ast::exp::{BinOp, Exp, Exps};
use lang::ast::sig::Sig;
use lang::ast::{Range, Size, Spanned};
use lang::id::Tid;
use lang::parser::Token;
use lang::typ::{Distribution, GTyp, Kind, Qualifier, Typ, TypeVar, TypeVars};
use share::{BoxAllocator, DocAllocator, DocBuilder};

use crate::paren::{lhs_needs_paren, rhs_needs_paren};
use crate::style::Style;
use crate::trivia::{
    Comment, TokenCursor, TokenStream, TriviaElement, TriviaGap, format_gap, gap_hard, gap_list,
    gap_none, gap_semi, gap_space, trim_if_clean,
};

const ALLOC: BoxAllocator = BoxAllocator;
type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

pub fn format_decls(
    decls: &[Spanned<Decl<Size>>],
    tokens: &TokenStream,
    comments: &[Comment],
    src_len: usize,
    style: &Style,
) -> String {
    let mut cursor = TokenCursor::new(tokens, comments);
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
            parts.push(gap_list(gap, style));
        }
        parts.push(format_decl(decl, &mut cursor, style));
    }

    if !decls.is_empty() {
        // Trailing gap after last decl — `sep = hardline` provides the
        // structural break; auto open/end handle comments.
        let trailing = cursor.advance_to(src_len);
        let open = match trailing.first() {
            Some(TriviaElement::Comment(c)) if c.at_line_start => Some(ALLOC.hardline()),
            Some(TriviaElement::Comment(_)) => Some(ALLOC.text(" ")),
            _ => None,
        };
        parts.push(format_gap(
            trailing,
            open,
            None,
            Some(ALLOC.hardline()),
            style,
        ));
    } else {
        parts.push(gap_list(cursor.advance_to(src_len), style));
    }

    let mut output = String::new();
    ALLOC
        .concat(parts)
        .1
        .render_fmt(style.width, &mut output)
        .expect("rendering failed");
    let mut canonical = output
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    canonical.truncate(canonical.trim_end_matches('\n').len());
    canonical.push('\n');
    canonical
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
            let (sig_gap, sig) = format_sig(&decl.node.sig, cursor, end, style);
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
                gap_space(trim_if_clean(where_gap), style)
            };

            // Gap after `where` — strip blank lines (structural hardline follows).
            // Use `line()` as open for inline comments (space in flat, newline
            // in broken) and `line()` as sep for empty gaps. At_line_start
            // comments get auto `hardline` open.
            let relation_leading_gap = cursor.advance_to(relation.span.start).trim_start();
            let relation_open = match relation_leading_gap.first() {
                Some(TriviaElement::Comment(c)) if c.at_line_start => None,
                Some(TriviaElement::Comment(_)) => Some(ALLOC.line()),
                _ => None,
            };
            let relation_leading = format_gap(
                relation_leading_gap,
                relation_open,
                None,
                Some(ALLOC.line()),
                style,
            );
            let relation = format_relation(relation, cursor, style);

            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));

            // Comments before `{` go inside the where group's nest so they
            // align with the relation body, not at column 0. Same pattern
            // as relation_leading above.
            let open = match open_gap.first() {
                Some(TriviaElement::Comment(c)) if c.at_line_start => None,
                Some(TriviaElement::Comment(_)) => Some(ALLOC.line()),
                _ => None,
            };
            let open_comments = format_gap(open_gap, open, None, Some(ALLOC.line()), style);

            // Gap after `{` — strip blank lines. `sep = hardline` provides
            // the structural break for empty gaps; `open = hardline` puts
            // comments on their own line; `end = hardline` breaks after.
            let body_leading = format_gap(
                cursor.advance_to(body.span.start).trim_start(),
                Some(ALLOC.hardline()),
                Some(ALLOC.hardline()),
                Some(ALLOC.hardline()),
                style,
            );
            let body = format_body_exp(body, cursor, style);

            // Gap before `}` — strip blank lines (structural hardline precedes).
            let close_comments = cursor
                .advance_to_token(end, |token| matches!(token, Token::RBrace))
                .trim_end();

            ALLOC.concat([
                gap_none(trim_if_clean(keyword_gap), style),
                ALLOC.text("proto"),
                gap_space(trim_if_clean(sig_gap), style),
                sig,
                where_comments,
                ALLOC
                    .concat([
                        ALLOC.text("where"),
                        ALLOC
                            .concat([relation_leading, relation])
                            .nest(style.indent_width() as isize),
                        open_comments.nest(style.indent_width() as isize),
                    ])
                    .group(),
                ALLOC.text("{"),
                ALLOC
                    .concat([body_leading, body, gap_hard(close_comments, style)])
                    .nest(style.indent_width() as isize),
                ALLOC.text("}"),
            ])
        }
        Body::Func { body } => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFn));
            let (sig_gap, sig) = format_sig(&decl.node.sig, cursor, end, style);
            let ret = if let Some(ret) = &decl.node.sig.ret {
                // Gap after `)` — strip blank lines (structural position).
                let arrow_gap = cursor
                    .advance_to_token(end, |token| matches!(token, Token::Arrow))
                    .trim_start();
                let (ret_gap, ret_doc) = format_typ(&ret.node, cursor, ret.span.end, style);
                ALLOC.concat([
                    gap_space(trim_if_clean(arrow_gap), style),
                    ALLOC.text("->"),
                    gap_space(trim_if_clean(ret_gap), style),
                    ret_doc,
                ])
            } else {
                ALLOC.nil()
            };
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));

            // Gap before `{` — strip leading blank lines (rustfmt behavior:
            // `{` stays on the same line as the signature, blank lines are
            // noise). Comments are preserved.
            let open_comments = gap_space(open_gap.trim_start(), style);

            // Gap after `{` — strip blank lines. `sep = hardline` provides
            // the structural break for empty gaps; `open = hardline` puts
            // comments on their own line; `end = hardline` breaks after.
            let body_leading = format_gap(
                cursor.advance_to(body.span.start).trim_start(),
                Some(ALLOC.hardline()),
                Some(ALLOC.hardline()),
                Some(ALLOC.hardline()),
                style,
            );
            let body = format_body_exp(body, cursor, style);

            // Gap before `}` — strip blank lines (structural hardline precedes).
            let close_comments = cursor
                .advance_to_token(end, |token| matches!(token, Token::RBrace))
                .trim_end();

            ALLOC.concat([
                gap_none(trim_if_clean(keyword_gap), style),
                ALLOC.text("fn"),
                gap_space(trim_if_clean(sig_gap), style),
                sig,
                ret,
                open_comments,
                ALLOC.text("{"),
                ALLOC
                    .concat([body_leading, body, gap_hard(close_comments, style)])
                    .nest(style.indent_width() as isize),
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
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Semi))),
                style,
            );
            ALLOC.concat([
                gap_none(trim_if_clean(keyword_gap), style),
                ALLOC.text("type"),
                gap_space(trim_if_clean(name_gap), style),
                ALLOC.text(decl.node.sig.name.node.to_string()),
                gap_space(trim_if_clean(eq_gap), style),
                ALLOC.text("="),
                gap_space(trim_if_clean(typ_gap), style),
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
) -> (TriviaGap, Doc<'static>) {
    let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let typevars = format_typevars(&sig.typevars.node, cursor, end, style);
    let arg_open_comments = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );

    let mut list = DelimList::new(style);
    // Find the `)` position to limit trailing comma search for the last arg.
    let rparen_end = cursor.peek_token(end, |token| matches!(token, Token::RParen));
    for (index, arg) in sig.args.node.0.iter().enumerate() {
        let (arg_gap, arg_doc) = format_arg(arg, cursor, style);
        if index + 1 < sig.args.node.0.len() {
            list.push_comma(
                arg_gap,
                arg_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
            );
        } else {
            // Last arg: consume trailing comma comments only if a comma exists before `)`.
            if let Some(rp_end) = &rparen_end {
                let comma_comments = gap_none(
                    trim_if_clean(
                        cursor.advance_to_token(rp_end.end, |token| matches!(token, Token::Comma)),
                    ),
                    style,
                );
                list.push(arg_gap, ALLOC.concat([arg_doc, comma_comments]));
            } else {
                list.push(arg_gap, arg_doc);
            }
        }
    }
    let arg_close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let args = list.finish("(", ")", arg_close_comments);

    (
        name_gap,
        ALLOC.concat([
            ALLOC.text(sig.name.node.to_string()),
            typevars,
            arg_open_comments,
            args,
        ]),
    )
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
            parts.push(gap_space(trim_if_clean(uniform_gap), style));
        } else {
            leading_gap = uniform_gap;
        }
        parts.push(ALLOC.text("uniform"));
        if matches!(arg.node.distribution, Distribution::UniformNonZero) {
            let star_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Star));
            parts.push(gap_space(trim_if_clean(star_gap), style));
            parts.push(ALLOC.text("*"));
        }
        has_prefix = true;
    }

    let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    if has_prefix {
        parts.push(gap_space(trim_if_clean(name_gap), style));
    } else {
        leading_gap = name_gap;
    }
    parts.push(ALLOC.text(arg.node.id.to_string()));
    let colon_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Colon));
    parts.push(gap_none(trim_if_clean(colon_gap), style));
    parts.push(ALLOC.text(":"));
    let (typ_gap, typ_doc) = format_typ(&arg.node.typ, cursor, end, style);
    parts.push(gap_space(trim_if_clean(typ_gap), style));
    parts.push(typ_doc);
    (leading_gap, ALLOC.concat(parts))
}

fn format_typevars(
    typevars: &TypeVars<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let open_comments = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
        style,
    );
    let mut list = DelimList::new(style);
    for (index, typevar) in typevars.0.iter().enumerate() {
        let (typevar_gap, typevar_doc) = format_typevar(typevar, cursor, style);
        if index + 1 < typevars.0.len() {
            list.push_comma(
                typevar_gap,
                typevar_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
            );
        } else {
            list.push(typevar_gap, typevar_doc);
        }
    }
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
    ALLOC.concat([open_comments, list.finish("<", ">", close_comments)])
}

fn format_typevar(
    typevar: &Spanned<TypeVar<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let end = typevar.span.end;
    let id_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let colon = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Colon))),
        style,
    );
    let (kind_gap, kind_doc) = format_kind(&typevar.node.kind, cursor, end, style);
    let doc = ALLOC.concat([
        ALLOC.text(typevar.node.id.to_string()),
        colon,
        ALLOC.text(":"),
        gap_space(trim_if_clean(kind_gap), style),
        kind_doc,
    ]);
    (id_gap, doc)
}

fn format_typ(
    typ: &GTyp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    match typ {
        Typ::Poly(base, m, n) => {
            let keyword_gap = cursor.advance_to_token(end, |token| {
                matches!(token, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
            });
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
                style,
            );
            let base_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            // Consume all inner gaps and format sizes up-front so we can
            // decide whether to use Uni/Mle sugar without losing comments.
            let comma_one = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let (m_gap, m_doc) = format_size(m, cursor, end, style);
            let comma_two = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let (n_gap, n_doc) = format_size(n, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));

            // Uni<F, N> is sugar for Poly<F, 1, N>; Mle<F, N> is sugar for
            // Poly<F, N, 1>. Emit the sugar only when the AST matches AND
            // no comments are attached to the skipped argument's gaps.
            let is_uni = matches!(m, Size::Lit(1))
                && !comma_one.has_comments()
                && !comma_two.has_comments()
                && !close_comments.has_comments();
            let is_mle = matches!(n, Size::Lit(1))
                && !comma_two.has_comments()
                && !close_comments.has_comments();

            let name = if is_uni {
                "Uni"
            } else if is_mle {
                "Mle"
            } else {
                "Poly"
            };

            let mut list = DelimList::new(style);
            list.push_comma(base_gap, ALLOC.text(base.to_string()), comma_one);
            if is_uni {
                list.push(n_gap, n_doc);
            } else if is_mle {
                list.push(m_gap, m_doc);
            } else {
                list.push_comma(m_gap, m_doc, comma_two);
                list.push(n_gap, n_doc);
            }

            (
                keyword_gap,
                ALLOC.concat([
                    ALLOC.text(name),
                    open,
                    list.finish("<", ">", close_comments),
                ]),
            )
        }
        Typ::Vec(typ, size) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let (inner_gap, inner_doc) = format_typ(&typ.node, cursor, typ.span.end, style);
            let semi = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Semi))),
                style,
            );
            let (size_gap, size_doc) = format_size(size, cursor, end, style);
            let close = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::RBrack))),
                style,
            );

            (
                open_gap,
                ALLOC.concat([
                    ALLOC.text("["),
                    gap_none(trim_if_clean(inner_gap), style),
                    inner_doc,
                    semi,
                    ALLOC.text(";"),
                    gap_space(trim_if_clean(size_gap), style),
                    size_doc,
                    close,
                    ALLOC.text("]"),
                ]),
            )
        }
        Typ::Base(base) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, ALLOC.text(base.to_string()))
        }
        Typ::Fin(range) => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFin));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
                style,
            );
            let (range_gap, range_doc) = format_range(range, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            let mut list = DelimList::new(style);
            list.push(range_gap, range_doc);
            (
                keyword_gap,
                ALLOC.concat([
                    ALLOC.text("Fin"),
                    open,
                    list.finish("<", ">", close_comments),
                ]),
            )
        }
        Typ::Unit => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwUnit));
            (gap, ALLOC.text("Unit"))
        }
        Typ::Record(fields) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, typ)| typ.span.start);
            let mut list = DelimList::new(style);
            format_field_items(
                &fields,
                |typ, cursor, end, style| format_typ(&typ.node, cursor, end, style),
                cursor,
                end,
                style,
                &mut list,
            );
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrace));
            (open_gap, list.finish("{", "}", close_comments))
        }
    }
}

fn format_kind(
    kind: &Kind<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    match kind {
        Kind::Field => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwField));
            (gap, ALLOC.text("Field"))
        }
        Kind::Group => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwGroup));
            (gap, ALLOC.text("Group"))
        }
        Kind::SizeVar => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwSize));
            (gap, ALLOC.text("Size"))
        }
        Kind::Scalar(ids) => {
            let keyword_gap =
                cursor.advance_to_token(end, |token| matches!(token, Token::KwScalar));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
                style,
            );
            let ids: Vec<_> = ids.iter().collect();
            let mut list = DelimList::new(style);
            for (index, id) in ids.iter().enumerate() {
                let id_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let id_doc = ALLOC.text(id.to_string());
                if index + 1 < ids.len() {
                    list.push_comma(
                        id_gap,
                        id_doc,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                    );
                } else {
                    list.push(id_gap, id_doc);
                }
            }
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            (
                keyword_gap,
                ALLOC.concat([
                    ALLOC.text("Scalar"),
                    open,
                    list.finish("<", ">", close_comments),
                ]),
            )
        }
        Kind::Pairing(g1, g2) => {
            let keyword_gap =
                cursor.advance_to_token(end, |token| matches!(token, Token::KwPairing));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
                style,
            );
            let first_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let second_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            let mut list = DelimList::new(style);
            list.push_comma(first_gap, ALLOC.text(g1.to_string()), comma);
            list.push(second_gap, ALLOC.text(g2.to_string()));
            let args = list.finish("<", ">", close_comments);
            (
                keyword_gap,
                ALLOC.concat([ALLOC.text("Pairing"), open, args]),
            )
        }
        Kind::Range(range) => format_range(range, cursor, end, style),
    }
}

fn format_size_spanned(
    size: &Spanned<Size>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    format_size(&size.node, cursor, size.span.end, style)
}

fn format_size(
    size: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    match size {
        Size::Var(id) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, ALLOC.text(id.to_string()))
        }
        Size::Lit(value) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_)));
            (gap, ALLOC.text(value.to_string()))
        }
        Size::Add(lhs, rhs) => format_size_binary(lhs, rhs, "+", cursor, end, style),
        Size::Sub(lhs, rhs) => format_size_binary(lhs, rhs, "-", cursor, end, style),
        Size::Mul(lhs, rhs) => format_size_binary(lhs, rhs, "*", cursor, end, style),
        Size::Div(lhs, rhs) => format_size_binary(lhs, rhs, "/", cursor, end, style),
        Size::Pow(lhs, rhs) => format_size_binary(lhs, rhs, "^", cursor, end, style),
        Size::Max(lhs, rhs) => format_size_call("max", lhs, rhs, cursor, end, style),
        Size::Min(lhs, rhs) => format_size_call("min", lhs, rhs, cursor, end, style),
    }
}

fn format_size_binary(
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    op: &'static str,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let (precedence, right_assoc) = match op {
        "+" | "-" => (1, false),
        "*" | "/" => (2, false),
        "^" => (3, true),
        _ => unreachable!(),
    };
    let (lhs_gap, lhs_doc) = format_size_spanned(lhs, cursor, style);
    let lhs = parenthesize(
        lhs_doc,
        size_lhs_needs_paren(&lhs.node, precedence, right_assoc),
    );
    let op_gap = cursor.advance_to_token(end, |token| matches_size_op(op, token));
    let (rhs_gap, rhs_doc) = format_size_spanned(rhs, cursor, style);
    let rhs = parenthesize(
        rhs_doc,
        size_rhs_needs_paren(&rhs.node, precedence, right_assoc),
    );

    let doc = ALLOC.concat([
        lhs,
        gap_space(trim_if_clean(op_gap), style),
        ALLOC.text(op),
        gap_space(trim_if_clean(rhs_gap), style),
        rhs,
    ]);
    (lhs_gap, doc)
}

fn format_size_call(
    name: &'static str,
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (lhs_gap, lhs_doc) = format_size_spanned(lhs, cursor, style);
    let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
    let (rhs_gap, rhs_doc) = format_size_spanned(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let mut list = DelimList::new(style);
    list.push_comma(lhs_gap, lhs_doc, comma);
    list.push(rhs_gap, rhs_doc);
    let args = list.finish("(", ")", close_comments);

    (name_gap, ALLOC.concat([ALLOC.text(name), open, args]))
}

fn format_range(
    range: &Range<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let (start_gap, start_doc) = format_range_size(&range.start, cursor, end, style);
    if let Some(step) = &range.step {
        let comma = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Comma))),
            style,
        );
        let (step_gap, step_doc) = format_range_size(step, cursor, end, style);
        let dots = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::DotDot))),
            style,
        );
        let last = range.end.as_ref().expect("stepped ranges have an end");
        let (last_gap, last_doc) = format_range_size(last, cursor, end, style);
        let doc = ALLOC.concat([
            start_doc,
            comma,
            ALLOC.text(","),
            gap_space(trim_if_clean(step_gap), style),
            step_doc,
            dots,
            ALLOC.text(".."),
            gap_none(trim_if_clean(last_gap), style),
            last_doc,
        ]);
        (start_gap, doc)
    } else if let Some(last) = &range.end {
        let dots = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::DotDot))),
            style,
        );
        let (last_gap, last_doc) = format_range_size(last, cursor, end, style);
        let doc = ALLOC.concat([
            start_doc,
            dots,
            ALLOC.text(".."),
            gap_none(trim_if_clean(last_gap), style),
            last_doc,
        ]);
        (start_gap, doc)
    } else {
        (start_gap, start_doc)
    }
}

fn format_range_size(
    size: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    if size.span.start == size.span.end {
        format_size(&size.node, cursor, end, style)
    } else {
        format_size_spanned(size, cursor, style)
    }
}

fn format_relation(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    match &exp.node {
        Exp::Assert(lhs, rhs) => {
            let (lhs_gap, lhs_doc) = format_exp(lhs, cursor, style);
            let eq_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::EqEq));
            let (rhs_gap, rhs_doc) = format_exp(rhs, cursor, style);
            ALLOC
                .concat([
                    ALLOC.concat([gap_none(trim_if_clean(lhs_gap), style), lhs_doc]),
                    gap_space(trim_if_clean(eq_gap), style),
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text("==")])
                        .flat_alt(ALLOC.text("==")),
                    gap_space(trim_if_clean(rhs_gap), style),
                    rhs_doc,
                ])
                .nest(style.indent_width() as isize)
                .group()
        }
        Exp::Let(Some(var), value, body) => {
            let keyword = gap_none(
                trim_if_clean(
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
                ),
                style,
            );
            let name_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq_gap = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let body = if let Some(body) = body.as_ref() {
                let semi_gap =
                    take_separator_gap(cursor, exp.span.end, |token| matches!(token, Token::Semi));
                ALLOC.concat([
                    gap_hard(semi_gap, style),
                    format_relation(body, cursor, style),
                ])
            } else {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                gap_semi(trim_if_clean(before_semi), style)
            };

            ALLOC.concat([
                keyword,
                ALLOC.text("let"),
                gap_space(trim_if_clean(name_gap), style),
                ALLOC.text(var.to_string()),
                gap_space(trim_if_clean(eq_gap), style),
                ALLOC.text("="),
                gap_space(trim_if_clean(value_gap), style),
                value_doc,
                ALLOC.text(";"),
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let value = format_relation(value, cursor, style);
            let body = if let Some(body) = body.as_ref() {
                let semi_gap =
                    take_separator_gap(cursor, exp.span.end, |token| matches!(token, Token::Semi));
                ALLOC.concat([
                    gap_hard(semi_gap, style),
                    format_relation(body, cursor, style),
                ])
            } else {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                gap_semi(trim_if_clean(before_semi), style)
            };

            ALLOC.concat([value, ALLOC.text(";"), body])
        }
        _ => {
            let (gap, doc) = format_exp(exp, cursor, style);
            ALLOC.concat([gap_none(trim_if_clean(gap), style), doc])
        }
    }
}

fn format_body_exp(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    match &exp.node {
        Exp::Let(Some(var), value, body) => {
            let keyword = gap_none(
                trim_if_clean(
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
                ),
                style,
            );
            let name_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq_gap = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                keyword,
                ALLOC.text("let"),
                gap_space(trim_if_clean(name_gap), style),
                ALLOC.text(var.to_string()),
                gap_space(trim_if_clean(eq_gap), style),
                ALLOC.text("="),
                gap_space(trim_if_clean(value_gap), style),
                value_doc,
                ALLOC.text(";"),
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                gap_none(trim_if_clean(value_gap), style),
                value_doc,
                ALLOC.text(";"),
                body,
            ])
        }
        Exp::Log(var, value, body) => {
            let name = gap_none(
                trim_if_clean(
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
                ),
                style,
            );
            let arrow_gap =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::LArrow));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                name,
                ALLOC.text(var.to_string()),
                gap_space(trim_if_clean(arrow_gap), style),
                ALLOC.text("<-"),
                gap_space(trim_if_clean(value_gap), style),
                value_doc,
                ALLOC.text(";"),
                body,
            ])
        }
        _ => {
            let (gap, doc) = format_exp(exp, cursor, style);
            ALLOC.concat([gap_none(trim_if_clean(gap), style), doc])
        }
    }
}

fn format_body_tail(
    before_semi: TriviaGap,
    body: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let Some(body) = body else {
        return gap_semi(trim_if_clean(before_semi), style);
    };

    let after_semi = cursor.advance_to(body.span.start);
    let gap = before_semi.join(after_semi);
    ALLOC.concat([gap_hard(gap, style), format_body_exp(body, cursor, style)])
}

fn hardlines(count: usize) -> Doc<'static> {
    ALLOC.concat((0..count).map(|_| ALLOC.hardline()))
}

fn format_exp(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let end = exp.span.end;
    match &exp.node {
        Exp::Lit(value) => format_size(value, cursor, end, style),
        Exp::Unit => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let list = DelimList::new(style);
            (gap, list.finish("(", ")", close_comments))
        }
        Exp::Var(var) => {
            let gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            (gap, ALLOC.text(var.to_string()))
        }
        Exp::Neg(inner) => {
            let minus_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Minus));
            let (inner_gap, inner_doc) = format_exp(inner, cursor, style);
            let inner = parenthesize(inner_doc, neg_needs_paren(&inner.node));
            (
                minus_gap,
                ALLOC.concat([
                    ALLOC.text("-"),
                    gap_none(trim_if_clean(inner_gap), style),
                    inner.group(),
                ]),
            )
        }
        Exp::Bin(BinOp::Dot, lhs, rhs) => format_binary_call("dot", lhs, rhs, cursor, end, style),
        Exp::Bin(op, lhs, rhs) => {
            // Flatten left-associative same-operator chain:
            //   a * b * c  =  Bin(*, Bin(*, a, b), c)  →  [a, b, c]
            // so all operators align at the same indent instead of nesting
            // deeper for each left-recursion level.
            let mut inner_rhs_list: Vec<&Spanned<Exp<Size>>> = Vec::new();
            let mut current: &Spanned<Exp<Size>> = lhs;
            while let Exp::Bin(inner_op, inner_lhs, inner_rhs) = &current.node {
                if inner_op == op {
                    inner_rhs_list.push(inner_rhs);
                    current = inner_lhs;
                } else {
                    break;
                }
            }
            inner_rhs_list.reverse();
            let mut chain: Vec<&Spanned<Exp<Size>>> = Vec::new();
            chain.push(current);
            chain.extend(inner_rhs_list);
            chain.push(rhs);

            let indent = style.indent_width() as isize;
            let mut parts = Vec::with_capacity(chain.len() * 3);

            // First operand — no operator before it.
            let (first_gap, first_doc) = format_exp(chain[0], cursor, style);
            let first = parenthesize(first_doc, lhs_needs_paren(*op, &chain[0].node));
            parts.push(ALLOC.concat([gap_none(trim_if_clean(first_gap), style), first]));

            // Remaining operands — each preceded by `op`.
            for operand in &chain[1..] {
                let op_gap = cursor.advance_to_token(end, |token| matches_binop(*op, token));
                let (operand_gap, operand_doc) = format_exp(operand, cursor, style);
                let operand = parenthesize(operand_doc, rhs_needs_paren(*op, &operand.node));
                parts.push(gap_space(trim_if_clean(op_gap), style));
                parts.push(
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text(binop_symbol(*op))])
                        .flat_alt(ALLOC.text(binop_text(*op))),
                );
                parts.push(ALLOC.concat([gap_space(trim_if_clean(operand_gap), style), operand]));
            }

            (
                TriviaGap::default(),
                ALLOC.concat(parts).nest(indent).group(),
            )
        }
        Exp::App(function, args) => {
            let function_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
                style,
            );
            let mut list = DelimList::new(style);
            format_exps_items(args, cursor, end, style, &mut list);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let args = list.finish("(", ")", close_comments);

            (
                function_gap,
                ALLOC.concat([ALLOC.text(function.to_string()), open, args]),
            )
        }
        Exp::Interpolate(None, evals) => format_unary_call(
            "interpolate",
            |token| matches!(token, Token::KwInterpolate),
            evals,
            cursor,
            end,
            style,
        ),
        Exp::Interpolate(Some(points), evals) => {
            format_binary_call("interpolate", points, evals, cursor, end, style)
        }
        Exp::Poly(value) => format_unary_call(
            "poly",
            |token| matches!(token, Token::KwPoly),
            value,
            cursor,
            end,
            style,
        ),
        Exp::Coef(value) => format_unary_call(
            "coef",
            |token| matches!(token, Token::KwCoef),
            value,
            cursor,
            end,
            style,
        ),
        Exp::Mle(value) => format_unary_call(
            "mle",
            |token| matches!(token, Token::KwMle),
            value,
            cursor,
            end,
            style,
        ),
        Exp::Evaluate(poly, range, point) => {
            format_evaluate(poly, range.as_ref(), point.as_deref(), cursor, end, style)
        }
        Exp::Vec(values) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let mut list = DelimList::new(style);
            format_exps_items(values, cursor, end, style, &mut list);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            (open_gap, list.finish("[", "]", close_comments))
        }
        Exp::Range(range) => format_range(range, cursor, end, style),
        Exp::Map(body, var, range) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let (body_gap, body_doc) = format_exp(body, cursor, style);
            let for_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFor));
            let var_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let in_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwIn));
            let (range_gap, range_doc) = format_exp(range, cursor, style);
            let close = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::RBrack))),
                style,
            );

            (
                open_gap,
                ALLOC.concat([
                    ALLOC.text("["),
                    ALLOC
                        .concat([
                            ALLOC.line_(),
                            ALLOC
                                .concat([gap_none(trim_if_clean(body_gap), style), body_doc])
                                .group(),
                            gap_space(trim_if_clean(for_gap), style),
                            ALLOC.line().flat_alt(ALLOC.nil()),
                            ALLOC
                                .concat([
                                    ALLOC.text("for"),
                                    gap_space(trim_if_clean(var_gap), style),
                                    ALLOC.text(var.to_string()),
                                    gap_space(trim_if_clean(in_gap), style),
                                    ALLOC.text("in"),
                                    gap_space(trim_if_clean(range_gap), style),
                                    range_doc,
                                ])
                                .group(),
                            ALLOC.line_(),
                        ])
                        .nest(style.indent_width() as isize)
                        .group(),
                    close,
                    ALLOC.text("]"),
                ]),
            )
        }
        Exp::Reduce(op, value) => {
            let keyword_gap =
                cursor.advance_to_token(end, |token| matches!(token, Token::KwReduce));
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
                style,
            );
            let op_gap = cursor.advance_to_token(end, |token| matches_binop(*op, token));
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let mut list = DelimList::new(style);
            list.push_comma(op_gap, ALLOC.text(binop_symbol(*op)), comma);
            list.push(value_gap, value_doc);
            let args = list.finish("(", ")", close_comments);

            (
                keyword_gap,
                ALLOC.concat([ALLOC.text("reduce"), open, args]),
            )
        }
        Exp::Ram(base, index) => {
            let (base_gap, base_doc) = format_exp(base, cursor, style);
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LBrack))),
                style,
            );
            let (index_gap, index_doc) = format_exp(index, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            let mut list = DelimList::new(style);
            list.push(index_gap, index_doc);
            (
                base_gap,
                ALLOC.concat([
                    base_doc.group(),
                    open,
                    list.finish("[", "]", close_comments),
                ]),
            )
        }
        Exp::Pair(lhs, rhs) => format_binary_call("pair", lhs, rhs, cursor, end, style),
        Exp::Random(typ, star) => {
            format_sampling("random", Token::KwRandom, typ, *star, cursor, end, style)
        }
        Exp::Challenge(typ, star) => format_sampling(
            "challenge",
            Token::KwChallenge,
            typ,
            *star,
            cursor,
            end,
            style,
        ),
        Exp::Let(_, _, _) | Exp::Log(_, _, _) => {
            let doc = format_body_exp(exp, cursor, style);
            (TriviaGap::default(), doc)
        }
        Exp::Assert(lhs, rhs) => {
            format_assertion("assert", Token::KwAssert, lhs, rhs, cursor, end, style)
        }
        Exp::Verify(lhs, rhs) => {
            format_assertion("verify", Token::KwVerify, lhs, rhs, cursor, end, style)
        }
        Exp::Fun(vars, body) => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFun));
            let mut items = Vec::new();
            let first_var_gap = if vars.is_empty() {
                TriviaGap::default()
            } else {
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)))
            };
            for (index, var) in vars.iter().enumerate() {
                let var_comments = if index == 0 {
                    ALLOC.nil()
                } else {
                    gap_none(
                        trim_if_clean(
                            cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                        ),
                        style,
                    )
                };
                let var_doc = ALLOC.concat([var_comments, ALLOC.text(var.to_string())]);
                if index + 1 < vars.len() {
                    items.push(comma_terminated_item(
                        var_doc,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                        style,
                    ));
                } else {
                    items.push(var_doc);
                }
            }
            let arrow_gap = cursor.advance_to_token(end, |token| matches!(token, Token::FatArrow));
            let (body_gap, body_doc) = format_exp(body, cursor, style);

            (
                keyword_gap,
                ALLOC.concat([
                    ALLOC.text("fun"),
                    gap_space(trim_if_clean(first_var_gap), style),
                    ALLOC.concat(items),
                    gap_space(trim_if_clean(arrow_gap), style),
                    ALLOC.text("=>"),
                    gap_space(trim_if_clean(body_gap), style),
                    body_doc.group(),
                ]),
            )
        }
        Exp::Record(fields) => {
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBraceBar));
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, value)| value.span.start);
            let mut list = DelimList::new(style);
            format_field_items(
                &fields,
                |exp, cursor, _end, style| format_exp(exp, cursor, style),
                cursor,
                end,
                style,
                &mut list,
            );
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::BarRBrace));
            (open_gap, list.finish("{|", "|}", close_comments))
        }
        Exp::Proj(base, field) => {
            let (base_gap, base_doc) = format_exp(base, cursor, style);
            let dot = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Dot))),
                style,
            );
            let field_comments = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)))),
                style,
            );
            (
                base_gap,
                ALLOC.concat([
                    base_doc.group(),
                    dot,
                    ALLOC.text("."),
                    field_comments,
                    ALLOC.text(field.to_string()),
                ]),
            )
        }
        Exp::SetRecord(record, field, value) => {
            let (record_gap, record_doc) = format_exp(record, cursor, style);
            let dot = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Dot))),
                style,
            );
            let set = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)))),
                style,
            );
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
                style,
            );
            let field_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let (value_gap, value_doc) = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let mut list = DelimList::new(style);
            list.push_comma(field_gap, ALLOC.text(field.to_string()), comma);
            list.push(value_gap, value_doc);

            (
                record_gap,
                ALLOC.concat([
                    record_doc.group(),
                    dot,
                    ALLOC.text("."),
                    set,
                    ALLOC.text("set"),
                    open,
                    list.finish("(", ")", close_comments),
                ]),
            )
        }
    }
}

fn format_unary_call(
    name: &'static str,
    pred: impl Fn(&Token) -> bool,
    arg: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, pred);
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (arg_gap, arg_doc) = format_exp(arg, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let mut list = DelimList::new(style);
    list.push(arg_gap, arg_doc);

    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

fn format_binary_call(
    name: &'static str,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| {
        matches!(
            token,
            Token::Id(_) | Token::KwInterpolate | Token::KwPair | Token::KwDot
        )
    });
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (lhs_gap, lhs_doc) = format_exp(lhs, cursor, style);
    let comma_comments = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
    let (rhs_gap, rhs_doc) = format_exp(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let mut list = DelimList::new(style);
    list.push_comma(lhs_gap, lhs_doc, comma_comments);
    list.push(rhs_gap, rhs_doc);

    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

fn format_evaluate(
    poly: &Spanned<Exp<Size>>,
    range: Option<&Range<Size>>,
    point: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwEval));
    let selector = if let Some(range) = range {
        let open = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
            style,
        );
        let (range_gap, range_doc) = format_range(range, cursor, end, style);
        let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
        let mut list = DelimList::new(style);
        list.push(range_gap, range_doc);
        ALLOC.concat([open, list.finish("<", ">", close_comments)])
    } else {
        ALLOC.nil()
    };

    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (poly_gap, poly_doc) = format_exp(poly, cursor, style);

    let mut list = DelimList::new(style);
    if let Some(point) = point {
        let comma_comments = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
        list.push_comma(poly_gap, poly_doc, comma_comments);
        let (point_gap, point_doc) = format_exp(point, cursor, style);
        list.push(point_gap, point_doc);
    } else {
        list.push(poly_gap, poly_doc);
    }
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));

    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text("eval"),
            selector,
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

#[allow(clippy::too_many_arguments)]
fn format_sampling(
    name: &'static str,
    keyword: Token<'static>,
    typ: &Tid,
    star: bool,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    });
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
        style,
    );
    let typ_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let star = if star {
        let comments = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Star))),
            style,
        );
        ALLOC.concat([comments, ALLOC.text("*")])
    } else {
        ALLOC.nil()
    };
    let content = ALLOC.concat([ALLOC.text(typ.to_string()), star]);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));

    let mut list = DelimList::new(style);
    list.push(typ_gap, content);
    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("<", ">", close_comments),
        ]),
    )
}

#[allow(clippy::too_many_arguments)]
fn format_assertion(
    name: &'static str,
    keyword: Token<'static>,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    let keyword_gap = cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    });
    let open = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LParen))),
        style,
    );
    let (lhs_gap, lhs_doc) = format_exp(lhs, cursor, style);
    let eq_gap = cursor.advance_to_token(end, |token| matches!(token, Token::EqEq));
    let (rhs_gap, rhs_doc) = format_exp(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));

    let content = ALLOC
        .concat([
            lhs_doc,
            gap_space(trim_if_clean(eq_gap), style),
            ALLOC
                .concat([ALLOC.line(), ALLOC.text("==")])
                .flat_alt(ALLOC.text("==")),
            gap_space(trim_if_clean(rhs_gap), style),
            rhs_doc,
        ])
        .nest(style.indent_width() as isize)
        .group();

    let mut list = DelimList::new(style);
    list.push(lhs_gap, content);
    (
        keyword_gap,
        ALLOC.concat([
            ALLOC.text(name),
            open,
            list.finish("(", ")", close_comments),
        ]),
    )
}

/// Format a list of `name: value` fields as comma-terminated items.
/// Used by both Typ::Record and Exp::Record.
fn format_field_items<N, T, F>(
    fields: &[(&N, &Spanned<T>)],
    format_value: F,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
    list: &mut DelimList<'_>,
) where
    N: std::fmt::Display,
    F: Fn(&Spanned<T>, &mut TokenCursor, usize, &Style) -> (TriviaGap, Doc<'static>),
{
    for (index, (name, value)) in fields.iter().enumerate() {
        let name_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
        let colon = gap_none(
            trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::Colon))),
            style,
        );
        let (value_gap, value_doc) = format_value(value, cursor, value.span.end, style);
        let field = ALLOC.concat([
            ALLOC.text(name.to_string()),
            colon,
            ALLOC.text(":"),
            gap_space(trim_if_clean(value_gap), style),
            value_doc,
        ]);
        if index + 1 < fields.len() {
            list.push_comma(
                name_gap,
                field,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
            );
        } else {
            list.push(name_gap, field);
        }
    }
}

fn format_exps_items(
    exps: &Exps<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
    list: &mut DelimList<'_>,
) {
    for (index, exp) in exps.0.iter().enumerate() {
        let (exp_gap, exp_doc) = format_exp(exp, cursor, style);
        if index + 1 < exps.0.len() {
            list.push_comma(
                exp_gap,
                exp_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
            );
        } else {
            list.push(exp_gap, exp_doc);
        }
    }
}

fn parenthesize(doc: Doc<'static>, needed: bool) -> Doc<'static> {
    if needed {
        ALLOC.concat([ALLOC.text("("), doc, ALLOC.text(")")])
    } else {
        doc
    }
}

fn comma_terminated_item(item: Doc<'static>, gap: TriviaGap, style: &Style) -> Doc<'static> {
    let needs_break = gap.needs_line_break();
    // After comma: inline comments get `space` open (stay on same line),
    // at_line_start comments get `hardline` open (new line). No preceding
    // `line_()` here — the comma is between items, not at the start.
    let open = match gap.first() {
        Some(TriviaElement::Comment(c)) if c.at_line_start => Some(ALLOC.hardline()),
        Some(TriviaElement::Comment(_)) => Some(ALLOC.text(" ")),
        _ => None,
    };
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
        ALLOC.text(","),
        format_gap(gap, open, end, Some(sep), style),
    ])
}

fn take_separator_gap(
    cursor: &mut TokenCursor,
    end: usize,
    pred: impl Fn(&Token) -> bool,
) -> TriviaGap {
    let before = cursor.advance_to_token(end, &pred);
    let next = cursor
        .peek_token(end, |_| true)
        .map(|r| r.start)
        .unwrap_or(end);
    before.join(cursor.advance_to(next))
}

/// Builder for items inside a `delimited_list`.
///
/// Automatically picks the right gap function for each item's leading
/// gap:
/// - **First item**: `gap_list` — no space before a comment (it's
///   right after the open delimiter: `</* c */ F>`, not `< /* c */ F>`).
/// - **Subsequent items**: `gap_none` — space before a comment (it's
///   after a comma: `, /* c */ G>`).
///
/// The close-delimiter trailing (no space after comment before `>`/`)`) is
/// handled by `delimited_list`'s `close_end = nil`.
struct DelimList<'a> {
    items: Vec<Doc<'static>>,
    is_first: bool,
    style: &'a Style,
}

impl<'a> DelimList<'a> {
    fn new(style: &'a Style) -> Self {
        Self {
            items: Vec::new(),
            is_first: true,
            style,
        }
    }

    /// Push an item with a leading gap. The gap is rendered with
    /// `gap_list` for the first item (with `trim_start` to strip blank
    /// lines after the open delimiter), `gap_none` for subsequent items.
    fn push(&mut self, gap: TriviaGap, doc: Doc<'static>) {
        let gap = if self.is_first {
            gap_list(trim_if_clean(gap).trim_start(), self.style)
        } else {
            gap_none(trim_if_clean(gap), self.style)
        };
        self.items.push(ALLOC.concat([gap, doc]));
        self.is_first = false;
    }

    /// Push an item with a leading gap, followed by a comma.
    /// The comma gap is passed to `comma_terminated_item`.
    fn push_comma(&mut self, gap: TriviaGap, doc: Doc<'static>, comma: TriviaGap) {
        let gap = if self.is_first {
            gap_list(trim_if_clean(gap).trim_start(), self.style)
        } else {
            gap_none(trim_if_clean(gap), self.style)
        };
        let item = ALLOC.concat([gap, doc]);
        self.items
            .push(comma_terminated_item(item, comma, self.style));
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
    fn finish(
        self,
        open: &'static str,
        close: &'static str,
        close_comments: TriviaGap,
    ) -> Doc<'static> {
        let style = self.style;
        let items = self.items;
        let indent = style.indent_width() as isize;
        let close_comments = close_comments.trim_end();
        let close_needs_break = close_comments.needs_line_break();
        let close_sep = if close_needs_break {
            ALLOC.hardline()
        } else {
            ALLOC.line_()
        };
        let close_end = if close_needs_break {
            Some(ALLOC.hardline())
        } else {
            Some(ALLOC.nil())
        };
        // Before close delimiter: inline comments get `space` open,
        // at_line_start comments get `hardline` open. The `line_()` before
        // the close delimiter is inside the group and may not break in flat
        // mode, so we need explicit `hardline` for at_line_start comments.
        let close_open = match close_comments.first() {
            Some(TriviaElement::Comment(c)) if c.at_line_start => Some(ALLOC.hardline()),
            Some(TriviaElement::Comment(_)) => Some(ALLOC.text(" ")),
            _ => None,
        };
        let close_gap = format_gap(
            close_comments,
            close_open,
            close_end,
            Some(close_sep),
            style,
        );
        ALLOC
            .text(open)
            .append(
                ALLOC
                    .concat([ALLOC
                        .concat([
                            ALLOC.line_(),
                            ALLOC.concat(items),
                            ALLOC.text(",").flat_alt(ALLOC.nil()),
                            close_gap,
                        ])
                        .nest(indent)])
                    .group(),
            )
            .append(ALLOC.text(close))
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

fn matches_binop(op: BinOp, token: &Token) -> bool {
    match op {
        BinOp::Add => matches!(token, Token::Plus),
        BinOp::Sub => matches!(token, Token::Minus),
        BinOp::Mul => matches!(token, Token::Star),
        BinOp::Div => matches!(token, Token::Slash),
        BinOp::Pow => matches!(token, Token::Caret),
        BinOp::Dot => false,
        BinOp::Concat => matches!(token, Token::PlusPlus),
        BinOp::Rem => matches!(token, Token::Percent),
    }
}

fn binop_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Pow => "^",
        BinOp::Dot => unreachable!(),
        BinOp::Concat => "++",
        BinOp::Rem => "%",
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Pow => "^",
        BinOp::Dot => "dot",
        BinOp::Concat => "++",
        BinOp::Rem => "%",
    }
}

fn neg_needs_paren(exp: &Exp<Size>) -> bool {
    matches!(exp, Exp::Bin(op, _, _) if op.parser_precedence() <= 3)
}

fn size_lhs_needs_paren(size: &Size, precedence: usize, right_assoc: bool) -> bool {
    let child = size.precedence();
    child < precedence || (child == precedence && right_assoc)
}

fn size_rhs_needs_paren(size: &Size, precedence: usize, right_assoc: bool) -> bool {
    let child = size.precedence();
    child < precedence || (child == precedence && !right_assoc)
}
