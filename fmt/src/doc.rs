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
    Comment, TokenCursor, TokenStream, TriviaElement, TriviaGap, format_gap, format_gap_after,
    format_gap_before,
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
                parts.push(format_gap_before(gap, style));
            } else {
                // Gap is all comments, no blank lines — force one blank
                // line after the comment. `format_gap_after` handles
                // positioning: `space` for trailing comments, `hardline`
                // for line-start comments.
                parts.push(format_gap_after(
                    gap,
                    hardlines(1 + style.max_blank_lines.min(1)),
                    style,
                ));
            }
        } else {
            parts.push(format_gap_before(gap, style));
        }
        parts.push(format_decl(decl, &mut cursor, style));
    }

    if !decls.is_empty() {
        parts.push(ALLOC.hardline());
    }
    parts.push(format_gap_before(cursor.advance_to(src_len), style));

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
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwProto)),
                style,
            );
            let sig = format_sig(&decl.node.sig, cursor, end, style);
            let where_gap = cursor
                .advance_to_token(end, |token| matches!(token, Token::KwWhere))
                .trim_start();
            // When comments are present between `)` and `where`, use
            // `format_gap` with `open = hardline()` so the comment starts
            // on a new line (not glued to `)`), and `where` follows on
            // its own line without a leading space.
            let has_where_comments = where_gap.has_comments();
            let where_comments = if has_where_comments {
                let end = if where_gap.needs_line_break() {
                    ALLOC.hardline()
                } else {
                    ALLOC.nil()
                };
                format_gap(where_gap, ALLOC.hardline(), end, style)
            } else {
                format_gap_before(where_gap, style)
            };
            let where_text = if has_where_comments {
                ALLOC.text("where")
            } else {
                ALLOC.text(" where")
            };
            // Gap after `where` — strip blank lines (structural hardline follows).
            let relation_leading =
                format_gap_before(cursor.advance_to(relation.span.start).trim_start(), style);
            let relation = format_relation(relation, cursor, style);
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));
            // Comments before `{` go inside the where group's nest so they
            // align with the relation body, not at column 0. Skip the
            // leading `ALLOC.line()` when the gap already starts with
            // `BlankLines` — otherwise the structural line break and the
            // blank lines double up.
            let gap_starts_with_blanks =
                matches!(open_gap.first(), Some(TriviaElement::BlankLines(_)));
            let open_comments = format_gap_before(open_gap, style);
            // Gap after `{` — strip blank lines (structural hardline follows).
            let body_leading =
                format_gap_before(cursor.advance_to(body.span.start).trim_start(), style);
            let body = format_body_exp(body, cursor, style);
            // Gap before `}` — strip blank lines (structural hardline precedes).
            let close_comments = cursor
                .advance_to_token(end, |token| matches!(token, Token::RBrace))
                .trim_end();
            let open_break = if gap_starts_with_blanks {
                ALLOC.nil()
            } else {
                ALLOC.line()
            };
            ALLOC.concat([
                keyword,
                ALLOC.text("proto "),
                sig,
                where_comments,
                ALLOC
                    .concat([
                        where_text,
                        ALLOC
                            .concat([ALLOC.line(), relation_leading, relation])
                            .nest(style.indent_width() as isize),
                        ALLOC
                            .concat([open_break, open_comments])
                            .nest(style.indent_width() as isize),
                    ])
                    .group(),
                ALLOC.text("{"),
                ALLOC.hardline(),
                ALLOC
                    .concat([
                        body_leading,
                        body,
                        format_gap_after(close_comments, ALLOC.hardline(), style),
                    ])
                    .indent(style.indent_width()),
                ALLOC.text("}"),
            ])
        }
        Body::Func { body } => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFn)),
                style,
            );
            let sig = format_sig(&decl.node.sig, cursor, end, style);
            let has_ret = decl.node.sig.ret.is_some();
            let ret = if let Some(ret) = &decl.node.sig.ret {
                // Gap after `)` — strip blank lines (structural position).
                let arrow = format_gap_before(
                    cursor
                        .advance_to_token(end, |token| matches!(token, Token::Arrow))
                        .trim_start(),
                    style,
                );
                ALLOC.concat([
                    arrow,
                    ALLOC.text(" -> "),
                    format_typ(&ret.node, cursor, ret.span.end, style),
                ])
            } else {
                ALLOC.nil()
            };
            let open_gap = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));
            // When no return type, `open_gap` is the gap after `)` — strip.
            let open_comments = if has_ret {
                format_gap_before(open_gap, style)
            } else {
                format_gap_before(open_gap.trim_start(), style)
            };
            // Gap after `{` — strip blank lines (structural hardline follows).
            let body_leading =
                format_gap_before(cursor.advance_to(body.span.start).trim_start(), style);
            let body = format_body_exp(body, cursor, style);
            // Gap before `}` — strip blank lines (structural hardline precedes).
            let close_comments = cursor
                .advance_to_token(end, |token| matches!(token, Token::RBrace))
                .trim_end();
            ALLOC.concat([
                keyword,
                ALLOC.text("fn "),
                sig,
                ret,
                open_comments,
                ALLOC.text(" {"),
                ALLOC.hardline(),
                ALLOC
                    .concat([
                        body_leading,
                        body,
                        format_gap_after(close_comments, ALLOC.hardline(), style),
                    ])
                    .indent(style.indent_width()),
                ALLOC.text("}"),
            ])
        }
        Body::TypeAlias => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwType)),
                style,
            );
            let name = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let eq = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Eq)),
                style,
            );
            let typ = decl
                .node
                .sig
                .ret
                .as_ref()
                .expect("type aliases have a type");
            let typ = format_typ(&typ.node, cursor, typ.span.end, style);
            let semi = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Semi)),
                style,
            );
            ALLOC.concat([
                keyword,
                ALLOC.text("type "),
                name,
                ALLOC.text(decl.node.sig.name.node.to_string()),
                eq,
                ALLOC.text(" = "),
                typ,
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
) -> Doc<'static> {
    let name = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
        style,
    );
    let typevar_open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
        style,
    );
    let typevars = format_typevars(&sig.typevars.node, cursor, end, style);
    let typevar_close = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
        style,
    );
    let arg_open_comments = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );

    let mut args = Vec::new();
    // Find the `)` position to limit trailing comma search for the last arg.
    let rparen_end = cursor.peek_token(end, |token| matches!(token, Token::RParen));
    for (index, arg) in sig.args.node.0.iter().enumerate() {
        let arg_doc = format_arg(arg, cursor, style);
        if index + 1 < sig.args.node.0.len() {
            args.push(comma_terminated_item(
                arg_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                style,
            ));
        } else {
            // Last arg: consume trailing comma comments only if a comma exists before `)`.
            if let Some(rp_end) = &rparen_end {
                let comma_comments = format_gap_before(
                    cursor.advance_to_token(rp_end.end, |token| matches!(token, Token::Comma)),
                    style,
                );
                args.push(ALLOC.concat([arg_doc, comma_comments]));
            } else {
                args.push(arg_doc);
            }
        }
    }
    let arg_close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let args = delimited_list("(", args, ")", arg_close_comments, style);

    ALLOC.concat([
        name,
        ALLOC.text(sig.name.node.to_string()),
        typevar_open,
        ALLOC.text("<"),
        typevars,
        typevar_close,
        ALLOC.text(">"),
        arg_open_comments,
        args,
    ])
}

fn format_arg(
    arg: &Spanned<Arg<Tid, Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let end = arg.span.end;
    let mut parts = Vec::new();
    let mut has_prefix = false;

    if !matches!(arg.node.qualifier, Qualifier::Local) {
        let qualifier = format_gap_before(
            cursor.advance_to_token(end, |token| match arg.node.qualifier {
                Qualifier::Witness => matches!(token, Token::KwWitness),
                Qualifier::Extra => matches!(token, Token::KwExtra),
                Qualifier::Instance => matches!(token, Token::KwInstance),
                Qualifier::Local => false,
            }),
            style,
        );
        parts.push(qualifier);
        parts.push(ALLOC.text(qualifier_text(arg.node.qualifier)));
        has_prefix = true;
    }

    if !matches!(arg.node.distribution, Distribution::Nonuniform) {
        if has_prefix {
            parts.push(ALLOC.text(" "));
        }
        parts.push(format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::KwUniform)),
            style,
        ));
        parts.push(ALLOC.text("uniform"));
        if matches!(arg.node.distribution, Distribution::UniformNonZero) {
            parts.push(format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Star)),
                style,
            ));
            parts.push(ALLOC.text("*"));
        }
        has_prefix = true;
    }

    if has_prefix {
        parts.push(ALLOC.text(" "));
    }
    parts.push(format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
        style,
    ));
    parts.push(ALLOC.text(arg.node.id.to_string()));
    parts.push(format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
        style,
    ));
    parts.push(ALLOC.text(": "));
    parts.push(format_typ(&arg.node.typ, cursor, end, style));
    ALLOC.concat(parts)
}

fn format_typevars(
    typevars: &TypeVars<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let mut items = Vec::new();
    for (index, typevar) in typevars.0.iter().enumerate() {
        let typevar_doc = format_typevar(typevar, cursor, style);
        if index + 1 < typevars.0.len() {
            items.push(comma_terminated_item(
                typevar_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                style,
            ));
        } else {
            items.push(typevar_doc);
        }
    }
    delimited_list("", items, "", TriviaGap::default(), style)
}

fn format_typevar(
    typevar: &Spanned<TypeVar<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let end = typevar.span.end;
    let id = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
        style,
    );
    let colon = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
        style,
    );
    let kind = format_kind(&typevar.node.kind, cursor, end, style);
    ALLOC.concat([
        id,
        ALLOC.text(typevar.node.id.to_string()),
        colon,
        ALLOC.text(": "),
        kind,
    ])
}

fn format_typ(
    typ: &GTyp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    match typ {
        Typ::Poly(base, m, n) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| {
                    matches!(token, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
                }),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
                style,
            );
            let base_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            // Consume all inner gaps and format sizes up-front so we can
            // decide whether to use Uni/Mle sugar without losing comments.
            let comma_one = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let m_doc = format_size(m, cursor, end, style);
            let comma_two = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let n_doc = format_size(n, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));

            // Uni<F, N> is sugar for Poly<F, 1, N>; Mle<F, N> is sugar for
            // Poly<F, N, 1>. Emit the sugar only when the AST matches AND
            // no comments are attached to the skipped argument's gaps.
            let is_uni =
                matches!(m, Size::Lit(1)) && !comma_one.has_comments() && !comma_two.has_comments();
            let is_mle = matches!(n, Size::Lit(1)) && !comma_two.has_comments();

            let (name, items): (&str, Vec<Doc<'static>>) = if is_uni {
                (
                    "Uni",
                    vec![
                        comma_terminated_item(
                            ALLOC.concat([base_comments, ALLOC.text(base.to_string())]),
                            comma_one,
                            style,
                        ),
                        n_doc,
                    ],
                )
            } else if is_mle {
                (
                    "Mle",
                    vec![
                        comma_terminated_item(
                            ALLOC.concat([base_comments, ALLOC.text(base.to_string())]),
                            comma_one,
                            style,
                        ),
                        m_doc,
                    ],
                )
            } else {
                (
                    "Poly",
                    vec![
                        comma_terminated_item(
                            ALLOC.concat([base_comments, ALLOC.text(base.to_string())]),
                            comma_one,
                            style,
                        ),
                        comma_terminated_item(m_doc, comma_two, style),
                        n_doc,
                    ],
                )
            };

            ALLOC.concat([
                keyword,
                ALLOC.text(name),
                open,
                ALLOC.text("<"),
                delimited_list("", items, "", close_comments, style),
                ALLOC.text(">"),
            ])
        }
        Typ::Vec(typ, size) => {
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
                style,
            );
            let typ = format_typ(&typ.node, cursor, typ.span.end, style);
            let semi = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Semi)),
                style,
            );
            let size = format_size(size, cursor, end, style);
            let close = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack)),
                style,
            );
            ALLOC.concat([
                open,
                ALLOC.text("["),
                typ,
                semi,
                ALLOC.text("; "),
                size,
                close,
                ALLOC.text("]"),
            ])
        }
        Typ::Base(base) => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            ALLOC.concat([comments, ALLOC.text(base.to_string())])
        }
        Typ::Fin(range) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFin)),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
                style,
            );
            let range = format_range(range, cursor, end, style);
            let close = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
                style,
            );
            ALLOC.concat([
                keyword,
                ALLOC.text("Fin"),
                open,
                ALLOC.text("<"),
                range,
                close,
                ALLOC.text(">"),
            ])
        }
        Typ::Unit => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwUnit)),
                style,
            );
            ALLOC.concat([comments, ALLOC.text("Unit")])
        }
        Typ::Record(fields) => {
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrace)),
                style,
            );
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, typ)| typ.span.start);
            let mut items = Vec::new();
            for (index, (name, typ)) in fields.iter().enumerate() {
                let name_comments = format_gap_before(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                    style,
                );
                let colon = format_gap_before(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
                    style,
                );
                let typ_doc = format_typ(&typ.node, cursor, typ.span.end, style);
                let field = ALLOC.concat([
                    name_comments,
                    ALLOC.text(name.to_string()),
                    colon,
                    ALLOC.text(": "),
                    typ_doc,
                ]);
                if index + 1 < fields.len() {
                    items.push(comma_terminated_item(
                        field,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                        style,
                    ));
                } else {
                    items.push(field);
                }
            }
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrace));
            ALLOC.concat([
                open,
                ALLOC.text("{"),
                delimited_list("", items, "", close_comments, style),
                ALLOC.text("}"),
            ])
        }
    }
}

fn format_kind(
    kind: &Kind<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    match kind {
        Kind::Field => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwField)),
                style,
            );
            ALLOC.concat([comments, ALLOC.text("Field")])
        }
        Kind::Group => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwGroup)),
                style,
            );
            ALLOC.concat([comments, ALLOC.text("Group")])
        }
        Kind::SizeVar => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwSize)),
                style,
            );
            ALLOC.concat([comments, ALLOC.text("Size")])
        }
        Kind::Scalar(ids) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwScalar)),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
                style,
            );
            let ids: Vec<_> = ids.iter().collect();
            let mut items = Vec::new();
            for (index, id) in ids.iter().enumerate() {
                let id_comments = format_gap_before(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                    style,
                );
                let id_doc = ALLOC.concat([id_comments, ALLOC.text(id.to_string())]);
                if index + 1 < ids.len() {
                    items.push(comma_terminated_item(
                        id_doc,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                        style,
                    ));
                } else {
                    items.push(id_doc);
                }
            }
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            ALLOC.concat([
                keyword,
                ALLOC.text("Scalar"),
                open,
                ALLOC.text("<"),
                delimited_list("", items, "", close_comments, style),
                ALLOC.text(">"),
            ])
        }
        Kind::Pairing(g1, g2) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwPairing)),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
                style,
            );
            let first = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let second = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            let items = vec![
                comma_terminated_item(
                    ALLOC.concat([first, ALLOC.text(g1.to_string())]),
                    comma,
                    style,
                ),
                ALLOC.concat([second, ALLOC.text(g2.to_string())]),
            ];
            let args = delimited_list("<", items, ">", close_comments, style);
            ALLOC.concat([keyword, ALLOC.text("Pairing"), open, args])
        }
        Kind::Range(range) => format_range(range, cursor, end, style),
    }
}

fn format_size_spanned(
    size: &Spanned<Size>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    format_size(&size.node, cursor, size.span.end, style)
}

fn format_size(size: &Size, cursor: &mut TokenCursor, end: usize, style: &Style) -> Doc<'static> {
    match size {
        Size::Var(id) => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            ALLOC.concat([comments, ALLOC.text(id.to_string())])
        }
        Size::Lit(value) => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_))),
                style,
            );
            ALLOC.concat([comments, ALLOC.text(value.to_string())])
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
    op: &str,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let (precedence, right_assoc) = match op {
        "+" | "-" => (1, false),
        "*" | "/" => (2, false),
        "^" => (3, true),
        _ => unreachable!(),
    };
    let lhs = parenthesize(
        format_size_spanned(lhs, cursor, style),
        size_lhs_needs_paren(&lhs.node, precedence, right_assoc),
    );
    let op_comments = format_gap_before(
        cursor.advance_to_token(end, |token| matches_size_op(op, token)),
        style,
    );
    let rhs = parenthesize(
        format_size_spanned(rhs, cursor, style),
        size_rhs_needs_paren(&rhs.node, precedence, right_assoc),
    );
    ALLOC.concat([lhs, op_comments, ALLOC.text(format!(" {op} ")), rhs])
}

fn format_size_call(
    name: &str,
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let name_comments = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
        style,
    );
    let open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );
    let lhs = format_size_spanned(lhs, cursor, style);
    let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
    let rhs = format_size_spanned(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let items = vec![comma_terminated_item(lhs, comma, style), rhs];
    let args = delimited_list("(", items, ")", close_comments, style);
    ALLOC.concat([name_comments, ALLOC.text(name.to_string()), open, args])
}

fn format_range(
    range: &Range<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let start = format_range_size(&range.start, cursor, end, style);
    if let Some(step) = &range.step {
        let comma = format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::Comma)),
            style,
        );
        let step = format_range_size(step, cursor, end, style);
        let dots = format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
            style,
        );
        let last = range.end.as_ref().expect("stepped ranges have an end");
        let last = format_range_size(last, cursor, end, style);
        ALLOC.concat([
            start,
            comma,
            ALLOC.text(", "),
            step,
            dots,
            ALLOC.text(".."),
            last,
        ])
    } else if let Some(last) = &range.end {
        let dots = format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
            style,
        );
        let last = format_range_size(last, cursor, end, style);
        ALLOC.concat([start, dots, ALLOC.text(".."), last])
    } else {
        start
    }
}

fn format_range_size(
    size: &Spanned<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
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
            let lhs = format_exp(lhs, cursor, style);
            let eq = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::EqEq)),
                style,
            );
            let rhs = format_exp(rhs, cursor, style);
            ALLOC
                .concat([
                    lhs,
                    eq,
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text("== ")])
                        .flat_alt(ALLOC.text(" == ")),
                    rhs,
                ])
                .nest(style.indent_width() as isize)
                .group()
        }
        Exp::Let(Some(var), value, body) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
                style,
            );
            let name = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let eq = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq)),
                style,
            );
            let value = format_exp(value, cursor, style);
            let body = if let Some(body) = body.as_ref() {
                let semi_gap =
                    take_separator_gap(cursor, exp.span.end, |token| matches!(token, Token::Semi));
                ALLOC.concat([
                    format_gap_after(semi_gap, ALLOC.hardline(), style),
                    format_relation(body, cursor, style),
                ])
            } else {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                let sep = if before_semi.needs_line_break() {
                    ALLOC.hardline()
                } else {
                    ALLOC.nil()
                };
                format_gap_after(before_semi, sep, style)
            };
            ALLOC.concat([
                keyword,
                ALLOC.text("let "),
                name,
                ALLOC.text(var.to_string()),
                eq,
                ALLOC.text(" = "),
                value,
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
                    format_gap_after(semi_gap, ALLOC.hardline(), style),
                    format_relation(body, cursor, style),
                ])
            } else {
                let before_semi =
                    cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
                let sep = if before_semi.needs_line_break() {
                    ALLOC.hardline()
                } else {
                    ALLOC.nil()
                };
                format_gap_after(before_semi, sep, style)
            };
            ALLOC.concat([value, ALLOC.text(";"), body])
        }
        _ => format_exp(exp, cursor, style),
    }
}

fn format_body_exp(
    exp: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    match &exp.node {
        Exp::Let(Some(var), value, body) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
                style,
            );
            let name = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let eq = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq)),
                style,
            );
            let value = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                keyword,
                ALLOC.text("let "),
                name,
                ALLOC.text(var.to_string()),
                eq,
                ALLOC.text(" = "),
                value,
                ALLOC.text(";"),
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let value = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([value, ALLOC.text(";"), body])
        }
        Exp::Log(var, value, body) => {
            let name = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let arrow = format_gap_before(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::LArrow)),
                style,
            );
            let value = format_exp(value, cursor, style);
            let before_semi =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = format_body_tail(before_semi, body.as_deref(), cursor, style);

            ALLOC.concat([
                name,
                ALLOC.text(var.to_string()),
                arrow,
                ALLOC.text(" <- "),
                value,
                ALLOC.text(";"),
                body,
            ])
        }
        _ => format_exp(exp, cursor, style),
    }
}

fn format_body_tail(
    before_semi: TriviaGap,
    body: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let Some(body) = body else {
        let sep = if before_semi.needs_line_break() {
            ALLOC.hardline()
        } else {
            ALLOC.nil()
        };
        return format_gap_after(before_semi, sep, style);
    };

    let after_semi = cursor.advance_to(body.span.start);
    let gap = before_semi.join(after_semi);
    ALLOC.concat([
        format_gap_after(gap, ALLOC.hardline(), style),
        format_body_exp(body, cursor, style),
    ])
}

fn hardlines(count: usize) -> Doc<'static> {
    ALLOC.concat((0..count).map(|_| ALLOC.hardline()))
}

fn format_exp(exp: &Spanned<Exp<Size>>, cursor: &mut TokenCursor, style: &Style) -> Doc<'static> {
    let end = exp.span.end;
    match &exp.node {
        Exp::Lit(value) => format_size(value, cursor, end, style),
        Exp::Unit => {
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
                style,
            );
            let close = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen)),
                style,
            );
            ALLOC.concat([open, ALLOC.text("("), close, ALLOC.text(")")])
        }
        Exp::Var(var) => {
            let comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            ALLOC.concat([comments, ALLOC.text(var.to_string())])
        }
        Exp::Neg(inner) => {
            let minus = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Minus)),
                style,
            );
            let inner = parenthesize(
                format_exp(inner, cursor, style),
                neg_needs_paren(&inner.node),
            );
            ALLOC.concat([minus, ALLOC.text("-"), inner.group()])
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
            parts.push(parenthesize(
                format_exp(chain[0], cursor, style),
                lhs_needs_paren(*op, &chain[0].node),
            ));

            // Remaining operands — each preceded by `op`.
            for operand in &chain[1..] {
                let op_comments = format_gap_before(
                    cursor.advance_to_token(end, |token| matches_binop(*op, token)),
                    style,
                );
                parts.push(op_comments);
                parts.push(
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text(binop_symbol(*op)), ALLOC.text(" ")])
                        .flat_alt(ALLOC.text(binop_text(*op))),
                );
                parts.push(parenthesize(
                    format_exp(operand, cursor, style),
                    rhs_needs_paren(*op, &operand.node),
                ));
            }

            ALLOC.concat(parts).nest(indent).group()
        }
        Exp::App(function, args) => {
            let function_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
                style,
            );
            let items = format_exps_items(args, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let args = delimited_list("(", items, ")", close_comments, style);
            ALLOC.concat([
                function_comments,
                ALLOC.text(function.to_string()),
                open,
                args,
            ])
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
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
                style,
            );
            let items = format_exps_items(values, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            let values = delimited_list("[", items, "]", close_comments, style);
            ALLOC.concat([open, values])
        }
        Exp::Range(range) => format_range(range, cursor, end, style),
        Exp::Map(body, var, range) => {
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
                style,
            );
            let body = format_exp(body, cursor, style);
            let for_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFor)),
                style,
            );
            let var_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let in_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwIn)),
                style,
            );
            let range = format_exp(range, cursor, style);
            let close = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack)),
                style,
            );
            ALLOC.concat([
                open,
                ALLOC.text("["),
                ALLOC
                    .concat([
                        ALLOC.line_(),
                        body.group(),
                        for_comments,
                        ALLOC.line().flat_alt(ALLOC.text(" ")),
                        ALLOC
                            .concat([
                                ALLOC.text("for "),
                                var_comments,
                                ALLOC.text(var.to_string()),
                                in_comments,
                                ALLOC.text(" in "),
                                range,
                            ])
                            .group(),
                        ALLOC.line_(),
                    ])
                    .nest(style.indent_width() as isize)
                    .group(),
                close,
                ALLOC.text("]"),
            ])
        }
        Exp::Reduce(op, value) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwReduce)),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
                style,
            );
            let op_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches_binop(*op, token)),
                style,
            );
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let value = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let op_item = comma_terminated_item(
                ALLOC.concat([op_comments, ALLOC.text(binop_symbol(*op))]),
                comma,
                style,
            );
            let items = vec![op_item, value];
            let args = delimited_list("(", items, ")", close_comments, style);
            ALLOC.concat([keyword, ALLOC.text("reduce"), open, args])
        }
        Exp::Ram(base, index) => {
            let base = format_exp(base, cursor, style);
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
                style,
            );
            let index = format_exp(index, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            ALLOC.concat([
                base.group(),
                open,
                ALLOC.text("["),
                delimited_list("", vec![index], "", close_comments, style),
                ALLOC.text("]"),
            ])
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
        Exp::Let(_, _, _) | Exp::Log(_, _, _) => format_body_exp(exp, cursor, style),
        Exp::Assert(lhs, rhs) => {
            format_assertion("assert", Token::KwAssert, lhs, rhs, cursor, end, style)
        }
        Exp::Verify(lhs, rhs) => {
            format_assertion("verify", Token::KwVerify, lhs, rhs, cursor, end, style)
        }
        Exp::Fun(vars, body) => {
            let keyword = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFun)),
                style,
            );
            let mut items = Vec::new();
            for (index, var) in vars.iter().enumerate() {
                let var_comments = format_gap_before(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                    style,
                );
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
            let arrow = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::FatArrow)),
                style,
            );
            let body = format_exp(body, cursor, style);
            ALLOC.concat([
                keyword,
                ALLOC.text("fun "),
                ALLOC.concat(items),
                arrow,
                ALLOC.text(" => "),
                body.group(),
            ])
        }
        Exp::Record(fields) => {
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBraceBar)),
                style,
            );
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, value)| value.span.start);
            let mut items = Vec::new();
            for (index, (name, value)) in fields.iter().enumerate() {
                let name_comments = format_gap_before(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                    style,
                );
                let colon = format_gap_before(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
                    style,
                );
                let value_doc = format_exp(value, cursor, style);
                let field = ALLOC.concat([
                    name_comments,
                    ALLOC.text(name.to_string()),
                    colon,
                    ALLOC.text(": "),
                    value_doc,
                ]);
                if index + 1 < fields.len() {
                    items.push(comma_terminated_item(
                        field,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                        style,
                    ));
                } else {
                    items.push(field);
                }
            }
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::BarRBrace));
            ALLOC.concat([
                open,
                ALLOC.text("{|"),
                delimited_list("", items, "", close_comments, style),
                ALLOC.text("|}"),
            ])
        }
        Exp::Proj(base, field) => {
            let base = format_exp(base, cursor, style);
            let dot = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Dot)),
                style,
            );
            let field_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            ALLOC.concat([
                base.group(),
                dot,
                ALLOC.text("."),
                field_comments,
                ALLOC.text(field.to_string()),
            ])
        }
        Exp::SetRecord(record, field, value) => {
            let record = format_exp(record, cursor, style);
            let dot = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Dot)),
                style,
            );
            let set = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let open = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
                style,
            );
            let field_comments = format_gap_before(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                style,
            );
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let value = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let items = vec![
                comma_terminated_item(
                    ALLOC.concat([field_comments, ALLOC.text(field.to_string())]),
                    comma,
                    style,
                ),
                value,
            ];
            ALLOC.concat([
                record.group(),
                dot,
                ALLOC.text("."),
                set,
                ALLOC.text("set"),
                open,
                delimited_list("(", items, ")", close_comments, style),
            ])
        }
    }
}

fn format_unary_call(
    name: &str,
    pred: impl Fn(&Token) -> bool,
    arg: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let keyword = format_gap_before(cursor.advance_to_token(end, pred), style);
    let open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );
    let arg_doc = format_exp(arg, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let items = vec![arg_doc];
    ALLOC.concat([
        keyword,
        ALLOC.text(name.to_string()),
        open,
        delimited_list("(", items, ")", close_comments, style),
    ])
}

fn format_binary_call(
    name: &str,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let keyword = format_gap_before(
        cursor.advance_to_token(end, |token| {
            matches!(
                token,
                Token::Id(_) | Token::KwInterpolate | Token::KwPair | Token::KwDot
            )
        }),
        style,
    );
    let open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );
    let lhs_doc = format_exp(lhs, cursor, style);
    let comma_comments = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
    let rhs_doc = format_exp(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let items = vec![
        comma_terminated_item(lhs_doc, comma_comments, style),
        rhs_doc,
    ];
    ALLOC.concat([
        keyword,
        ALLOC.text(name.to_string()),
        open,
        delimited_list("(", items, ")", close_comments, style),
    ])
}

fn format_evaluate(
    poly: &Spanned<Exp<Size>>,
    range: Option<&Range<Size>>,
    point: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let keyword = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::KwEval)),
        style,
    );
    let selector = if let Some(range) = range {
        let open = format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
            style,
        );
        let range = format_range(range, cursor, end, style);
        let close = format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
            style,
        );
        ALLOC.concat([open, ALLOC.text("<"), range, close, ALLOC.text(">")])
    } else {
        ALLOC.nil()
    };
    let open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );
    let poly_doc = format_exp(poly, cursor, style);
    let mut items = Vec::new();
    if let Some(point) = point {
        let comma_comments = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
        items.push(comma_terminated_item(poly_doc, comma_comments, style));
        items.push(format_exp(point, cursor, style));
    } else {
        items.push(poly_doc);
    }
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    ALLOC.concat([
        keyword,
        ALLOC.text("eval"),
        selector,
        open,
        delimited_list("(", items, ")", close_comments, style),
    ])
}

fn format_sampling(
    name: &str,
    keyword: Token<'static>,
    typ: &Tid,
    star: bool,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let keyword_comments = format_gap_before(
        cursor.advance_to_token(end, |token| {
            std::mem::discriminant(token) == std::mem::discriminant(&keyword)
        }),
        style,
    );
    let open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
        style,
    );
    let typ_comments = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
        style,
    );
    let star = if star {
        let comments = format_gap_before(
            cursor.advance_to_token(end, |token| matches!(token, Token::Star)),
            style,
        );
        ALLOC.concat([comments, ALLOC.text("*")])
    } else {
        ALLOC.nil()
    };
    let close = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
        style,
    );
    ALLOC.concat([
        keyword_comments,
        ALLOC.text(name.to_string()),
        open,
        ALLOC.text("<"),
        typ_comments,
        ALLOC.text(typ.to_string()),
        star,
        close,
        ALLOC.text(">"),
    ])
}

fn format_assertion(
    name: &str,
    keyword: Token<'static>,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let keyword_comments = format_gap_before(
        cursor.advance_to_token(end, |token| {
            std::mem::discriminant(token) == std::mem::discriminant(&keyword)
        }),
        style,
    );
    let open = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
        style,
    );
    let lhs = format_exp(lhs, cursor, style);
    let eq = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::EqEq)),
        style,
    );
    let rhs = format_exp(rhs, cursor, style);
    let close = format_gap_before(
        cursor.advance_to_token(end, |token| matches!(token, Token::RParen)),
        style,
    );
    ALLOC.concat([
        keyword_comments,
        ALLOC.text(name.to_string()),
        open,
        ALLOC.text("("),
        ALLOC
            .concat([
                lhs,
                eq,
                ALLOC
                    .concat([ALLOC.line(), ALLOC.text("== ")])
                    .flat_alt(ALLOC.text(" == ")),
                rhs,
            ])
            .nest(style.indent_width() as isize)
            .group(),
        close,
        ALLOC.text(")"),
    ])
}

fn format_exps_items(
    exps: &Exps<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Vec<Doc<'static>> {
    let mut items = Vec::new();
    for (index, exp) in exps.0.iter().enumerate() {
        let exp_doc = format_exp(exp, cursor, style);
        if index + 1 < exps.0.len() {
            items.push(comma_terminated_item(
                exp_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                style,
            ));
        } else {
            items.push(exp_doc);
        }
    }
    items
}

fn parenthesize(doc: Doc<'static>, needed: bool) -> Doc<'static> {
    if needed {
        ALLOC.concat([ALLOC.text("("), doc, ALLOC.text(")")])
    } else {
        doc
    }
}

fn comma_terminated_item(item: Doc<'static>, gap: TriviaGap, style: &Style) -> Doc<'static> {
    let sep = if gap.needs_line_break() {
        ALLOC.hardline()
    } else {
        ALLOC.line()
    };
    ALLOC.concat([item, ALLOC.text(","), format_gap_after(gap, sep, style)])
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

/// Build a rustfmt-style breakable delimited list.
///
/// Flat mode (fits on one line): `open item1, item2 close`
/// Broken mode (doesn't fit):
/// ```text
/// open
///     item1,
///     item2,
/// close
/// ```
fn delimited_list(
    open: &'static str,
    items: Vec<Doc<'static>>,
    close: &'static str,
    close_comments: TriviaGap,
    style: &Style,
) -> Doc<'static> {
    let indent = style.indent_width() as isize;
    let close_sep = if close_comments.needs_line_break() {
        ALLOC.hardline()
    } else {
        ALLOC.line_()
    };
    ALLOC
        .text(open)
        .append(
            ALLOC
                .concat([ALLOC
                    .concat([
                        ALLOC.line_(),
                        ALLOC.concat(items),
                        ALLOC.text(",").flat_alt(ALLOC.nil()),
                        format_gap_after(close_comments, close_sep, style),
                    ])
                    .nest(indent)])
                .group(),
        )
        .append(ALLOC.text(close))
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
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::Div => " / ",
        BinOp::Pow => " ^ ",
        BinOp::Dot => unreachable!(),
        BinOp::Concat => " ++ ",
        BinOp::Rem => " % ",
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
