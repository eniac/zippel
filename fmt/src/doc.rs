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
    Comment, TokenCursor, TokenStream, TriviaGap, format_delimiter_gap, format_leading_gap,
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
        if index > 0 {
            parts.push(hardlines(1 + style.max_blank_lines));
        }
        parts.push(format_leading_gap(cursor.advance_to(decl.span.start)));
        parts.push(format_decl(decl, &mut cursor, style));
    }

    if !decls.is_empty() {
        parts.push(ALLOC.hardline());
    }
    parts.push(format_leading_gap(cursor.advance_to(src_len)));

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
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwProto)),
            );
            let sig = format_sig(&decl.node.sig, cursor, end, style);
            let where_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwWhere)),
            );
            let relation = format_relation(relation, cursor, style);
            let open_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrace)),
            );
            let body = format_body_exp(body, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrace));
            ALLOC.concat([
                keyword,
                ALLOC.text("proto "),
                sig,
                where_comments,
                ALLOC.text(" where"),
                ALLOC.hardline(),
                relation.indent(style.indent_width()),
                open_comments,
                ALLOC.hardline(),
                ALLOC.text("{"),
                ALLOC.hardline(),
                ALLOC
                    .concat([body, format_delimiter_gap(close_comments, ALLOC.hardline())])
                    .indent(style.indent_width()),
                ALLOC.text("}"),
            ])
        }
        Body::Func { body } => {
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFn)),
            );
            let sig = format_sig(&decl.node.sig, cursor, end, style);
            let ret = if let Some(ret) = &decl.node.sig.ret {
                let arrow = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Arrow)),
                );
                ALLOC.concat([
                    arrow,
                    ALLOC.text(" -> "),
                    format_typ(&ret.node, cursor, ret.span.end, style),
                ])
            } else {
                ALLOC.nil()
            };
            let open_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrace)),
            );
            let body = format_body_exp(body, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrace));
            ALLOC.concat([
                keyword,
                ALLOC.text("fn "),
                sig,
                ret,
                open_comments,
                ALLOC.text(" {"),
                ALLOC.hardline(),
                ALLOC
                    .concat([body, format_delimiter_gap(close_comments, ALLOC.hardline())])
                    .indent(style.indent_width()),
                ALLOC.text("}"),
            ])
        }
        Body::TypeAlias => {
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwType)),
            );
            let name = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let eq = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Eq)),
            );
            let typ = decl
                .node
                .sig
                .ret
                .as_ref()
                .expect("type aliases have a type");
            let typ = format_typ(&typ.node, cursor, typ.span.end, style);
            let semi = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Semi)),
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
    let name =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
    let typevar_open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)));
    let typevars = format_typevars(&sig.typevars.node, cursor, end, style);
    let typevar_close =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)));
    let arg_open_comments =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LParen)));

    let mut args = Vec::new();
    // Find the `)` position to limit trailing comma search for the last arg.
    let rparen_end = cursor.peek_token(end, |token| matches!(token, Token::RParen));
    for (index, arg) in sig.args.node.0.iter().enumerate() {
        let arg_doc = format_arg(arg, cursor, style);
        if index + 1 < sig.args.node.0.len() {
            args.push(comma_terminated_item(
                arg_doc,
                take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
            ));
        } else {
            // Last arg: consume trailing comma comments only if a comma exists before `)`.
            if let Some(rp_end) = &rparen_end {
                let comma_comments = format_leading_gap(
                    cursor.advance_to_token(rp_end.end, |token| matches!(token, Token::Comma)),
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
        let qualifier =
            format_leading_gap(
                cursor.advance_to_token(end, |token| match arg.node.qualifier {
                    Qualifier::Witness => matches!(token, Token::KwWitness),
                    Qualifier::Extra => matches!(token, Token::KwExtra),
                    Qualifier::Instance => matches!(token, Token::KwInstance),
                    Qualifier::Local => false,
                }),
            );
        parts.push(qualifier);
        parts.push(ALLOC.text(qualifier_text(arg.node.qualifier)));
        has_prefix = true;
    }

    if !matches!(arg.node.distribution, Distribution::Nonuniform) {
        if has_prefix {
            parts.push(ALLOC.text(" "));
        }
        parts.push(format_leading_gap(
            cursor.advance_to_token(end, |token| matches!(token, Token::KwUniform)),
        ));
        parts.push(ALLOC.text("uniform"));
        if matches!(arg.node.distribution, Distribution::UniformNonZero) {
            parts.push(format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Star)),
            ));
            parts.push(ALLOC.text("*"));
        }
        has_prefix = true;
    }

    if has_prefix {
        parts.push(ALLOC.text(" "));
    }
    parts.push(format_leading_gap(
        cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
    ));
    parts.push(ALLOC.text(arg.node.id.to_string()));
    parts.push(format_leading_gap(
        cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
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
    let id =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
    let colon =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Colon)));
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
            let keyword = format_leading_gap(cursor.advance_to_token(end, |token| {
                matches!(token, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
            }));
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
            );
            let base_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let comma_one = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let m = format_size(m, cursor, end);
            let comma_two = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let n = format_size(n, cursor, end);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            let items = vec![
                comma_terminated_item(
                    ALLOC.concat([base_comments, ALLOC.text(base.to_string())]),
                    comma_one,
                ),
                comma_terminated_item(m, comma_two),
                n,
            ];
            ALLOC.concat([
                keyword,
                ALLOC.text("Poly"),
                open,
                ALLOC.text("<"),
                delimited_list("", items, "", close_comments, style),
                ALLOC.text(">"),
            ])
        }
        Typ::Vec(typ, size) => {
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
            );
            let typ = format_typ(&typ.node, cursor, typ.span.end, style);
            let semi = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Semi)),
            );
            let size = format_size(size, cursor, end);
            let close = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack)),
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
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            ALLOC.concat([comments, ALLOC.text(base.to_string())])
        }
        Typ::Fin(range) => {
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFin)),
            );
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
            );
            let range = format_range(range, cursor, end);
            let close = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
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
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwUnit)),
            );
            ALLOC.concat([comments, ALLOC.text("Unit")])
        }
        Typ::Record(fields) => {
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrace)),
            );
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, typ)| typ.span.start);
            let mut items = Vec::new();
            for (index, (name, typ)) in fields.iter().enumerate() {
                let name_comments = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                );
                let colon = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
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
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwField)),
            );
            ALLOC.concat([comments, ALLOC.text("Field")])
        }
        Kind::Group => {
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwGroup)),
            );
            ALLOC.concat([comments, ALLOC.text("Group")])
        }
        Kind::SizeVar => {
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwSize)),
            );
            ALLOC.concat([comments, ALLOC.text("Size")])
        }
        Kind::Scalar(ids) => {
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwScalar)),
            );
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
            );
            let ids: Vec<_> = ids.iter().collect();
            let mut items = Vec::new();
            for (index, id) in ids.iter().enumerate() {
                let id_comments = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                );
                let id_doc = ALLOC.concat([id_comments, ALLOC.text(id.to_string())]);
                if index + 1 < ids.len() {
                    items.push(comma_terminated_item(
                        id_doc,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
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
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwPairing)),
            );
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
            );
            let first = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let second = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let close = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
            );
            ALLOC.concat([
                keyword,
                ALLOC.text("Pairing"),
                open,
                ALLOC.text("<"),
                first,
                ALLOC.text(g1.to_string()),
                ALLOC.text(","),
                {
                    let sep = if comma.needs_line_break() {
                        ALLOC.hardline()
                    } else {
                        ALLOC.text(" ")
                    };
                    format_delimiter_gap(comma, sep)
                },
                second,
                ALLOC.text(g2.to_string()),
                close,
                ALLOC.text(">"),
            ])
        }
        Kind::Range(range) => format_range(range, cursor, end),
    }
}

fn format_size_spanned(size: &Spanned<Size>, cursor: &mut TokenCursor) -> Doc<'static> {
    format_size(&size.node, cursor, size.span.end)
}

fn format_size(size: &Size, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    match size {
        Size::Var(id) => {
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            ALLOC.concat([comments, ALLOC.text(id.to_string())])
        }
        Size::Lit(value) => {
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_))),
            );
            ALLOC.concat([comments, ALLOC.text(value.to_string())])
        }
        Size::Add(lhs, rhs) => format_size_binary(lhs, rhs, "+", cursor, end),
        Size::Sub(lhs, rhs) => format_size_binary(lhs, rhs, "-", cursor, end),
        Size::Mul(lhs, rhs) => format_size_binary(lhs, rhs, "*", cursor, end),
        Size::Div(lhs, rhs) => format_size_binary(lhs, rhs, "/", cursor, end),
        Size::Pow(lhs, rhs) => format_size_binary(lhs, rhs, "^", cursor, end),
        Size::Max(lhs, rhs) => format_size_call("max", lhs, rhs, cursor, end),
        Size::Min(lhs, rhs) => format_size_call("min", lhs, rhs, cursor, end),
    }
}

fn format_size_binary(
    lhs: &Spanned<Size>,
    rhs: &Spanned<Size>,
    op: &str,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let (precedence, right_assoc) = match op {
        "+" | "-" => (1, false),
        "*" | "/" => (2, false),
        "^" => (3, true),
        _ => unreachable!(),
    };
    let lhs = parenthesize(
        format_size_spanned(lhs, cursor),
        size_lhs_needs_paren(&lhs.node, precedence, right_assoc),
    );
    let op_comments =
        format_leading_gap(cursor.advance_to_token(end, |token| matches_size_op(op, token)));
    let rhs = parenthesize(
        format_size_spanned(rhs, cursor),
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
) -> Doc<'static> {
    let name_comments =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
    let open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LParen)));
    let lhs = format_size_spanned(lhs, cursor);
    let comma =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
    let rhs = format_size_spanned(rhs, cursor);
    let close =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::RParen)));
    ALLOC.concat([
        name_comments,
        ALLOC.text(name.to_string()),
        open,
        ALLOC.text("("),
        lhs,
        comma,
        ALLOC.text(", "),
        rhs,
        close,
        ALLOC.text(")"),
    ])
}

fn format_range(range: &Range<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    let start = format_range_size(&range.start, cursor, end);
    if let Some(step) = &range.step {
        let comma =
            format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
        let step = format_range_size(step, cursor, end);
        let dots = format_leading_gap(
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
        );
        let last = range.end.as_ref().expect("stepped ranges have an end");
        let last = format_range_size(last, cursor, end);
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
        let dots = format_leading_gap(
            cursor.advance_to_token(end, |token| matches!(token, Token::DotDot)),
        );
        let last = format_range_size(last, cursor, end);
        ALLOC.concat([start, dots, ALLOC.text(".."), last])
    } else {
        start
    }
}

fn format_range_size(size: &Spanned<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    if size.span.start == size.span.end {
        format_size(&size.node, cursor, end)
    } else {
        format_size_spanned(size, cursor)
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
            let eq = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::EqEq)),
            );
            let rhs = format_exp(rhs, cursor, style);
            ALLOC.concat([lhs, eq, ALLOC.text(" == "), rhs])
        }
        Exp::Let(Some(var), value, body) => {
            let keyword = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
            );
            let name = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
            );
            let eq = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq)),
            );
            let value = format_exp(value, cursor, style);
            let body = if let Some(body) = body.as_ref() {
                let semi_gap =
                    take_separator_gap(cursor, exp.span.end, |token| matches!(token, Token::Semi));
                ALLOC.concat([
                    format_delimiter_gap(semi_gap, ALLOC.hardline()),
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
                format_delimiter_gap(before_semi, sep)
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
                    format_delimiter_gap(semi_gap, ALLOC.hardline()),
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
                format_delimiter_gap(before_semi, sep)
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
            let keyword = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet)),
            );
            let name = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
            );
            let eq = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq)),
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
            let name = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_))),
            );
            let arrow = format_leading_gap(
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::LArrow)),
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
        return format_delimiter_gap(before_semi, sep);
    };

    let semi_end = cursor.position();
    let blank_lines = cursor.blank_lines_between(semi_end, body.span.start);
    let block_start = blank_lines.first().copied();
    let cutoff = block_start.unwrap_or(body.span.start);
    let after_semi = cursor.advance_to(cutoff);
    let gap = before_semi.join(after_semi);
    let separator = if block_start.is_some() {
        hardlines(1 + blank_lines.len().min(style.max_blank_lines))
    } else {
        ALLOC.hardline()
    };
    ALLOC.concat([
        format_delimiter_gap(gap, separator),
        format_body_exp(body, cursor, style),
    ])
}

fn hardlines(count: usize) -> Doc<'static> {
    ALLOC.concat((0..count).map(|_| ALLOC.hardline()))
}

fn format_exp(exp: &Spanned<Exp<Size>>, cursor: &mut TokenCursor, style: &Style) -> Doc<'static> {
    let end = exp.span.end;
    match &exp.node {
        Exp::Lit(value) => format_size(value, cursor, end),
        Exp::Unit => {
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
            );
            let close = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen)),
            );
            ALLOC.concat([open, ALLOC.text("("), close, ALLOC.text(")")])
        }
        Exp::Var(var) => {
            let comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            ALLOC.concat([comments, ALLOC.text(var.to_string())])
        }
        Exp::Neg(inner) => {
            let minus = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Minus)),
            );
            let inner = parenthesize(
                format_exp(inner, cursor, style),
                neg_needs_paren(&inner.node),
            );
            ALLOC.concat([minus, ALLOC.text("-"), inner.group()])
        }
        Exp::Bin(BinOp::Dot, lhs, rhs) => format_binary_call("dot", lhs, rhs, cursor, end, style),
        Exp::Bin(op, lhs, rhs) => {
            let lhs = parenthesize(
                format_exp(lhs, cursor, style),
                lhs_needs_paren(*op, &lhs.node),
            );
            let op_comments =
                format_leading_gap(cursor.advance_to_token(end, |token| matches_binop(*op, token)));
            let rhs = parenthesize(
                format_exp(rhs, cursor, style),
                rhs_needs_paren(*op, &rhs.node),
            );
            ALLOC
                .concat([
                    lhs,
                    op_comments,
                    ALLOC
                        .concat([ALLOC.line(), ALLOC.text(binop_symbol(*op)), ALLOC.text(" ")])
                        .flat_alt(ALLOC.text(binop_text(*op))),
                    rhs,
                ])
                .nest(style.indent_width() as isize)
                .group()
        }
        Exp::App(function, args) => {
            let function_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
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
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
            );
            let items = format_exps_items(values, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            let values = delimited_list("[", items, "]", close_comments, style);
            ALLOC.concat([open, values])
        }
        Exp::Range(range) => format_range(range, cursor, end),
        Exp::Map(body, var, range) => {
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
            );
            let body = format_exp(body, cursor, style);
            let for_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFor)),
            );
            let var_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let in_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwIn)),
            );
            let range = format_exp(range, cursor, style);
            let close = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack)),
            );
            ALLOC.concat([
                open,
                ALLOC.text("["),
                ALLOC
                    .concat([
                        body,
                        for_comments,
                        ALLOC.line().flat_alt(ALLOC.text(" ")),
                        ALLOC.text("for "),
                        var_comments,
                        ALLOC.text(var.to_string()),
                        in_comments,
                        ALLOC.text(" in "),
                        range,
                    ])
                    .nest(style.indent_width() as isize)
                    .group(),
                close,
                ALLOC.text("]"),
            ])
        }
        Exp::Reduce(op, value) => {
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwReduce)),
            );
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
            );
            let op_comments =
                format_leading_gap(cursor.advance_to_token(end, |token| matches_binop(*op, token)));
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let value = format_exp(value, cursor, style);
            let close = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen)),
            );
            ALLOC.concat([
                keyword,
                ALLOC.text("reduce"),
                open,
                ALLOC.text("("),
                op_comments,
                ALLOC.text(binop_symbol(*op)),
                ALLOC.text(","),
                {
                    let sep = if comma.needs_line_break() {
                        ALLOC.hardline()
                    } else {
                        ALLOC.text(" ")
                    };
                    format_delimiter_gap(comma, sep)
                },
                value,
                close,
                ALLOC.text(")"),
            ])
        }
        Exp::Ram(base, index) => {
            let base = format_exp(base, cursor, style);
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrack)),
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
            let keyword = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::KwFun)),
            );
            let mut items = Vec::new();
            for (index, var) in vars.iter().enumerate() {
                let var_comments = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                );
                let var_doc = ALLOC.concat([var_comments, ALLOC.text(var.to_string())]);
                if index + 1 < vars.len() {
                    items.push(comma_terminated_item(
                        var_doc,
                        take_separator_gap(cursor, end, |token| matches!(token, Token::Comma)),
                    ));
                } else {
                    items.push(var_doc);
                }
            }
            let arrow = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::FatArrow)),
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
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LBraceBar)),
            );
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, value)| value.span.start);
            let mut items = Vec::new();
            for (index, (name, value)) in fields.iter().enumerate() {
                let name_comments = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
                );
                let colon = format_leading_gap(
                    cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
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
            let dot = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Dot)),
            );
            let field_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
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
            let dot = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Dot)),
            );
            let set = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let open = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::LParen)),
            );
            let field_comments = format_leading_gap(
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))),
            );
            let comma = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
            let value = format_exp(value, cursor, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            let items = vec![
                comma_terminated_item(
                    ALLOC.concat([field_comments, ALLOC.text(field.to_string())]),
                    comma,
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
    let keyword = format_leading_gap(cursor.advance_to_token(end, pred));
    let open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LParen)));
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
    let keyword = format_leading_gap(cursor.advance_to_token(end, |token| {
        matches!(
            token,
            Token::Id(_) | Token::KwInterpolate | Token::KwPair | Token::KwDot
        )
    }));
    let open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LParen)));
    let lhs_doc = format_exp(lhs, cursor, style);
    let comma_comments = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
    let rhs_doc = format_exp(rhs, cursor, style);
    let close_comments = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    let items = vec![comma_terminated_item(lhs_doc, comma_comments), rhs_doc];
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
    let keyword =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::KwEval)));
    let selector = if let Some(range) = range {
        let open = format_leading_gap(
            cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
        );
        let range = format_range(range, cursor, end);
        let close = format_leading_gap(
            cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)),
        );
        ALLOC.concat([open, ALLOC.text("<"), range, close, ALLOC.text(">")])
    } else {
        ALLOC.nil()
    };
    let open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LParen)));
    let poly_doc = format_exp(poly, cursor, style);
    let mut items = Vec::new();
    if let Some(point) = point {
        let comma_comments = take_separator_gap(cursor, end, |token| matches!(token, Token::Comma));
        items.push(comma_terminated_item(poly_doc, comma_comments));
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
    _style: &Style,
) -> Doc<'static> {
    let keyword_comments = format_leading_gap(cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    }));
    let open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)));
    let typ_comments =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
    let star = if star {
        let comments =
            format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::Star)));
        ALLOC.concat([comments, ALLOC.text("*")])
    } else {
        ALLOC.nil()
    };
    let close =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::RAngle)));
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
    let keyword_comments = format_leading_gap(cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    }));
    let open =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::LParen)));
    let lhs = format_exp(lhs, cursor, style);
    let eq = format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::EqEq)));
    let rhs = format_exp(rhs, cursor, style);
    let close =
        format_leading_gap(cursor.advance_to_token(end, |token| matches!(token, Token::RParen)));
    ALLOC.concat([
        keyword_comments,
        ALLOC.text(name.to_string()),
        open,
        ALLOC.text("("),
        lhs,
        eq,
        ALLOC.text(" == "),
        rhs,
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

fn comma_terminated_item(item: Doc<'static>, gap: TriviaGap) -> Doc<'static> {
    let sep = if gap.needs_line_break() {
        ALLOC.hardline()
    } else {
        ALLOC.line()
    };
    ALLOC.concat([item, ALLOC.text(","), format_delimiter_gap(gap, sep)])
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
    open: &str,
    items: Vec<Doc<'static>>,
    close: &str,
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
        .text(open.to_string())
        .append(
            ALLOC
                .concat([ALLOC
                    .concat([
                        ALLOC.line_(),
                        ALLOC.concat(items),
                        ALLOC.text(",").flat_alt(ALLOC.nil()),
                        format_delimiter_gap(close_comments, close_sep),
                    ])
                    .nest(indent)])
                .group(),
        )
        .append(ALLOC.text(close.to_string()))
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
