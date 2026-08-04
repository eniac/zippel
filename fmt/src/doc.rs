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
use crate::trivia::{Comment, TokenCursor, TokenStream};

const ALLOC: BoxAllocator = BoxAllocator;
type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

pub fn format_decls(
    decls: &[Spanned<Decl<Size>>],
    tokens: &TokenStream,
    comments: &[Comment],
    line_starts: &[usize],
    src_len: usize,
    style: &Style,
) -> String {
    let mut cursor = TokenCursor::new(tokens, comments, line_starts);
    let mut parts = Vec::new();

    for (index, decl) in decls.iter().enumerate() {
        if index > 0 {
            parts.push(ALLOC.hardline());
            parts.push(ALLOC.hardline());
        }
        parts.push(cursor.advance_to(decl.span.start));
        parts.push(format_decl(decl, &mut cursor, style));
    }

    if !decls.is_empty() {
        parts.push(ALLOC.hardline());
    }
    parts.push(cursor.advance_to(src_len));

    let mut output = String::new();
    ALLOC
        .concat(parts)
        .1
        .render_fmt(style.width, &mut output)
        .expect("rendering failed");
    output.truncate(output.trim_end_matches('\n').len());
    output.push('\n');
    output
}

fn format_decl(
    decl: &Spanned<Decl<Size>>,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let end = decl.span.end;
    match &decl.node.body {
        Body::Proto { relation, body } => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwProto));
            let sig = format_sig(&decl.node.sig, cursor, end);
            let where_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::KwWhere));
            let relation = format_relation(relation, cursor);
            let open_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));
            let body = format_body_exp(body, cursor);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrace));
            ALLOC.concat([
                keyword,
                ALLOC.text("proto "),
                sig,
                where_comments,
                ALLOC.text(" where "),
                relation,
                open_comments,
                ALLOC.text(" {"),
                ALLOC.hardline(),
                body.indent(style.indent_width()),
                close_comments,
                ALLOC.hardline(),
                ALLOC.text("}"),
            ])
        }
        Body::Func { body } => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwFn));
            let sig = format_sig(&decl.node.sig, cursor, end);
            let ret = if let Some(ret) = &decl.node.sig.ret {
                let arrow = cursor.advance_to_token(end, |token| matches!(token, Token::Arrow));
                ALLOC.concat([
                    arrow,
                    ALLOC.text(" -> "),
                    format_typ(&ret.node, cursor, ret.span.end),
                ])
            } else {
                ALLOC.nil()
            };
            let open_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));
            let body = format_body_exp(body, cursor);
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
                body.indent(style.indent_width()),
                close_comments,
                ALLOC.hardline(),
                ALLOC.text("}"),
            ])
        }
        Body::TypeAlias => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwType));
            let name = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let eq = cursor.advance_to_token(end, |token| matches!(token, Token::Eq));
            let typ = decl
                .node
                .sig
                .ret
                .as_ref()
                .expect("type aliases have a type");
            let typ = format_typ(&typ.node, cursor, typ.span.end);
            let semi = cursor.advance_to_token(end, |token| matches!(token, Token::Semi));
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

fn format_sig(sig: &Sig<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    let name = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let typevar_open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
    let typevars = format_typevars(&sig.typevars.node, cursor, end);
    let typevar_close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
    let arg_open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));

    let mut args = Vec::new();
    for (index, arg) in sig.args.node.0.iter().enumerate() {
        args.push(format_arg(arg, cursor));
        if index + 1 < sig.args.node.0.len() {
            args.push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
            args.push(ALLOC.text(","));
            args.push(ALLOC.line());
        }
    }
    let args = ALLOC.concat(args).group();
    let arg_close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));

    ALLOC.concat([
        name,
        ALLOC.text(sig.name.node.to_string()),
        typevar_open,
        ALLOC.text("<"),
        typevars,
        typevar_close,
        ALLOC.text(">"),
        arg_open,
        ALLOC.text("("),
        args,
        arg_close,
        ALLOC.text(")"),
    ])
}

fn format_arg(arg: &Spanned<Arg<Tid, Size>>, cursor: &mut TokenCursor) -> Doc<'static> {
    let end = arg.span.end;
    let mut parts = Vec::new();
    let mut has_prefix = false;

    if !matches!(arg.node.qualifier, Qualifier::Local) {
        let qualifier = cursor.advance_to_token(end, |token| match arg.node.qualifier {
            Qualifier::Witness => matches!(token, Token::KwWitness),
            Qualifier::Extra => matches!(token, Token::KwExtra),
            Qualifier::Instance => matches!(token, Token::KwInstance),
            Qualifier::Local => false,
        });
        parts.push(qualifier);
        parts.push(ALLOC.text(qualifier_text(arg.node.qualifier)));
        has_prefix = true;
    }

    if !matches!(arg.node.distribution, Distribution::Nonuniform) {
        if has_prefix {
            parts.push(ALLOC.text(" "));
        }
        parts.push(cursor.advance_to_token(end, |token| matches!(token, Token::KwUniform)));
        parts.push(ALLOC.text("uniform"));
        if matches!(arg.node.distribution, Distribution::UniformNonZero) {
            parts.push(cursor.advance_to_token(end, |token| matches!(token, Token::Star)));
            parts.push(ALLOC.text("*"));
        }
        has_prefix = true;
    }

    if has_prefix {
        parts.push(ALLOC.text(" "));
    }
    parts.push(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
    parts.push(ALLOC.text(arg.node.id.to_string()));
    parts.push(cursor.advance_to_token(end, |token| matches!(token, Token::Colon)));
    parts.push(ALLOC.text(": "));
    parts.push(format_typ(&arg.node.typ, cursor, end));
    ALLOC.concat(parts)
}

fn format_typevars(
    typevars: &TypeVars<Size>,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let mut parts = Vec::new();
    for (index, typevar) in typevars.0.iter().enumerate() {
        parts.push(format_typevar(typevar, cursor));
        if index + 1 < typevars.0.len() {
            parts.push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
            parts.push(ALLOC.text(", "));
        }
    }
    ALLOC.concat(parts)
}

fn format_typevar(typevar: &Spanned<TypeVar<Size>>, cursor: &mut TokenCursor) -> Doc<'static> {
    let end = typevar.span.end;
    let id = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let colon = cursor.advance_to_token(end, |token| matches!(token, Token::Colon));
    let kind = format_kind(&typevar.node.kind, cursor, end);
    ALLOC.concat([
        id,
        ALLOC.text(typevar.node.id.to_string()),
        colon,
        ALLOC.text(": "),
        kind,
    ])
}

fn format_typ(typ: &GTyp<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    match typ {
        Typ::Poly(base, m, n) => {
            let keyword = cursor.advance_to_token(end, |token| {
                matches!(token, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
            });
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
            let base_comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let comma_one = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
            let m = format_size(m, cursor, end);
            let comma_two = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
            let n = format_size(n, cursor, end);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            ALLOC.concat([
                keyword,
                ALLOC.text("Poly"),
                open,
                ALLOC.text("<"),
                base_comments,
                ALLOC.text(base.to_string()),
                comma_one,
                ALLOC.text(", "),
                m,
                comma_two,
                ALLOC.text(", "),
                n,
                close,
                ALLOC.text(">"),
            ])
        }
        Typ::Vec(typ, size) => {
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let typ = format_typ(&typ.node, cursor, typ.span.end);
            let semi = cursor.advance_to_token(end, |token| matches!(token, Token::Semi));
            let size = format_size(size, cursor, end);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
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
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            ALLOC.concat([comments, ALLOC.text(base.to_string())])
        }
        Typ::Fin(range) => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwFin));
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
            let range = format_range(range, cursor, end);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
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
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::KwUnit));
            ALLOC.concat([comments, ALLOC.text("Unit")])
        }
        Typ::Record(fields) => {
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LBrace));
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, typ)| typ.span.start);
            let mut docs = Vec::new();
            for (index, (name, typ)) in fields.iter().enumerate() {
                docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
                docs.push(ALLOC.text(name.to_string()));
                docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Colon)));
                docs.push(ALLOC.text(": "));
                docs.push(format_typ(&typ.node, cursor, typ.span.end));
                if index + 1 < fields.len() {
                    docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
                    docs.push(ALLOC.text(", "));
                }
            }
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RBrace));
            ALLOC.concat([
                open,
                ALLOC.text("{"),
                ALLOC.concat(docs),
                close,
                ALLOC.text("}"),
            ])
        }
    }
}

fn format_kind(kind: &Kind<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    match kind {
        Kind::Field => {
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::KwField));
            ALLOC.concat([comments, ALLOC.text("Field")])
        }
        Kind::Group => {
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::KwGroup));
            ALLOC.concat([comments, ALLOC.text("Group")])
        }
        Kind::SizeVar => {
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::KwSize));
            ALLOC.concat([comments, ALLOC.text("Size")])
        }
        Kind::Scalar(ids) => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwScalar));
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
            let ids: Vec<_> = ids.iter().collect();
            let mut docs = Vec::new();
            for (index, id) in ids.iter().enumerate() {
                docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
                docs.push(ALLOC.text(id.to_string()));
                if index + 1 < ids.len() {
                    docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
                    docs.push(ALLOC.text(", "));
                }
            }
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            ALLOC.concat([
                keyword,
                ALLOC.text("Scalar"),
                open,
                ALLOC.text("<"),
                ALLOC.concat(docs),
                close,
                ALLOC.text(">"),
            ])
        }
        Kind::Pairing(g1, g2) => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwPairing));
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
            let first = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
            let second = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            ALLOC.concat([
                keyword,
                ALLOC.text("Pairing"),
                open,
                ALLOC.text("<"),
                first,
                ALLOC.text(g1.to_string()),
                comma,
                ALLOC.text(", "),
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
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            ALLOC.concat([comments, ALLOC.text(id.to_string())])
        }
        Size::Lit(value) => {
            let comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::Positive(_)));
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
    let op_comments = cursor.advance_to_token(end, |token| matches_size_op(op, token));
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
    let name_comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
    let lhs = format_size_spanned(lhs, cursor);
    let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
    let rhs = format_size_spanned(rhs, cursor);
    let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
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
        let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
        let step = format_range_size(step, cursor, end);
        let dots = cursor.advance_to_token(end, |token| matches!(token, Token::DotDot));
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
        let dots = cursor.advance_to_token(end, |token| matches!(token, Token::DotDot));
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

fn format_relation(exp: &Spanned<Exp<Size>>, cursor: &mut TokenCursor) -> Doc<'static> {
    match &exp.node {
        Exp::Assert(lhs, rhs) => {
            let lhs = format_exp(lhs, cursor);
            let eq = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::EqEq));
            let rhs = format_exp(rhs, cursor);
            ALLOC.concat([lhs, eq, ALLOC.text(" == "), rhs])
        }
        Exp::Let(Some(var), value, body) => {
            let keyword =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet));
            let name = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| ALLOC.concat([ALLOC.text("; "), format_relation(body, cursor)]))
                .unwrap_or_else(|| ALLOC.text(";"));
            ALLOC.concat([
                keyword,
                ALLOC.text("let "),
                name,
                ALLOC.text(var.to_string()),
                eq,
                ALLOC.text(" = "),
                value,
                semi,
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let value = format_relation(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| ALLOC.concat([ALLOC.text("; "), format_relation(body, cursor)]))
                .unwrap_or_else(|| ALLOC.text(";"));
            ALLOC.concat([value, semi, body])
        }
        _ => format_exp(exp, cursor),
    }
}

fn format_body_exp(exp: &Spanned<Exp<Size>>, cursor: &mut TokenCursor) -> Doc<'static> {
    match &exp.node {
        Exp::Let(Some(var), value, body) => {
            let keyword =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet));
            let name = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| format_body_exp(body, cursor))
                .unwrap_or_else(|| ALLOC.nil());
            ALLOC.concat([
                keyword,
                ALLOC.text("let "),
                name,
                ALLOC.text(var.to_string()),
                eq,
                ALLOC.text(" = "),
                value,
                semi,
                ALLOC.text(";"),
                ALLOC.hardline(),
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| format_body_exp(body, cursor))
                .unwrap_or_else(|| ALLOC.nil());
            ALLOC.concat([value, semi, ALLOC.text(";"), ALLOC.hardline(), body])
        }
        Exp::Log(var, value, body) => {
            let name = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let arrow =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::LArrow));
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| format_body_exp(body, cursor))
                .unwrap_or_else(|| ALLOC.nil());
            ALLOC.concat([
                name,
                ALLOC.text(var.to_string()),
                arrow,
                ALLOC.text(" <- "),
                value,
                semi,
                ALLOC.text(";"),
                ALLOC.hardline(),
                body,
            ])
        }
        _ => format_exp(exp, cursor),
    }
}

fn format_exp(exp: &Spanned<Exp<Size>>, cursor: &mut TokenCursor) -> Doc<'static> {
    let end = exp.span.end;
    match &exp.node {
        Exp::Lit(value) => format_size(value, cursor, end),
        Exp::Unit => {
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            ALLOC.concat([open, ALLOC.text("("), close, ALLOC.text(")")])
        }
        Exp::Var(var) => {
            let comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            ALLOC.concat([comments, ALLOC.text(var.to_string())])
        }
        Exp::Neg(inner) => {
            let minus = cursor.advance_to_token(end, |token| matches!(token, Token::Minus));
            let inner = parenthesize(format_exp(inner, cursor), neg_needs_paren(&inner.node));
            ALLOC.concat([minus, ALLOC.text("-"), inner])
        }
        Exp::Bin(BinOp::Dot, lhs, rhs) => format_binary_call("dot", lhs, rhs, cursor, end),
        Exp::Bin(op, lhs, rhs) => {
            let lhs = parenthesize(format_exp(lhs, cursor), lhs_needs_paren(*op, &lhs.node));
            let op_comments = cursor.advance_to_token(end, |token| matches_binop(*op, token));
            let rhs = parenthesize(format_exp(rhs, cursor), rhs_needs_paren(*op, &rhs.node));
            ALLOC.concat([lhs, op_comments, ALLOC.text(binop_text(*op)), rhs])
        }
        Exp::App(function, args) => {
            let function_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let args = format_exps(args, cursor, end);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            ALLOC.concat([
                function_comments,
                ALLOC.text(function.to_string()),
                open,
                ALLOC.text("("),
                args,
                close,
                ALLOC.text(")"),
            ])
        }
        Exp::Interpolate(None, evals) => format_unary_call(
            "interpolate",
            |token| matches!(token, Token::KwInterpolate),
            evals,
            cursor,
            end,
        ),
        Exp::Interpolate(Some(points), evals) => {
            format_binary_call("interpolate", points, evals, cursor, end)
        }
        Exp::Poly(value) => format_unary_call(
            "poly",
            |token| matches!(token, Token::KwPoly),
            value,
            cursor,
            end,
        ),
        Exp::Coef(value) => format_unary_call(
            "coef",
            |token| matches!(token, Token::KwCoef),
            value,
            cursor,
            end,
        ),
        Exp::Mle(value) => format_unary_call(
            "mle",
            |token| matches!(token, Token::KwMle),
            value,
            cursor,
            end,
        ),
        Exp::Evaluate(poly, range, point) => {
            format_evaluate(poly, range.as_ref(), point.as_deref(), cursor, end)
        }
        Exp::Vec(values) => {
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let values = format_exps(values, cursor, end);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            ALLOC.concat([open, ALLOC.text("["), values, close, ALLOC.text("]")])
        }
        Exp::Range(range) => format_range(range, cursor, end),
        Exp::Map(body, var, range) => {
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let body = format_exp(body, cursor);
            let for_comments = cursor.advance_to_token(end, |token| matches!(token, Token::KwFor));
            let var_comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let in_comments = cursor.advance_to_token(end, |token| matches!(token, Token::KwIn));
            let range = format_exp(range, cursor);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            ALLOC.concat([
                open,
                ALLOC.text("["),
                body,
                for_comments,
                ALLOC.text(" for "),
                var_comments,
                ALLOC.text(var.to_string()),
                in_comments,
                ALLOC.text(" in "),
                range,
                close,
                ALLOC.text("]"),
            ])
        }
        Exp::Reduce(op, value) => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwReduce));
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let op_comments = cursor.advance_to_token(end, |token| matches_binop(*op, token));
            let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
            let value = format_exp(value, cursor);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            ALLOC.concat([
                keyword,
                ALLOC.text("reduce"),
                open,
                ALLOC.text("("),
                op_comments,
                ALLOC.text(binop_symbol(*op)),
                comma,
                ALLOC.text(", "),
                value,
                close,
                ALLOC.text(")"),
            ])
        }
        Exp::Ram(base, index) => {
            let base = format_exp(base, cursor);
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LBrack));
            let index = format_exp(index, cursor);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));
            ALLOC.concat([base, open, ALLOC.text("["), index, close, ALLOC.text("]")])
        }
        Exp::Pair(lhs, rhs) => format_binary_call("pair", lhs, rhs, cursor, end),
        Exp::Random(typ, star) => {
            format_sampling("random", Token::KwRandom, typ, *star, cursor, end)
        }
        Exp::Challenge(typ, star) => {
            format_sampling("challenge", Token::KwChallenge, typ, *star, cursor, end)
        }
        Exp::Let(_, _, _) | Exp::Log(_, _, _) => format_exp_chain(exp, cursor),
        Exp::Assert(lhs, rhs) => format_assertion("assert", Token::KwAssert, lhs, rhs, cursor, end),
        Exp::Verify(lhs, rhs) => format_assertion("verify", Token::KwVerify, lhs, rhs, cursor, end),
        Exp::Fun(vars, body) => {
            let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwFun));
            let mut var_docs = Vec::new();
            for (index, var) in vars.iter().enumerate() {
                var_docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
                var_docs.push(ALLOC.text(var.to_string()));
                if index + 1 < vars.len() {
                    var_docs
                        .push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
                    var_docs.push(ALLOC.text(", "));
                }
            }
            let arrow = cursor.advance_to_token(end, |token| matches!(token, Token::FatArrow));
            let body = format_exp(body, cursor);
            ALLOC.concat([
                keyword,
                ALLOC.text("fun "),
                ALLOC.concat(var_docs),
                arrow,
                ALLOC.text(" => "),
                body,
            ])
        }
        Exp::Record(fields) => {
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LBraceBar));
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_by_key(|(_, value)| value.span.start);
            let mut docs = Vec::new();
            for (index, (name, value)) in fields.iter().enumerate() {
                docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Id(_))));
                docs.push(ALLOC.text(name.to_string()));
                docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Colon)));
                docs.push(ALLOC.text(": "));
                docs.push(format_exp(value, cursor));
                if index + 1 < fields.len() {
                    docs.push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
                    docs.push(ALLOC.text(", "));
                }
            }
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::BarRBrace));
            ALLOC.concat([
                open,
                ALLOC.text("{|"),
                ALLOC.concat(docs),
                close,
                ALLOC.text("|}"),
            ])
        }
        Exp::Proj(base, field) => {
            let base = format_exp(base, cursor);
            let dot = cursor.advance_to_token(end, |token| matches!(token, Token::Dot));
            let field_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            ALLOC.concat([
                base,
                dot,
                ALLOC.text("."),
                field_comments,
                ALLOC.text(field.to_string()),
            ])
        }
        Exp::SetRecord(record, field, value) => {
            let record = format_exp(record, cursor);
            let dot = cursor.advance_to_token(end, |token| matches!(token, Token::Dot));
            let set = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
            let field_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
            let value = format_exp(value, cursor);
            let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
            ALLOC.concat([
                record,
                dot,
                ALLOC.text("."),
                set,
                ALLOC.text("set"),
                open,
                ALLOC.text("("),
                field_comments,
                ALLOC.text(field.to_string()),
                comma,
                ALLOC.text(", "),
                value,
                close,
                ALLOC.text(")"),
            ])
        }
    }
}

fn format_exp_chain(exp: &Spanned<Exp<Size>>, cursor: &mut TokenCursor) -> Doc<'static> {
    match &exp.node {
        Exp::Let(Some(var), value, body) => {
            let keyword =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::KwLet));
            let name = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let eq = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Eq));
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| ALLOC.concat([ALLOC.text("; "), format_exp_chain(body, cursor)]))
                .unwrap_or_else(|| ALLOC.text(";"));
            ALLOC.concat([
                keyword,
                ALLOC.text("let "),
                name,
                ALLOC.text(var.to_string()),
                eq,
                ALLOC.text(" = "),
                value,
                semi,
                body,
            ])
        }
        Exp::Let(None, value, body) => {
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| ALLOC.concat([ALLOC.text("; "), format_exp_chain(body, cursor)]))
                .unwrap_or_else(|| ALLOC.text(";"));
            ALLOC.concat([value, semi, body])
        }
        Exp::Log(var, value, body) => {
            let name = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Id(_)));
            let arrow =
                cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::LArrow));
            let value = format_exp(value, cursor);
            let semi = cursor.advance_to_token(exp.span.end, |token| matches!(token, Token::Semi));
            let body = body
                .as_ref()
                .map(|body| ALLOC.concat([ALLOC.text("; "), format_exp_chain(body, cursor)]))
                .unwrap_or_else(|| ALLOC.text(";"));
            ALLOC.concat([
                name,
                ALLOC.text(var.to_string()),
                arrow,
                ALLOC.text(" <- "),
                value,
                semi,
                body,
            ])
        }
        _ => format_exp(exp, cursor),
    }
}

fn format_unary_call(
    name: &str,
    pred: impl Fn(&Token) -> bool,
    arg: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let keyword = cursor.advance_to_token(end, pred);
    let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
    let arg = format_exp(arg, cursor);
    let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    ALLOC.concat([
        keyword,
        ALLOC.text(name.to_string()),
        open,
        ALLOC.text("("),
        arg,
        close,
        ALLOC.text(")"),
    ])
}

fn format_binary_call(
    name: &str,
    lhs: &Spanned<Exp<Size>>,
    rhs: &Spanned<Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let keyword = cursor.advance_to_token(end, |token| {
        matches!(
            token,
            Token::Id(_) | Token::KwInterpolate | Token::KwPair | Token::KwDot
        )
    });
    let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
    let lhs = format_exp(lhs, cursor);
    let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
    let rhs = format_exp(rhs, cursor);
    let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    ALLOC.concat([
        keyword,
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

fn format_evaluate(
    poly: &Spanned<Exp<Size>>,
    range: Option<&Range<Size>>,
    point: Option<&Spanned<Exp<Size>>>,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let keyword = cursor.advance_to_token(end, |token| matches!(token, Token::KwEval));
    let selector = if let Some(range) = range {
        let open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
        let range = format_range(range, cursor, end);
        let close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
        ALLOC.concat([open, ALLOC.text("<"), range, close, ALLOC.text(">")])
    } else {
        ALLOC.nil()
    };
    let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
    let poly = format_exp(poly, cursor);
    let point = if let Some(point) = point {
        let comma = cursor.advance_to_token(end, |token| matches!(token, Token::Comma));
        ALLOC.concat([comma, ALLOC.text(", "), format_exp(point, cursor)])
    } else {
        ALLOC.nil()
    };
    let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
    ALLOC.concat([
        keyword,
        ALLOC.text("eval"),
        selector,
        open,
        ALLOC.text("("),
        poly,
        point,
        close,
        ALLOC.text(")"),
    ])
}

fn format_sampling(
    name: &str,
    keyword: Token<'static>,
    typ: &Tid,
    star: bool,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let keyword_comments = cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    });
    let open = cursor.advance_to_token(end, |token| matches!(token, Token::LAngle));
    let typ_comments = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
    let star = if star {
        let comments = cursor.advance_to_token(end, |token| matches!(token, Token::Star));
        ALLOC.concat([comments, ALLOC.text("*")])
    } else {
        ALLOC.nil()
    };
    let close = cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
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
) -> Doc<'static> {
    let keyword_comments = cursor.advance_to_token(end, |token| {
        std::mem::discriminant(token) == std::mem::discriminant(&keyword)
    });
    let open = cursor.advance_to_token(end, |token| matches!(token, Token::LParen));
    let lhs = format_exp(lhs, cursor);
    let eq = cursor.advance_to_token(end, |token| matches!(token, Token::EqEq));
    let rhs = format_exp(rhs, cursor);
    let close = cursor.advance_to_token(end, |token| matches!(token, Token::RParen));
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

fn format_exps(exps: &Exps<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    let mut parts = Vec::new();
    for (index, exp) in exps.0.iter().enumerate() {
        parts.push(format_exp(exp, cursor));
        if index + 1 < exps.0.len() {
            parts.push(cursor.advance_to_token(end, |token| matches!(token, Token::Comma)));
            parts.push(ALLOC.text(", "));
        }
    }
    ALLOC.concat(parts)
}

fn parenthesize(doc: Doc<'static>, needed: bool) -> Doc<'static> {
    if needed {
        ALLOC.concat([ALLOC.text("("), doc, ALLOC.text(")")])
    } else {
        doc
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
