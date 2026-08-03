//! Wadler doc builders for the Zippel AST.
//!
//! Each builder produces a `DocBuilder` for a canonical-style rendering.
//! Uses `pretty` crate's `group`/`nest`/`line` for width-aware layout.
//!
//! Comment handling uses a `TokenCursor` that wraps the `TokenStream` and
//! `CommentMap`. As format functions emit tokens left-to-right, they advance
//! the cursor, which automatically emits comments before each token. This
//! centralizes all comment handling in the cursor.

use lang::ast::Size;
use lang::ast::exp::{BinOp, Exp, Exps};
use lang::ast::sig::Sig;
use lang::typ::{Distribution, GTyp, Kind, Qualifier, Range, Typ, TypeVar, TypeVars};
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

use crate::paren::{lhs_needs_paren, rhs_needs_paren};
use crate::style::Style;
use crate::trivia::{
    Comment, CommentAttachment, CommentMap, CstBody, CstDecl, CstExp, TokenCursor, TokenStream,
};
use lang::parser::Token;

type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

const ALLOC: BoxAllocator = BoxAllocator;

/// Format a list of CST declarations into a single document.
pub fn format_decls(
    cst: &[CstDecl],
    comment_map: &CommentMap,
    tokens: &TokenStream,
    file_leading: &[Comment],
    file_trailing: &[Comment],
    style: &Style,
) -> String {
    let mut docs = Vec::with_capacity(cst.len());

    // File-level leading comments.
    if !file_leading.is_empty() {
        docs.push(format_comment_group(file_leading));
    }

    for cstd in cst {
        let mut cursor = TokenCursor::new(tokens, comment_map);
        docs.push(format_cst_decl(cstd, &mut cursor, style));
    }

    // File-level trailing comments.
    if !file_trailing.is_empty() {
        docs.push(format_comment_group(file_trailing));
    }

    // Join declarations with exactly one blank line between them.
    let body = ALLOC.intersperse(docs, ALLOC.concat([ALLOC.hardline(), ALLOC.hardline()]));

    // Trailing newline.
    let mut output = String::new();
    ALLOC
        .concat([body, ALLOC.hardline()])
        .1
        .render_fmt(style.width, &mut output)
        .expect("rendering failed");
    output
}

/// Format a group of comments (one per line).
fn format_comment_group(comments: &[Comment]) -> Doc<'static> {
    let docs: Vec<_> = comments
        .iter()
        .map(|c| ALLOC.text(c.text.clone()))
        .collect();
    ALLOC.intersperse(docs, ALLOC.hardline())
}

/// Format leading comments + hardline.
fn format_leading(attachment: &CommentAttachment) -> Doc<'static> {
    if attachment.leading.is_empty() {
        ALLOC.nil()
    } else {
        ALLOC.concat([format_comment_group(&attachment.leading), ALLOC.hardline()])
    }
}

/// Format trailing comment (same line, after node).
fn format_trailing(attachment: &CommentAttachment) -> Doc<'static> {
    match &attachment.trailing {
        Some(c) => ALLOC.concat([ALLOC.text(" "), ALLOC.text(c.text.clone())]),
        None => ALLOC.nil(),
    }
}

// ── Declarations ──────────────────────────────────────────────────────

/// Format a single CST declaration.
fn format_cst_decl(cstd: &CstDecl, cursor: &mut TokenCursor, style: &Style) -> Doc<'static> {
    let decl = &cstd.decl.node;
    let span = &cstd.decl.span;
    let end = span.end;
    let indent = style.indent_width();

    let decl_doc = match &cstd.body {
        CstBody::Proto { relation, body } => {
            // Find `where` keyword and `{ }` in the decl span.
            let where_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::KwWhere));
            let brace = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrace),
                |t| matches!(t, Token::RBrace),
            );

            let sig = format_sig_with_cst_args(&decl.sig, &cstd.args, cursor, end, style);

            // Relation span: from after `where` to `{`.
            let rel_end = match (where_pos, brace) {
                (Some(_), Some((_, _, bs, _))) => bs,
                _ => end,
            };

            // Advance cursor past the `where` keyword.
            let where_comments = if let Some(w) = where_pos {
                let comments = cursor.advance_to(w);
                let we = cursor.token_end(w).unwrap_or(w + 5);
                cursor.skip_to(we);
                comments
            } else {
                ALLOC.nil()
            };

            // Format relation with the main cursor (source order: after `where`).
            let rel_doc = format_relation(&relation.exp, cursor, rel_end, style);

            // Advance to `{` and skip past it.
            if let Some((_, oe, _, _)) = brace {
                cursor.skip_to(oe);
            }

            ALLOC.concat([
                ALLOC.text("proto "),
                sig,
                where_comments,
                ALLOC.text(" where "),
                rel_doc,
                ALLOC.text(" {"),
                ALLOC.hardline(),
                format_cst_body_exp(body, cursor, style).indent(indent),
                {
                    // Flush any remaining comments before `}`.
                    let close_pos = brace.map(|(_, _, _, cs)| cs).unwrap_or(end);
                    let has_remaining = cursor.has_comments_before(close_pos);
                    if has_remaining {
                        ALLOC.concat([
                            ALLOC.hardline(),
                            cursor.flush_comments_before(close_pos).indent(indent),
                        ])
                    } else {
                        ALLOC.nil()
                    }
                },
                ALLOC.hardline(),
                ALLOC.text("}"),
            ])
        }
        CstBody::Func { body } => {
            let sig = format_sig_with_cst_args(&decl.sig, &cstd.args, cursor, end, style);
            // Find `->` and `{ }` in the decl span.
            let arrow_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::Arrow));
            let brace = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrace),
                |t| matches!(t, Token::RBrace),
            );

            let sig_with_ret = match (&decl.sig.ret, arrow_pos, brace) {
                (Some(ret), Some(a), Some((_, _, bs, _))) => {
                    let ret_end = bs;
                    // Advance cursor to `->`.
                    let arrow_comments = cursor.advance_to(a);
                    let ae = cursor.token_end(a).unwrap_or(a + 2);
                    cursor.skip_to(ae);
                    ALLOC.concat([
                        sig,
                        arrow_comments,
                        ALLOC.text(" -> "),
                        format_typ(ret, cursor, ret_end, style),
                    ])
                }
                (Some(ret), _, _) => {
                    // Fallback: no arrow/brace found.
                    let ret_end = end;
                    ALLOC.concat([
                        sig,
                        ALLOC.text(" -> "),
                        format_typ(ret, cursor, ret_end, style),
                    ])
                }
                (None, _, _) => sig,
            };

            // Advance cursor past the `{` (to open_end, not open_start).
            if let Some((_, oe, _, _)) = brace {
                cursor.skip_to(oe);
            }

            ALLOC.concat([
                ALLOC.text("fn "),
                sig_with_ret,
                ALLOC.text(" {"),
                ALLOC.hardline(),
                format_cst_body_exp(body, cursor, style).indent(indent),
                {
                    // Flush any remaining comments before `}`.
                    let close_pos = brace.map(|(_, _, _, cs)| cs).unwrap_or(end);
                    let has_remaining = cursor.has_comments_before(close_pos);
                    if has_remaining {
                        ALLOC.concat([
                            ALLOC.hardline(),
                            cursor.flush_comments_before(close_pos).indent(indent),
                        ])
                    } else {
                        ALLOC.nil()
                    }
                },
                ALLOC.hardline(),
                ALLOC.text("}"),
            ])
        }
        CstBody::TypeAlias => {
            // Find `=` and `;` in the decl span.
            let eq_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::Eq));
            let semi_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let ret = decl.sig.ret.as_ref().expect("type alias must have ret");

            // Advance to the name token.
            let name_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let name_comments = cursor.advance_to(name_pos);
            let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
            cursor.skip_to(name_end);

            // Advance to `=`.
            let eq_comments = if let Some(e) = eq_pos {
                let c = cursor.advance_to(e);
                let ee = cursor.token_end(e).unwrap_or(e + 1);
                cursor.skip_to(ee);
                c
            } else {
                ALLOC.nil()
            };

            let ret_end = semi_pos.unwrap_or(end);

            ALLOC.concat([
                name_comments,
                ALLOC.text("type "),
                decl.sig.name.clone().pretty(&ALLOC),
                eq_comments,
                ALLOC.text(" = "),
                format_typ(ret, cursor, ret_end, style),
                ALLOC.text(";"),
            ])
        }
    };

    // Prepend leading comments, append trailing comment.
    let with_leading = if cstd.comments.leading.is_empty() {
        decl_doc
    } else {
        ALLOC.concat([format_leading(&cstd.comments), decl_doc])
    };
    if cstd.comments.trailing.is_some() {
        ALLOC.concat([with_leading, format_trailing(&cstd.comments)])
    } else {
        with_leading
    }
}

/// Format a signature using CST args (with comment attachments).
fn format_sig_with_cst_args(
    sig: &Sig<Size>,
    cst_args: &[crate::trivia::CstArg],
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    // Advance to the function name.
    let name_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
    let name_comments = cursor.advance_to(name_pos);
    let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
    cursor.skip_to(name_end);

    let name = ALLOC.concat([name_comments, sig.name.clone().pretty(&ALLOC)]);

    // Find typevars span: `<` ... `>` after the function name.
    let typevars = if sig.typevars.0.is_empty() {
        ALLOC.nil()
    } else {
        let angle = cursor.find_brackets(
            end,
            |t| matches!(t, Token::LAngle),
            |t| matches!(t, Token::RAngle),
        );
        let tv_end = match angle {
            Some((_, _, cs, _)) => cs,
            None => end,
        };
        // Advance to `<`.
        let open_comments =
            cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
        let open_end = angle.map(|(_, oe, _, _)| oe).unwrap_or(cursor.pos());
        cursor.skip_to(open_end);
        ALLOC.concat([
            open_comments,
            ALLOC.text("<"),
            format_typevars(&sig.typevars, cursor, tv_end, style),
            ALLOC.text(">"),
        ])
    };

    // Find `(` and `)`.
    let parens = cursor.find_brackets(
        end,
        |t| matches!(t, Token::LParen),
        |t| matches!(t, Token::RParen),
    );
    let (open_end, close_start) = match parens {
        Some((_, oe, cs, _)) => (oe, cs),
        None => (cursor.pos(), end),
    };

    // Advance to `(`.
    let open_comments = cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
    cursor.skip_to(open_end);

    let args = if cst_args.is_empty() {
        ALLOC.nil()
    } else {
        // If any arg has a trailing line comment, all args must go on
        // separate lines (// comments extend to EOL and would swallow
        // the next arg on the same line).
        let any_line_comment = cst_args.iter().any(|a| {
            a.comments
                .trailing
                .as_ref()
                .map(|c| !c.is_block)
                .unwrap_or(false)
        });

        // Build each arg as: leading_comments + arg_text + [comma + trailing_comment]
        let mut docs = Vec::with_capacity(cst_args.len());
        for (i, a) in cst_args.iter().enumerate() {
            let arg_doc = format_cst_arg_content(a, cursor, style);
            let is_last = i == cst_args.len() - 1;
            let comma = if is_last {
                ALLOC.nil()
            } else {
                ALLOC.text(",")
            };
            let trailing = match &a.comments.trailing {
                Some(c) => ALLOC.concat([ALLOC.text(" "), ALLOC.text(c.text.clone())]),
                None => ALLOC.nil(),
            };
            docs.push(ALLOC.concat([arg_doc, comma, trailing]));
        }

        let separator = if any_line_comment {
            ALLOC.hardline()
        } else {
            ALLOC.line()
        };
        ALLOC.intersperse(docs, separator).group()
    };

    // If the last arg has a trailing comment, `)` must go on a new line
    // (otherwise the `//` comment swallows the `)`).
    let last_has_trailing = cst_args
        .last()
        .and_then(|a| a.comments.trailing.as_ref())
        .is_some();
    let close_paren = if last_has_trailing {
        ALLOC.concat([ALLOC.hardline(), ALLOC.text(")")])
    } else {
        ALLOC.text(")")
    };

    // Advance cursor past `)`.
    let close_comments = cursor.advance_to(close_start);
    cursor.skip_to(close_start);

    ALLOC.concat([
        name,
        typevars,
        open_comments,
        ALLOC.text("("),
        args,
        close_comments,
        close_paren,
    ])
}

/// Format just the content of a CST arg (no trailing comment — that's
/// handled by the caller after the comma).
fn format_cst_arg_content(
    cst_arg: &crate::trivia::CstArg,
    cursor: &mut TokenCursor,
    style: &Style,
) -> Doc<'static> {
    let arg = &cst_arg.arg;
    let ts = &cst_arg.token_spans;
    let arg_end = cst_arg.span.end;

    // Build arg components with inline/leading comments.
    let qual_text = match arg.qualifier {
        Qualifier::Witness => "witness",
        Qualifier::Local => "local",
        Qualifier::Extra => "extra",
        Qualifier::Instance => "instance",
    };
    let dist_text = match arg.distribution {
        Distribution::Uniform => "uniform",
        Distribution::UniformNonZero => "uniform*",
        Distribution::Nonuniform => "",
    };

    let mut parts = Vec::new();

    // Qualifier: advance to it, emit comments.
    let qual_comments = cursor.advance_to(ts.qualifier_start);
    let qual_end = cursor
        .token_end(ts.qualifier_start)
        .unwrap_or(ts.qualifier_start + qual_text.len());
    cursor.skip_to(qual_end);
    parts.push(qual_comments);
    parts.push(ALLOC.text(qual_text));
    if !dist_text.is_empty() {
        parts.push(ALLOC.text(" "));
        parts.push(ALLOC.text(dist_text));
    }

    // Identifier: advance to it, emit comments.
    let id_comments = cursor.advance_to(ts.id_start);
    let id_end = cursor.token_end(ts.id_start).unwrap_or(ts.id_start);
    cursor.skip_to(id_end);
    parts.push(ALLOC.text(" "));
    parts.push(id_comments);
    parts.push(arg.id.clone().pretty(&ALLOC));

    // Colon: advance to it, emit comments.
    let colon_comments = cursor.advance_to(ts.colon_start);
    let colon_end = cursor
        .token_end(ts.colon_start)
        .unwrap_or(ts.colon_start + 1);
    cursor.skip_to(colon_end);
    parts.push(ALLOC.text(" "));
    parts.push(colon_comments);
    parts.push(ALLOC.text(":"));

    // Type: advance to typ_start, emit comments, then format the type.
    let typ_comments = cursor.advance_to(ts.typ_start);
    parts.push(ALLOC.text(" "));
    parts.push(typ_comments);
    parts.push(format_typ(&arg.typ, cursor, arg_end, style));

    ALLOC.concat(parts)
}

// ── Type variables ────────────────────────────────────────────────────

/// Format type variables: `T: Field, U: Group`
fn format_typevars(
    tvars: &TypeVars<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    if tvars.0.is_empty() {
        return ALLOC.nil();
    }

    // Find commas at depth 0 to split typevar spans.
    let comma_pos = cursor.find_all_at_depth0(end, |t| matches!(t, Token::Comma));
    let mut bounds = vec![cursor.pos()];
    for c in &comma_pos {
        bounds.push(*c);
    }
    bounds.push(end);

    let mut parts = Vec::new();
    for (i, tv) in tvars.0.iter().enumerate() {
        let tv_end = bounds.get(i + 1).copied().unwrap_or(end);
        parts.push(format_typevar(tv, cursor, tv_end, style));
        if i < tvars.0.len() - 1 {
            // Emit comments before the comma, then the comma.
            let comma_pos = comma_pos.get(i).copied().unwrap_or(tv_end);
            parts.push(cursor.advance_to(comma_pos));
            let ce = cursor.token_end(comma_pos).unwrap_or(comma_pos + 1);
            cursor.skip_to(ce);
            parts.push(ALLOC.text(", "));
        }
    }
    ALLOC.concat(parts)
}

fn format_typevar(
    tv: &TypeVar<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    // Find `:` at depth 0.
    let colon_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::Colon));
    let id_pos = cursor.first_significant(end).unwrap_or(cursor.pos());

    let id_comments = cursor.advance_to(id_pos);
    let id_end = cursor.token_end(id_pos).unwrap_or(id_pos);
    cursor.skip_to(id_end);

    let colon_comments = if let Some(c) = colon_pos {
        let comments = cursor.advance_to(c);
        let ce = cursor.token_end(c).unwrap_or(c + 1);
        cursor.skip_to(ce);
        comments
    } else {
        ALLOC.nil()
    };

    ALLOC.concat([
        id_comments,
        tv.id.clone().pretty(&ALLOC),
        colon_comments,
        ALLOC.text(": "),
        format_kind(&tv.kind, cursor, end, style),
    ])
}

// ── Types ─────────────────────────────────────────────────────────────

fn format_typ(
    typ: &GTyp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    _style: &Style,
) -> Doc<'static> {
    match typ {
        Typ::Poly(b, m, n) => {
            let angle = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LAngle),
                |t| matches!(t, Token::RAngle),
            );
            let (open_end, close_start) = match angle {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            // Advance to `Poly` keyword.
            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            // Advance to `<`.
            let open_comments =
                cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            // Find commas inside <...>.
            let commas = cursor.find_all_at_depth0(close_start, |t| matches!(t, Token::Comma));
            let mut bounds = vec![cursor.pos()];
            for c in &commas {
                bounds.push(*c);
            }
            bounds.push(close_start);

            // b, m, n
            let b_doc = b.clone().pretty(&ALLOC);
            // Advance cursor past b.
            let b_end = bounds.get(1).copied().unwrap_or(close_start);
            cursor.skip_to(b_end);

            // Comma 1 + comments
            let comma1_comments = if !commas.is_empty() {
                let c = commas[0];
                let comments = cursor.advance_to(c);
                let ce = cursor.token_end(c).unwrap_or(c + 1);
                cursor.skip_to(ce);
                comments
            } else {
                ALLOC.nil()
            };

            // m
            let m_end = bounds.get(2).copied().unwrap_or(close_start);
            let m_doc = format_size(m, cursor, m_end);

            // Comma 2 + comments
            let comma2_comments = if commas.get(1).is_some() {
                let c = commas[1];
                let comments = cursor.advance_to(c);
                let ce = cursor.token_end(c).unwrap_or(c + 1);
                cursor.skip_to(ce);
                comments
            } else {
                ALLOC.nil()
            };

            // n
            let n_doc = format_size(n, cursor, close_start);

            // Advance to `>`.
            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("Poly<"),
                open_comments,
                b_doc,
                comma1_comments,
                ALLOC.text(", "),
                m_doc,
                comma2_comments,
                ALLOC.text(", "),
                n_doc,
                close_comments,
                ALLOC.text(">"),
            ])
        }
        Typ::Base(b) => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, b.clone().pretty(&ALLOC)])
        }
        Typ::Vec(t, n) => {
            let brackets = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrack),
                |t| matches!(t, Token::RBrack),
            );
            let (open_end, close_start) = match brackets {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            // Advance to `[`.
            let open_comments =
                cursor.advance_to(brackets.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            // Find `;` inside [...].
            let semi = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Semi));
            let (t_end, _n_start) = match semi {
                Some(s) => {
                    let se = cursor.token_end(s).unwrap_or(s + 1);
                    (s, se)
                }
                None => (close_start, close_start),
            };

            let t_doc = format_typ(t, cursor, t_end, _style);

            // Advance to `;`.
            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            let n_doc = format_size(n, cursor, close_start);

            // Advance to `]`.
            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                open_comments,
                ALLOC.text("["),
                t_doc,
                semi_comments,
                ALLOC.text("; "),
                n_doc,
                close_comments,
                ALLOC.text("]"),
            ])
        }
        Typ::Fin(r) => {
            let angle = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LAngle),
                |t| matches!(t, Token::RAngle),
            );
            let (open_end, close_start) = match angle {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let range_doc = format_range(r, cursor, close_start);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("Fin<"),
                open_comments,
                range_doc,
                close_comments,
                ALLOC.text(">"),
            ])
        }
        Typ::Unit => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, ALLOC.text("Unit")])
        }
        Typ::Record(fields) => {
            let braces = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrace),
                |t| matches!(t, Token::RBrace),
            );
            let (open_end, close_start) = match braces {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let open_comments =
                cursor.advance_to(braces.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let commas = cursor.find_all_at_depth0(close_start, |t| matches!(t, Token::Comma));
            let mut bounds = vec![cursor.pos()];
            for c in &commas {
                bounds.push(*c);
            }
            bounds.push(close_start);

            let field_list: Vec<_> = fields.iter().collect();
            let mut field_docs = Vec::new();
            for (i, (name, t)) in field_list.iter().enumerate() {
                let _f_start = bounds.get(i).copied().unwrap_or(open_end);
                let f_end = bounds.get(i + 1).copied().unwrap_or(close_start);

                let name_pos = cursor.first_significant(f_end).unwrap_or(cursor.pos());
                let name_comments = cursor.advance_to(name_pos);
                let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
                cursor.skip_to(name_end);

                let colon = cursor.find_at_depth0(f_end, |t| matches!(t, Token::Colon));
                let colon_comments = if let Some(c) = colon {
                    let comments = cursor.advance_to(c);
                    let ce = cursor.token_end(c).unwrap_or(c + 1);
                    cursor.skip_to(ce);
                    comments
                } else {
                    ALLOC.nil()
                };

                field_docs.push(ALLOC.concat([
                    name_comments,
                    ALLOC.text(name.to_string()),
                    colon_comments,
                    ALLOC.text(": "),
                    format_typ(t, cursor, f_end, _style),
                ]));
            }

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                open_comments,
                ALLOC.text("{"),
                ALLOC.intersperse(field_docs, ALLOC.text(", ")),
                close_comments,
                ALLOC.text("}"),
            ])
        }
    }
}

fn format_kind(
    kind: &Kind<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    _style: &Style,
) -> Doc<'static> {
    match kind {
        Kind::Field => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, ALLOC.text("Field")])
        }
        Kind::Group => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, ALLOC.text("Group")])
        }
        Kind::Scalar(f) => {
            let angle = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LAngle),
                |t| matches!(t, Token::RAngle),
            );
            let (open_end, close_start) = match angle {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let ids: Vec<_> = f.iter().map(|t| ALLOC.text(t.to_string())).collect();
            let ids_doc = ALLOC.intersperse(ids, ALLOC.text(", "));

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("Scalar<"),
                open_comments,
                ids_doc,
                close_comments,
                ALLOC.text(">"),
            ])
        }
        Kind::Pairing(g1, g2) => {
            let angle = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LAngle),
                |t| matches!(t, Token::RAngle),
            );
            let (open_end, close_start) = match angle {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let comma = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Comma));
            let g1_end = comma.unwrap_or(close_start);

            // Advance past g1.
            let g1_last = cursor.last_significant_end(g1_end).unwrap_or(g1_end);
            cursor.skip_to(g1_last);

            let comma_comments = if let Some(c) = comma {
                let comments = cursor.advance_to(c);
                let ce = cursor.token_end(c).unwrap_or(c + 1);
                cursor.skip_to(ce);
                comments
            } else {
                ALLOC.nil()
            };

            // Advance past g2.
            let g2_last = cursor
                .last_significant_end(close_start)
                .unwrap_or(close_start);
            cursor.skip_to(g2_last);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("Pairing<"),
                open_comments,
                ALLOC.text(g1.to_string()),
                comma_comments,
                ALLOC.text(", "),
                ALLOC.text(g2.to_string()),
                close_comments,
                ALLOC.text(">"),
            ])
        }
        Kind::Range(r) => format_range(r, cursor, end),
        Kind::SizeVar => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, ALLOC.text("Size")])
        }
    }
}

// ── Size expressions ──────────────────────────────────────────────────

fn format_size(s: &Size, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    match s {
        Size::Var(_) | Size::Lit(_) => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, s.clone().pretty(&ALLOC)])
        }
        Size::Add(a, b) => format_size_binop(a, b, Token::Plus, "+", cursor, end),
        Size::Sub(a, b) => format_size_binop(a, b, Token::Minus, "-", cursor, end),
        Size::Mul(a, b) => format_size_binop(a, b, Token::Star, "*", cursor, end),
        Size::Div(a, b) => format_size_binop(a, b, Token::Slash, "/", cursor, end),
        Size::Pow(a, b) => format_size_binop(a, b, Token::Caret, "^", cursor, end),
        Size::Max(a, b) => format_size_func("max", a, b, cursor, end),
        Size::Min(a, b) => format_size_func("min", a, b, cursor, end),
    }
}

fn format_size_binop(
    a: &Size,
    b: &Size,
    op_token: Token<'static>,
    op_str: &str,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let op_pos = cursor.find_at_depth0(end, |t| {
        std::mem::discriminant(t) == std::mem::discriminant(&op_token)
    });
    let (a_end, _b_start) = match op_pos {
        Some(p) => {
            let pe = cursor.token_end(p).unwrap_or(p + 1);
            (p, pe)
        }
        None => (end, end),
    };

    let a_doc = format_size(a, cursor, a_end);

    let op_comments = if let Some(p) = op_pos {
        let comments = cursor.advance_to(p);
        let pe = cursor.token_end(p).unwrap_or(p + 1);
        cursor.skip_to(pe);
        comments
    } else {
        ALLOC.nil()
    };

    let b_doc = format_size(b, cursor, end);

    ALLOC.concat([
        a_doc,
        op_comments,
        ALLOC.text(format!(" {} ", op_str)),
        b_doc,
    ])
}

fn format_size_func(
    name: &str,
    a: &Size,
    b: &Size,
    cursor: &mut TokenCursor,
    end: usize,
) -> Doc<'static> {
    let parens = cursor.find_brackets(
        end,
        |t| matches!(t, Token::LParen),
        |t| matches!(t, Token::RParen),
    );
    let (open_end, close_start) = match parens {
        Some((_, oe, cs, _)) => (oe, cs),
        None => (cursor.pos(), end),
    };

    let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
    let kw_comments = cursor.advance_to(kw_pos);
    let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
    cursor.skip_to(kw_end);

    let open_comments = cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
    cursor.skip_to(open_end);

    let comma = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Comma));
    let (a_end, _b_start) = match comma {
        Some(c) => {
            let ce = cursor.token_end(c).unwrap_or(c + 1);
            (c, ce)
        }
        None => (close_start, close_start),
    };

    let a_doc = format_size(a, cursor, a_end);

    let comma_comments = if let Some(c) = comma {
        let comments = cursor.advance_to(c);
        let ce = cursor.token_end(c).unwrap_or(c + 1);
        cursor.skip_to(ce);
        comments
    } else {
        ALLOC.nil()
    };

    let b_doc = format_size(b, cursor, close_start);

    let close_comments = cursor.advance_to(close_start);
    cursor.skip_to(close_start);

    ALLOC.concat([
        kw_comments,
        ALLOC.text(name.to_string()),
        ALLOC.text("("),
        open_comments,
        a_doc,
        comma_comments,
        ALLOC.text(", "),
        b_doc,
        close_comments,
        ALLOC.text(")"),
    ])
}

fn format_range(r: &Range<Size>, cursor: &mut TokenCursor, end: usize) -> Doc<'static> {
    let dotdot_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::DotDot));
    let has_step = r.step.is_some();

    if has_step {
        let comma_pos = cursor.find_at_depth0(end, |t| matches!(t, Token::Comma));
        let (start_end, _step_start, step_end, _end_start) = match (comma_pos, dotdot_pos) {
            (Some(c), Some(d)) => {
                let ce = cursor.token_end(c).unwrap_or(c + 1);
                let de = cursor.token_end(d).unwrap_or(d + 2);
                (c, ce, d, de)
            }
            _ => (end, end, end, end),
        };

        let start_doc = format_size(&r.start.node, cursor, start_end);

        let comma_comments = if let Some(c) = comma_pos {
            let comments = cursor.advance_to(c);
            let ce = cursor.token_end(c).unwrap_or(c + 1);
            cursor.skip_to(ce);
            comments
        } else {
            ALLOC.nil()
        };

        let step_doc = format_size(&r.step.as_ref().unwrap().node, cursor, step_end);

        let dotdot_comments = if let Some(d) = dotdot_pos {
            let comments = cursor.advance_to(d);
            let de = cursor.token_end(d).unwrap_or(d + 2);
            cursor.skip_to(de);
            comments
        } else {
            ALLOC.nil()
        };

        let end_doc = format_size(&r.end.as_ref().unwrap().node, cursor, end);

        ALLOC.concat([
            start_doc,
            comma_comments,
            ALLOC.text(", "),
            step_doc,
            dotdot_comments,
            ALLOC.text(".."),
            end_doc,
        ])
    } else {
        let (start_end, _end_start) = match dotdot_pos {
            Some(d) => {
                let de = cursor.token_end(d).unwrap_or(d + 2);
                (d, de)
            }
            None => (end, end),
        };

        let start_doc = format_size(&r.start.node, cursor, start_end);

        if let Some(end_spanned) = &r.end {
            let dotdot_comments = if let Some(d) = dotdot_pos {
                let comments = cursor.advance_to(d);
                let de = cursor.token_end(d).unwrap_or(d + 2);
                cursor.skip_to(de);
                comments
            } else {
                ALLOC.nil()
            };

            let end_doc = format_size(&end_spanned.node, cursor, end);

            ALLOC.concat([start_doc, dotdot_comments, ALLOC.text(".."), end_doc])
        } else {
            // Bare size_ty like `N` → no `..end` part.
            start_doc
        }
    }
}

// ── Expressions ───────────────────────────────────────────────────────

/// Format a where-clause relation. Unlike body expressions, `Assert` in a
/// where clause is printed as `lhs == rhs` (no `assert(...)` wrapper).
fn format_relation(
    exp: &Exp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    match exp {
        Exp::Assert(lhs, rhs) => {
            let eqeq = cursor.find_at_depth0(end, |t| matches!(t, Token::EqEq));
            let (lhs_end, _rhs_start) = match eqeq {
                Some(p) => {
                    let pe = cursor.token_end(p).unwrap_or(p + 2);
                    (p, pe)
                }
                None => (end, end),
            };

            let lhs_doc = format_exp(lhs, cursor, lhs_end, style);

            let eqeq_comments = if let Some(p) = eqeq {
                let comments = cursor.advance_to(p);
                let pe = cursor.token_end(p).unwrap_or(p + 2);
                cursor.skip_to(pe);
                comments
            } else {
                ALLOC.nil()
            };

            let rhs_doc = format_exp(rhs, cursor, end, style);

            ALLOC.concat([lhs_doc, eqeq_comments, ALLOC.text(" == "), rhs_doc])
        }
        Exp::Let(Some(x), val, body) => {
            let eq = cursor.find_at_depth0(end, |t| matches!(t, Token::Eq));
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = semi.unwrap_or(end);
            let _body_start = match semi {
                Some(s) => cursor.token_end(s).unwrap_or(s + 1),
                None => end,
            };

            let let_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let let_comments = cursor.advance_to(let_pos);
            let let_end = cursor.token_end(let_pos).unwrap_or(let_pos + 3);
            cursor.skip_to(let_end);

            // Advance past the variable name.
            let name_pos = cursor
                .first_significant(eq.unwrap_or(end))
                .unwrap_or(cursor.pos());
            let name_comments = cursor.advance_to(name_pos);
            let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
            cursor.skip_to(name_end);

            let eq_comments = if let Some(e) = eq {
                let comments = cursor.advance_to(e);
                let ee = cursor.token_end(e).unwrap_or(e + 1);
                cursor.skip_to(ee);
                comments
            } else {
                ALLOC.nil()
            };

            let val_doc = format_exp(val, cursor, val_end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            let body_doc = match body {
                Some(b) => ALLOC.concat([ALLOC.text("; "), format_relation(b, cursor, end, style)]),
                None => ALLOC.text(";"),
            };

            ALLOC.concat([
                let_comments,
                ALLOC.text("let "),
                name_comments,
                x.clone().pretty(&ALLOC),
                eq_comments,
                ALLOC.text(" = "),
                val_doc,
                semi_comments,
                body_doc,
            ])
        }
        Exp::Let(None, val, body) => {
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = semi.unwrap_or(end);
            let _body_start = match semi {
                Some(s) => cursor.token_end(s).unwrap_or(s + 1),
                None => end,
            };

            let val_doc = format_relation(val, cursor, val_end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            let body_doc = match body {
                Some(b) => ALLOC.concat([ALLOC.text("; "), format_relation(b, cursor, end, style)]),
                None => ALLOC.text(";"),
            };

            ALLOC.concat([val_doc, semi_comments, body_doc])
        }
        _ => format_exp(exp, cursor, end, style),
    }
}

/// Format a CST body expression (inside `{ }`). The CstExp carries its
/// own comments — the cursor handles inline comments within expressions.
fn format_cst_body_exp(cst_exp: &CstExp, cursor: &mut TokenCursor, style: &Style) -> Doc<'static> {
    let leading_doc = format_leading(&cst_exp.comments);
    let trailing_doc = format_trailing(&cst_exp.comments);
    let span = &cst_exp.span;
    let end = span.end;

    match &cst_exp.exp {
        Exp::Let(Some(x), val, _body) => {
            // Find token positions BEFORE processing body (cursor is at span.start).
            let eq = cursor.find_at_depth0(end, |t| matches!(t, Token::Eq));
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = match (eq, semi) {
                (Some(e), Some(s)) => {
                    let ee = cursor.token_end(e).unwrap_or(e + 1);
                    ee..s
                }
                _ => span.start..end,
            };

            let let_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let let_comments = cursor.advance_to(let_pos);
            let let_end = cursor.token_end(let_pos).unwrap_or(let_pos + 3);
            cursor.skip_to(let_end);

            // Advance past the variable name.
            let name_pos = cursor
                .first_significant(eq.unwrap_or(end))
                .unwrap_or(cursor.pos());
            let name_comments = cursor.advance_to(name_pos);
            let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
            cursor.skip_to(name_end);

            let eq_comments = if let Some(e) = eq {
                let comments = cursor.advance_to(e);
                let ee = cursor.token_end(e).unwrap_or(e + 1);
                cursor.skip_to(ee);
                comments
            } else {
                ALLOC.nil()
            };

            let val_doc = format_exp(val, cursor, val_end.end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            // Process body AFTER current statement (source order).
            let body_doc = match &cst_exp.body {
                Some(b) => format_cst_body_exp(b, cursor, style),
                None => ALLOC.nil(),
            };

            ALLOC.concat([
                leading_doc,
                let_comments,
                ALLOC.text("let "),
                name_comments,
                x.clone().pretty(&ALLOC),
                eq_comments,
                ALLOC.text(" = "),
                val_doc,
                semi_comments,
                ALLOC.text(";"),
                trailing_doc,
                ALLOC.hardline(),
                body_doc,
            ])
        }
        Exp::Let(None, val, _body) => {
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = semi.unwrap_or(end);

            let val_doc = format_exp(val, cursor, val_end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            // Process body AFTER current statement (source order).
            let body_doc = match &cst_exp.body {
                Some(b) => format_cst_body_exp(b, cursor, style),
                None => ALLOC.nil(),
            };

            ALLOC.concat([
                leading_doc,
                val_doc,
                semi_comments,
                ALLOC.text(";"),
                trailing_doc,
                ALLOC.hardline(),
                body_doc,
            ])
        }
        Exp::Log(x, val, _body) => {
            let larrow = cursor.find_at_depth0(end, |t| matches!(t, Token::LArrow));
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = match (larrow, semi) {
                (Some(a), Some(s)) => {
                    let ae = cursor.token_end(a).unwrap_or(a + 2);
                    ae..s
                }
                _ => span.start..end,
            };

            let id_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let id_comments = cursor.advance_to(id_pos);
            let id_end = cursor.token_end(id_pos).unwrap_or(id_pos);
            cursor.skip_to(id_end);

            let larrow_comments = if let Some(a) = larrow {
                let comments = cursor.advance_to(a);
                let ae = cursor.token_end(a).unwrap_or(a + 2);
                cursor.skip_to(ae);
                comments
            } else {
                ALLOC.nil()
            };

            let val_doc = format_exp(val, cursor, val_end.end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            // Process body AFTER current statement (source order).
            let body_doc = match &cst_exp.body {
                Some(b) => format_cst_body_exp(b, cursor, style),
                None => ALLOC.nil(),
            };

            ALLOC.concat([
                leading_doc,
                id_comments,
                x.clone().pretty(&ALLOC),
                larrow_comments,
                ALLOC.text(" <- "),
                val_doc,
                semi_comments,
                ALLOC.text(";"),
                trailing_doc,
                ALLOC.hardline(),
                body_doc,
            ])
        }
        _ => ALLOC.concat([leading_doc, format_exp(&cst_exp.exp, cursor, end, style)]),
    }
}

/// Format a Let/Log chain in non-body position (no comments available).
fn format_exp_let_log(
    exp: &Exp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    match exp {
        Exp::Let(Some(x), val, body) => {
            let eq = cursor.find_at_depth0(end, |t| matches!(t, Token::Eq));
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = match (eq, semi) {
                (Some(e), Some(s)) => {
                    let ee = cursor.token_end(e).unwrap_or(e + 1);
                    ee..s
                }
                _ => cursor.pos()..end,
            };
            let _body_start = match semi {
                Some(s) => cursor.token_end(s).unwrap_or(s + 1),
                None => end,
            };

            let let_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let let_comments = cursor.advance_to(let_pos);
            let let_end = cursor.token_end(let_pos).unwrap_or(let_pos + 3);
            cursor.skip_to(let_end);

            // Advance past the variable name.
            let name_pos = cursor
                .first_significant(eq.unwrap_or(end))
                .unwrap_or(cursor.pos());
            let name_comments = cursor.advance_to(name_pos);
            let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
            cursor.skip_to(name_end);

            let eq_comments = if let Some(e) = eq {
                let comments = cursor.advance_to(e);
                let ee = cursor.token_end(e).unwrap_or(e + 1);
                cursor.skip_to(ee);
                comments
            } else {
                ALLOC.nil()
            };

            let val_doc = format_exp(val, cursor, val_end.end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            let body_doc = match body {
                Some(b) => {
                    ALLOC.concat([ALLOC.text("; "), format_exp_let_log(b, cursor, end, style)])
                }
                None => ALLOC.text(";"),
            };

            ALLOC.concat([
                let_comments,
                ALLOC.text("let "),
                name_comments,
                x.clone().pretty(&ALLOC),
                eq_comments,
                ALLOC.text(" = "),
                val_doc,
                semi_comments,
                body_doc,
            ])
        }
        Exp::Let(None, val, body) => {
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = semi.unwrap_or(end);

            let val_doc = format_exp(val, cursor, val_end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            let body_doc = match body {
                Some(b) => {
                    ALLOC.concat([ALLOC.text("; "), format_exp_let_log(b, cursor, end, style)])
                }
                None => ALLOC.text(";"),
            };

            ALLOC.concat([val_doc, semi_comments, body_doc])
        }
        Exp::Log(x, val, body) => {
            let larrow = cursor.find_at_depth0(end, |t| matches!(t, Token::LArrow));
            let semi = cursor.find_at_depth0(end, |t| matches!(t, Token::Semi));
            let val_end = match (larrow, semi) {
                (Some(a), Some(s)) => {
                    let ae = cursor.token_end(a).unwrap_or(a + 2);
                    ae..s
                }
                _ => cursor.pos()..end,
            };

            let id_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let id_comments = cursor.advance_to(id_pos);
            let id_end = cursor.token_end(id_pos).unwrap_or(id_pos);
            cursor.skip_to(id_end);

            let larrow_comments = if let Some(a) = larrow {
                let comments = cursor.advance_to(a);
                let ae = cursor.token_end(a).unwrap_or(a + 2);
                cursor.skip_to(ae);
                comments
            } else {
                ALLOC.nil()
            };

            let val_doc = format_exp(val, cursor, val_end.end, style);

            let semi_comments = if let Some(s) = semi {
                let comments = cursor.advance_to(s);
                let se = cursor.token_end(s).unwrap_or(s + 1);
                cursor.skip_to(se);
                comments
            } else {
                ALLOC.nil()
            };

            let body_doc = match body {
                Some(b) => {
                    ALLOC.concat([ALLOC.text("; "), format_exp_let_log(b, cursor, end, style)])
                }
                None => ALLOC.text(";"),
            };

            ALLOC.concat([
                id_comments,
                x.clone().pretty(&ALLOC),
                larrow_comments,
                ALLOC.text(" <- "),
                val_doc,
                semi_comments,
                body_doc,
            ])
        }
        _ => format_exp(exp, cursor, end, style),
    }
}

/// Format an expression in canonical style.
pub fn format_exp(
    exp: &Exp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    match exp {
        Exp::Neg(inner) => {
            let minus_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let minus_comments = cursor.advance_to(minus_pos);
            let minus_end = cursor.token_end(minus_pos).unwrap_or(minus_pos + 1);
            cursor.skip_to(minus_end);
            ALLOC.concat([
                minus_comments,
                ALLOC.text("-"),
                format_exp(inner, cursor, end, style),
            ])
        }

        Exp::Bin(op, lhs, rhs) => {
            if matches!(op, BinOp::Dot) {
                return format_binary_call("dot", lhs, rhs, cursor, end, style);
            }
            let op_pred = |t: &Token| -> bool {
                match op {
                    BinOp::Add => matches!(t, Token::Plus),
                    BinOp::Sub => matches!(t, Token::Minus),
                    BinOp::Mul => matches!(t, Token::Star),
                    BinOp::Div => matches!(t, Token::Slash),
                    BinOp::Pow => matches!(t, Token::Caret),
                    BinOp::Concat => matches!(t, Token::PlusPlus),
                    BinOp::Rem => matches!(t, Token::Percent),
                    BinOp::Dot => false,
                }
            };
            let op_pos = cursor.find_at_depth0(end, op_pred);
            let (lhs_end, _rhs_start) = match op_pos {
                Some(p) => {
                    let pe = cursor.token_end(p).unwrap_or(p + 1);
                    (p, pe)
                }
                None => (end, end),
            };

            let l = format_exp(lhs, cursor, lhs_end, style);
            let l = if lhs_needs_paren(*op, lhs) {
                ALLOC.concat([ALLOC.text("("), l, ALLOC.text(")")])
            } else {
                l
            };

            let op_comments = if let Some(p) = op_pos {
                let comments = cursor.advance_to(p);
                let pe = cursor.token_end(p).unwrap_or(p + 1);
                cursor.skip_to(pe);
                comments
            } else {
                ALLOC.nil()
            };

            let r = format_exp(rhs, cursor, end, style);
            let r = if rhs_needs_paren(*op, rhs) {
                ALLOC.concat([ALLOC.text("("), r, ALLOC.text(")")])
            } else {
                r
            };

            let op_str = match op {
                BinOp::Add => " + ",
                BinOp::Sub => " - ",
                BinOp::Mul => " * ",
                BinOp::Div => " / ",
                BinOp::Pow => " ^ ",
                BinOp::Dot => unreachable!(),
                BinOp::Concat => " ++ ",
                BinOp::Rem => " % ",
            };
            ALLOC.concat([l, op_comments, ALLOC.text(op_str), r])
        }

        Exp::Lit(n) => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, n.clone().pretty(&ALLOC)])
        }
        Exp::Unit => {
            let parens = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LParen),
                |t| matches!(t, Token::RParen),
            );
            match parens {
                Some((os, _, cs, _)) => {
                    let open_comments = cursor.advance_to(os);
                    let oe = cursor.token_end(os).unwrap_or(os + 1);
                    cursor.skip_to(oe);
                    let close_comments = cursor.advance_to(cs);
                    cursor.skip_to(cs);
                    ALLOC.concat([
                        open_comments,
                        ALLOC.text("("),
                        close_comments,
                        ALLOC.text(")"),
                    ])
                }
                None => ALLOC.text("()"),
            }
        }
        Exp::Var(x) => {
            let pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let comments = cursor.advance_to(pos);
            let pe = cursor.token_end(pos).unwrap_or(pos);
            cursor.skip_to(pe);
            ALLOC.concat([comments, x.clone().pretty(&ALLOC)])
        }

        Exp::App(f, args) => {
            // Find `(` and `)`.
            let parens = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LParen),
                |t| matches!(t, Token::RParen),
            );
            let (open_end, close_start) = match parens {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            // Advance to function name.
            let f_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let f_comments = cursor.advance_to(f_pos);
            let f_end = cursor.token_end(f_pos).unwrap_or(f_pos);
            cursor.skip_to(f_end);

            // Advance to `(`.
            let open_comments =
                cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let args_doc = format_exps(args, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                f_comments,
                f.clone().pretty(&ALLOC),
                open_comments,
                ALLOC.text("("),
                args_doc,
                close_comments,
                ALLOC.text(")"),
            ])
        }

        Exp::Interpolate(None, evals) => {
            format_unary_call("interpolate", evals, cursor, end, style)
        }
        Exp::Interpolate(Some(points), evals) => {
            format_binary_call("interpolate", points, evals, cursor, end, style)
        }

        Exp::Poly(p) => format_unary_call("poly", p, cursor, end, style),
        Exp::Coef(p) => format_unary_call("coef", p, cursor, end, style),
        Exp::Mle(p) => format_unary_call("mle", p, cursor, end, style),

        Exp::Evaluate(p, None, None) => format_unary_call("eval", p, cursor, end, style),
        Exp::Evaluate(p, None, Some(x)) => format_binary_call("eval", p, x, cursor, end, style),
        Exp::Evaluate(p, Some(range), Some(x)) => {
            format_eval_ranged(p, Some(range), Some(x), cursor, end, style)
        }
        Exp::Evaluate(p, Some(range), None) => {
            format_eval_ranged(p, Some(range), None, cursor, end, style)
        }

        Exp::Vec(exps) => {
            let brackets = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrack),
                |t| matches!(t, Token::RBrack),
            );
            let (open_end, close_start) = match brackets {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let open_comments =
                cursor.advance_to(brackets.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let args_doc = format_exps(exps, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                open_comments,
                ALLOC.text("["),
                args_doc,
                close_comments,
                ALLOC.text("]"),
            ])
        }

        Exp::Range(r) => format_range(r, cursor, end),

        Exp::Map(body, var, range) => {
            let brackets = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrack),
                |t| matches!(t, Token::RBrack),
            );
            let (open_end, close_start) = match brackets {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let open_comments =
                cursor.advance_to(brackets.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let for_pos = cursor.find_at_depth0(close_start, |t| matches!(t, Token::KwFor));
            let in_pos = cursor.find_at_depth0(close_start, |t| matches!(t, Token::KwIn));
            let body_end = for_pos.unwrap_or(close_start);

            let body_doc = format_exp(body, cursor, body_end, style);

            let for_comments = if let Some(f) = for_pos {
                let comments = cursor.advance_to(f);
                let fe = cursor.token_end(f).unwrap_or(f + 3);
                cursor.skip_to(fe);
                comments
            } else {
                ALLOC.nil()
            };

            // Advance past the variable name.
            let var_end = in_pos.unwrap_or(close_start);
            let var_pos = cursor.first_significant(var_end).unwrap_or(cursor.pos());
            let var_comments = cursor.advance_to(var_pos);
            let var_end = cursor.token_end(var_pos).unwrap_or(var_pos);
            cursor.skip_to(var_end);

            let in_comments = if let Some(i) = in_pos {
                let comments = cursor.advance_to(i);
                let ie = cursor.token_end(i).unwrap_or(i + 2);
                cursor.skip_to(ie);
                comments
            } else {
                ALLOC.nil()
            };

            let range_doc = format_exp(range, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                open_comments,
                ALLOC.text("["),
                body_doc,
                for_comments,
                ALLOC.text(" for "),
                var_comments,
                var.clone().pretty(&ALLOC),
                in_comments,
                ALLOC.text(" in "),
                range_doc,
                close_comments,
                ALLOC.text("]"),
            ])
        }

        Exp::Reduce(op, exp) => {
            let parens = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LParen),
                |t| matches!(t, Token::RParen),
            );
            let (open_end, close_start) = match parens {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let comma = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Comma));
            let _exp_start = match comma {
                Some(c) => cursor.token_end(c).unwrap_or(c + 1),
                None => open_end,
            };

            // Advance past the binop symbol.
            let op_end = comma.unwrap_or(close_start);
            let op_last = cursor.last_significant_end(op_end).unwrap_or(op_end);
            cursor.skip_to(op_last);

            let comma_comments = if let Some(c) = comma {
                let comments = cursor.advance_to(c);
                let ce = cursor.token_end(c).unwrap_or(c + 1);
                cursor.skip_to(ce);
                comments
            } else {
                ALLOC.nil()
            };

            let exp_doc = format_exp(exp, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("reduce("),
                open_comments,
                format_binop_symbol(op),
                comma_comments,
                ALLOC.text(", "),
                exp_doc,
                close_comments,
                ALLOC.text(")"),
            ])
        }

        Exp::Ram(base, idx) => {
            let brackets = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBrack),
                |t| matches!(t, Token::RBrack),
            );
            let (open_end, close_start) = match brackets {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let base_end = brackets.map(|(os, _, _, _)| os).unwrap_or(end);
            let base_doc = format_exp(base, cursor, base_end, style);

            let open_comments =
                cursor.advance_to(brackets.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let idx_doc = format_exp(idx, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                base_doc,
                open_comments,
                ALLOC.text("["),
                idx_doc,
                close_comments,
                ALLOC.text("]"),
            ])
        }

        Exp::Pair(a, b) => format_binary_call("pair", a, b, cursor, end, style),

        Exp::Random(t, star) => {
            let angle = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LAngle),
                |t| matches!(t, Token::RAngle),
            );
            let (open_end, close_start) = match angle {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let star_pos = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Star));

            // Advance past the type identifier.
            let tid_end = star_pos.unwrap_or(close_start);
            let tid_last = cursor.last_significant_end(tid_end).unwrap_or(tid_end);
            cursor.skip_to(tid_last);

            let star_comments = if let Some(s) = star_pos {
                if *star {
                    let comments = cursor.advance_to(s);
                    let se = cursor.token_end(s).unwrap_or(s + 1);
                    cursor.skip_to(se);
                    comments
                } else {
                    cursor.skip_to(close_start);
                    ALLOC.nil()
                }
            } else {
                ALLOC.nil()
            };

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("random<"),
                open_comments,
                t.clone().pretty(&ALLOC),
                if *star {
                    ALLOC.concat([star_comments, ALLOC.text("*")])
                } else {
                    ALLOC.nil()
                },
                close_comments,
                ALLOC.text(">"),
            ])
        }
        Exp::Challenge(t, star) => {
            let angle = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LAngle),
                |t| matches!(t, Token::RAngle),
            );
            let (open_end, close_start) = match angle {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let star_pos = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Star));

            let tid_end = star_pos.unwrap_or(close_start);
            let tid_last = cursor.last_significant_end(tid_end).unwrap_or(tid_end);
            cursor.skip_to(tid_last);

            let star_comments = if let Some(s) = star_pos {
                if *star {
                    let comments = cursor.advance_to(s);
                    let se = cursor.token_end(s).unwrap_or(s + 1);
                    cursor.skip_to(se);
                    comments
                } else {
                    cursor.skip_to(close_start);
                    ALLOC.nil()
                }
            } else {
                ALLOC.nil()
            };

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("challenge<"),
                open_comments,
                t.clone().pretty(&ALLOC),
                if *star {
                    ALLOC.concat([star_comments, ALLOC.text("*")])
                } else {
                    ALLOC.nil()
                },
                close_comments,
                ALLOC.text(">"),
            ])
        }

        Exp::Let(_, _, _) | Exp::Log(_, _, _) => format_exp_let_log(exp, cursor, end, style),

        Exp::Assert(lhs, rhs) => {
            let parens = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LParen),
                |t| matches!(t, Token::RParen),
            );
            let (open_end, close_start) = match parens {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let eqeq = cursor.find_at_depth0(close_start, |t| matches!(t, Token::EqEq));
            let lhs_end = eqeq.unwrap_or(close_start);

            let lhs_doc = format_exp(lhs, cursor, lhs_end, style);

            let eqeq_comments = if let Some(p) = eqeq {
                let comments = cursor.advance_to(p);
                let pe = cursor.token_end(p).unwrap_or(p + 2);
                cursor.skip_to(pe);
                comments
            } else {
                ALLOC.nil()
            };

            let rhs_doc = format_exp(rhs, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("assert("),
                open_comments,
                lhs_doc,
                eqeq_comments,
                ALLOC.text(" == "),
                rhs_doc,
                close_comments,
                ALLOC.text(")"),
            ])
        }
        Exp::Verify(lhs, rhs) => {
            let parens = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LParen),
                |t| matches!(t, Token::RParen),
            );
            let (open_end, close_start) = match parens {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            let open_comments =
                cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let eqeq = cursor.find_at_depth0(close_start, |t| matches!(t, Token::EqEq));
            let lhs_end = eqeq.unwrap_or(close_start);

            let lhs_doc = format_exp(lhs, cursor, lhs_end, style);

            let eqeq_comments = if let Some(p) = eqeq {
                let comments = cursor.advance_to(p);
                let pe = cursor.token_end(p).unwrap_or(p + 2);
                cursor.skip_to(pe);
                comments
            } else {
                ALLOC.nil()
            };

            let rhs_doc = format_exp(rhs, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                kw_comments,
                ALLOC.text("verify("),
                open_comments,
                lhs_doc,
                eqeq_comments,
                ALLOC.text(" == "),
                rhs_doc,
                close_comments,
                ALLOC.text(")"),
            ])
        }

        Exp::Fun(vars, body) => {
            let arrow = cursor.find_at_depth0(end, |t| matches!(t, Token::FatArrow));

            let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
            let kw_comments = cursor.advance_to(kw_pos);
            let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
            cursor.skip_to(kw_end);

            // Advance past the variable list.
            let vars_end = arrow.unwrap_or(end);
            let vars_last = cursor.last_significant_end(vars_end).unwrap_or(vars_end);
            cursor.skip_to(vars_last);

            let arrow_comments = if let Some(a) = arrow {
                let comments = cursor.advance_to(a);
                let ae = cursor.token_end(a).unwrap_or(a + 2);
                cursor.skip_to(ae);
                comments
            } else {
                ALLOC.nil()
            };

            let vars_str = vars
                .iter()
                .map(|v| v.0.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            ALLOC.concat([
                kw_comments,
                ALLOC.text("fun "),
                ALLOC.text(vars_str),
                arrow_comments,
                ALLOC.text(" => "),
                format_exp(body, cursor, end, style),
            ])
        }

        Exp::Record(fields) => {
            let brackets = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LBraceBar),
                |t| matches!(t, Token::BarRBrace),
            );
            let (open_end, close_start) = match brackets {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let open_comments =
                cursor.advance_to(brackets.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let commas = cursor.find_all_at_depth0(close_start, |t| matches!(t, Token::Comma));
            let mut bounds = vec![cursor.pos()];
            for c in &commas {
                bounds.push(*c);
            }
            bounds.push(close_start);

            let field_list: Vec<_> = fields.iter().collect();
            let mut field_docs = Vec::new();
            for (i, (name, exp)) in field_list.iter().enumerate() {
                let _f_start = bounds.get(i).copied().unwrap_or(open_end);
                let f_end = bounds.get(i + 1).copied().unwrap_or(close_start);

                let name_pos = cursor.first_significant(f_end).unwrap_or(cursor.pos());
                let name_comments = cursor.advance_to(name_pos);
                let name_end = cursor.token_end(name_pos).unwrap_or(name_pos);
                cursor.skip_to(name_end);

                let colon = cursor.find_at_depth0(f_end, |t| matches!(t, Token::Colon));
                let colon_comments = if let Some(c) = colon {
                    let comments = cursor.advance_to(c);
                    let ce = cursor.token_end(c).unwrap_or(c + 1);
                    cursor.skip_to(ce);
                    comments
                } else {
                    ALLOC.nil()
                };

                field_docs.push(ALLOC.concat([
                    name_comments,
                    ALLOC.text(name.to_string()),
                    colon_comments,
                    ALLOC.text(": "),
                    format_exp(exp, cursor, f_end, style),
                ]));
            }

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                open_comments,
                ALLOC.text("{|"),
                ALLOC.intersperse(field_docs, ALLOC.text(", ")),
                close_comments,
                ALLOC.text("|}"),
            ])
        }

        Exp::Proj(base, field) => {
            let dot = cursor.find_at_depth0(end, |t| matches!(t, Token::Dot));
            let base_end = dot.unwrap_or(end);

            let base_doc = format_exp(base, cursor, base_end, style);

            let dot_comments = if let Some(d) = dot {
                let comments = cursor.advance_to(d);
                let de = cursor.token_end(d).unwrap_or(d + 1);
                cursor.skip_to(de);
                comments
            } else {
                ALLOC.nil()
            };

            // Advance past the field name.
            let field_last = cursor.last_significant_end(end).unwrap_or(end);
            cursor.skip_to(field_last);

            ALLOC.concat([
                base_doc,
                dot_comments,
                ALLOC.text("."),
                ALLOC.text(field.to_string()),
            ])
        }

        Exp::SetRecord(record, field, value) => {
            let parens = cursor.find_brackets(
                end,
                |t| matches!(t, Token::LParen),
                |t| matches!(t, Token::RParen),
            );
            let (open_end, close_start) = match parens {
                Some((_, oe, cs, _)) => (oe, cs),
                None => (cursor.pos(), end),
            };

            let dot = cursor.find_at_depth0(open_end, |t| matches!(t, Token::Dot));
            let record_end = dot.unwrap_or(open_end);

            let record_doc = format_exp(record, cursor, record_end, style);

            let dot_comments = if let Some(d) = dot {
                let comments = cursor.advance_to(d);
                let de = cursor.token_end(d).unwrap_or(d + 1);
                cursor.skip_to(de);
                comments
            } else {
                ALLOC.nil()
            };

            // Advance past the field name.
            let field_end = open_end;
            let field_last = cursor.last_significant_end(field_end).unwrap_or(field_end);
            cursor.skip_to(field_last);

            let open_comments =
                cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
            cursor.skip_to(open_end);

            let comma = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Comma));
            let comma_comments = if let Some(c) = comma {
                let comments = cursor.advance_to(c);
                let ce = cursor.token_end(c).unwrap_or(c + 1);
                cursor.skip_to(ce);
                comments
            } else {
                ALLOC.nil()
            };

            let value_doc = format_exp(value, cursor, close_start, style);

            let close_comments = cursor.advance_to(close_start);
            cursor.skip_to(close_start);

            ALLOC.concat([
                record_doc,
                dot_comments,
                ALLOC.text(".set("),
                open_comments,
                ALLOC.text(field.to_string()),
                comma_comments,
                ALLOC.text(", "),
                value_doc,
                close_comments,
                ALLOC.text(")"),
            ])
        }
    }
}

/// Format a unary function call: `name(exp)`.
fn format_unary_call(
    name: &str,
    arg: &Exp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let parens = cursor.find_brackets(
        end,
        |t| matches!(t, Token::LParen),
        |t| matches!(t, Token::RParen),
    );
    let (open_end, close_start) = match parens {
        Some((_, oe, cs, _)) => (oe, cs),
        None => (cursor.pos(), end),
    };

    let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
    let kw_comments = cursor.advance_to(kw_pos);
    let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
    cursor.skip_to(kw_end);

    let open_comments = cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
    cursor.skip_to(open_end);

    let arg_doc = format_exp(arg, cursor, close_start, style);

    let close_comments = cursor.advance_to(close_start);
    cursor.skip_to(close_start);

    ALLOC.concat([
        kw_comments,
        ALLOC.text(name.to_string()),
        ALLOC.text("("),
        open_comments,
        arg_doc,
        close_comments,
        ALLOC.text(")"),
    ])
}

/// Format a binary function call: `name(a, b)`.
fn format_binary_call(
    name: &str,
    a: &Exp<Size>,
    b: &Exp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let parens = cursor.find_brackets(
        end,
        |t| matches!(t, Token::LParen),
        |t| matches!(t, Token::RParen),
    );
    let (open_end, close_start) = match parens {
        Some((_, oe, cs, _)) => (oe, cs),
        None => (cursor.pos(), end),
    };

    let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
    let kw_comments = cursor.advance_to(kw_pos);
    let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
    cursor.skip_to(kw_end);

    let open_comments = cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
    cursor.skip_to(open_end);

    let comma = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Comma));
    let a_end = comma.unwrap_or(close_start);

    let a_doc = format_exp(a, cursor, a_end, style);

    let comma_comments = if let Some(c) = comma {
        let comments = cursor.advance_to(c);
        let ce = cursor.token_end(c).unwrap_or(c + 1);
        cursor.skip_to(ce);
        comments
    } else {
        ALLOC.nil()
    };

    let b_doc = format_exp(b, cursor, close_start, style);

    let close_comments = cursor.advance_to(close_start);
    cursor.skip_to(close_start);

    ALLOC.concat([
        kw_comments,
        ALLOC.text(name.to_string()),
        ALLOC.text("("),
        open_comments,
        a_doc,
        comma_comments,
        ALLOC.text(", "),
        b_doc,
        close_comments,
        ALLOC.text(")"),
    ])
}

/// Format `eval<range>(p, x)` or `eval<range>(p)`.
fn format_eval_ranged(
    p: &Exp<Size>,
    range: Option<&Range<Size>>,
    x: Option<&Exp<Size>>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let angle = cursor.find_brackets(
        end,
        |t| matches!(t, Token::LAngle),
        |t| matches!(t, Token::RAngle),
    );
    let (angle_open_end, angle_close_start) = match angle {
        Some((_, oe, cs, _)) => (oe, cs),
        None => (cursor.pos(), end),
    };

    let parens = cursor.find_brackets(
        end,
        |t| matches!(t, Token::LParen),
        |t| matches!(t, Token::RParen),
    );
    let (open_end, close_start) = match parens {
        Some((_, oe, cs, _)) => (oe, cs),
        None => (cursor.pos(), end),
    };

    let kw_pos = cursor.first_significant(end).unwrap_or(cursor.pos());
    let kw_comments = cursor.advance_to(kw_pos);
    let kw_end = cursor.token_end(kw_pos).unwrap_or(kw_pos);
    cursor.skip_to(kw_end);

    // Advance to `<`.
    let angle_open_comments =
        cursor.advance_to(angle.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
    cursor.skip_to(angle_open_end);

    let range_doc = if let Some(r) = range {
        format_range(r, cursor, angle_close_start)
    } else {
        cursor.skip_to(angle_close_start);
        ALLOC.nil()
    };

    let angle_close_comments = cursor.advance_to(angle_close_start);
    cursor.skip_to(angle_close_start);

    // Advance to `(`.
    let open_comments = cursor.advance_to(parens.map(|(os, _, _, _)| os).unwrap_or(cursor.pos()));
    cursor.skip_to(open_end);

    let comma = cursor.find_at_depth0(close_start, |t| matches!(t, Token::Comma));
    let p_end = comma.unwrap_or(close_start);

    let p_doc = format_exp(p, cursor, p_end, style);

    let comma_comments = if let Some(c) = comma {
        let comments = cursor.advance_to(c);
        let ce = cursor.token_end(c).unwrap_or(c + 1);
        cursor.skip_to(ce);
        comments
    } else {
        ALLOC.nil()
    };

    let x_doc = if let Some(x) = x {
        format_exp(x, cursor, close_start, style)
    } else {
        ALLOC.nil()
    };

    let close_comments = cursor.advance_to(close_start);
    cursor.skip_to(close_start);

    ALLOC.concat([
        kw_comments,
        ALLOC.text("eval<"),
        angle_open_comments,
        range_doc,
        angle_close_comments,
        ALLOC.text(">("),
        open_comments,
        p_doc,
        comma_comments,
        if x.is_some() {
            ALLOC.text(", ")
        } else {
            ALLOC.nil()
        },
        x_doc,
        close_comments,
        ALLOC.text(")"),
    ])
}

/// Format a comma-separated list of expressions.
fn format_exps(
    exps: &Exps<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    if exps.0.is_empty() {
        return ALLOC.nil();
    }

    // Find commas at depth 0.
    let commas = cursor.find_all_at_depth0(end, |t| matches!(t, Token::Comma));
    let last_end = cursor.last_significant_end(end).unwrap_or(end);
    let mut bounds = vec![cursor.pos()];
    for c in &commas {
        bounds.push(*c);
    }
    bounds.push(last_end);

    let mut parts = Vec::new();
    for (i, e) in exps.0.iter().enumerate() {
        let e_end = bounds.get(i + 1).copied().unwrap_or(end);
        parts.push(format_exp(e, cursor, e_end, style));
        if i < exps.0.len() - 1 {
            // Emit comments before the comma.
            let comma_pos = commas.get(i).copied().unwrap_or(e_end);
            parts.push(cursor.advance_to(comma_pos));
            let ce = cursor.token_end(comma_pos).unwrap_or(comma_pos + 1);
            cursor.skip_to(ce);
            parts.push(ALLOC.text(", "));
        }
    }
    ALLOC.concat(parts)
}

fn format_binop_symbol(op: &BinOp) -> Doc<'static> {
    match op {
        BinOp::Add => ALLOC.text("+"),
        BinOp::Sub => ALLOC.text("-"),
        BinOp::Mul => ALLOC.text("*"),
        BinOp::Div => ALLOC.text("/"),
        BinOp::Pow => ALLOC.text("^"),
        BinOp::Dot => ALLOC.text("dot"),
        BinOp::Concat => ALLOC.text("++"),
        BinOp::Rem => ALLOC.text("%"),
    }
}
