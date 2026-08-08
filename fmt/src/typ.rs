//! Type formatting.

use lang::ast::{Size, Spanned};
use lang::parser::Token;
use lang::typ::{GTyp, Typ, TypeVar, TypeVars};
use share::DocAllocator;

use crate::ctx::{ALLOC, Doc};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::kind::format_kind;
use crate::size::{format_range, format_size};
use crate::style::Style;
use crate::trivia::{TokenCursor, TriviaGap, gap_none, gap_space, trim_if_clean};

pub(crate) fn format_typevars(
    typevars: &TypeVars<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let open_comments = gap_none(
        trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
        style,
    );
    let mut list = DelimList::new(style, ",", true);
    for (index, typevar) in typevars.0.iter().enumerate() {
        let (typevar_gap, typevar_doc) = format_typevar(typevar, cursor, style);
        if index + 1 < typevars.0.len() {
            let (before, after) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            list.push_sep(typevar_gap, typevar_doc, before, after);
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

pub(crate) fn format_typ(
    typ: &GTyp<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    match typ {
        Typ::Poly(base, m, n) => {
            // Detect whether the source uses sugar syntax (Uni/Mle) or full
            // Poly form. This determines how many args are in the source.
            let source_is_uni = cursor
                .peek_token(end, |t| matches!(t, Token::KwUni))
                .is_some();
            let source_is_mle = cursor
                .peek_token(end, |t| matches!(t, Token::KwMleTy))
                .is_some();
            let keyword_gap = cursor.advance_to_token(end, |token| {
                matches!(token, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
            });
            let open = gap_none(
                trim_if_clean(cursor.advance_to_token(end, |token| matches!(token, Token::LAngle))),
                style,
            );
            let base_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));

            // Consume gaps and format sizes. When the source is already in
            // sugar form (Uni/Mle), the skipped arg is implicit — don't try
            // to find it in the token stream.
            let (comma_one_b, comma_one_a) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            let (m_gap, m_doc) = if source_is_uni {
                (TriviaGap::default(), ALLOC.nil())
            } else {
                format_size(m, cursor, end, style)
            };
            let (comma_two_b, comma_two_a) = if source_is_uni || source_is_mle {
                (TriviaGap::default(), TriviaGap::default())
            } else {
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma))
            };
            let (n_gap, n_doc) = if source_is_mle {
                (TriviaGap::default(), ALLOC.nil())
            } else {
                format_size(n, cursor, end, style)
            };
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));

            // Uni<F, N> is sugar for Poly<F, 1, N>; Mle<F, N> is sugar for
            // Poly<F, N, 1>. Emit the sugar only when the AST matches AND
            // no comments are attached to the skipped argument's gaps.
            let is_uni = matches!(m, Size::Lit(1))
                && !comma_one_a.has_comments()
                && !comma_two_b.has_comments();
            let is_mle = matches!(n, Size::Lit(1))
                && !comma_two_a.has_comments()
                && !close_comments.has_comments();

            let name = if is_uni {
                "Uni"
            } else if is_mle {
                "Mle"
            } else {
                "Poly"
            };

            let mut list = DelimList::new(style, ",", true);
            list.push_sep(
                base_gap,
                ALLOC.text(base.to_string()),
                comma_one_b,
                comma_one_a,
            );
            if is_uni {
                list.push(n_gap, n_doc);
            } else if is_mle {
                list.push(m_gap, m_doc);
            } else {
                list.push_sep(m_gap, m_doc, comma_two_b, comma_two_a);
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
            let (semi_gap_b, semi_gap_a) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Semi));
            let (size_gap, size_doc) = format_size(size, cursor, end, style);
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RBrack));

            let mut list = DelimList::new(style, ";", false);
            list.push_sep(inner_gap, inner_doc, semi_gap_b, semi_gap_a);
            list.push(size_gap, size_doc);

            (open_gap, list.finish("[", "]", close_comments))
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
            let mut list = DelimList::new(style, ",", true);
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
            let mut list = DelimList::new(style, ",", true);
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

/// Format a list of `name: value` fields as comma-terminated items.
/// Used by both Typ::Record and Exp::Record.
pub(crate) fn format_field_items<N, T, F>(
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
            let (before, after) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            list.push_sep(name_gap, field, before, after);
        } else {
            list.push(name_gap, field);
        }
    }
}
