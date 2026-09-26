//! Type formatting.

use lang::ast::{Size, Spanned};
use lang::id::Tid;
use lang::parser::Token;
use lang::typ::{GTyp, Typ, TypeVar, TypeVars};
use pretty::DocAllocator;

use crate::ctx::{ALLOC, Doc};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::kind::format_kind;
use crate::size::{format_range, format_size};
use crate::style::Style;
use crate::trivia::{TokenCursor, TriviaGap, gap_none, gap_space};

pub(crate) fn format_typevars(
    typevars: &TypeVars<Size>,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> Doc<'static> {
    let open_comments = gap_none(
        cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
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
        cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
        style,
    );
    let (kind_gap, kind_doc) = format_kind(&typevar.node.kind, cursor, end, style);
    let doc = ALLOC.concat([
        ALLOC.as_string(&typevar.node.id.node),
        colon,
        ALLOC.text(":"),
        gap_space(kind_gap, style),
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
        Typ::Poly(base, m, n) => format_poly(base, m, n, cursor, end, style),
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
            (gap, ALLOC.as_string(base))
        }
        Typ::Fin(range) => {
            let keyword_gap = cursor.advance_to_token(end, |token| matches!(token, Token::KwFin));
            let open = gap_none(
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
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
        Typ::Bool => (TriviaGap::default(), ALLOC.text("Bool")),
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

/// Which sugar form the source uses — determines cursor traversal.
enum SourceForm {
    Poly, // Poly<F, M, N> — 3 args in source
    Uni,  // Uni<F, N>    — 2 args, M=1 implicit
    Mle,  // Mle<F, N>    — 2 args, N=1 implicit
}

/// Format `Poly<F, M, N>`, emitting `Uni`/`Mle` sugar when the AST
/// matches and no comments are attached to the skipped argument.
///
/// Two independent concerns:
/// - **Source form** (Uni/Mle/Poly): how many tokens to consume from the
///   cursor. Detected by peeking at the keyword token.
/// - **Output form** (Uni/Mle/Poly): whether to emit sugar. Decided by
///   checking if the AST values match the sugar pattern AND no comments
///   are attached to the gaps that would be dropped.
fn format_poly(
    base: &Tid,
    m: &Size,
    n: &Size,
    cursor: &mut TokenCursor,
    end: usize,
    style: &Style,
) -> (TriviaGap, Doc<'static>) {
    // ── Phase 1: Detect source form ──
    let source = if cursor
        .peek_token(end, |t| matches!(t, Token::KwUni))
        .is_some()
    {
        SourceForm::Uni
    } else if cursor
        .peek_token(end, |t| matches!(t, Token::KwMleTy))
        .is_some()
    {
        SourceForm::Mle
    } else {
        SourceForm::Poly
    };

    // ── Phase 2: Consume tokens from cursor ──
    // All three forms share: keyword, `<`, base, `,`.
    let keyword_gap = cursor.advance_to_token(end, |t| {
        matches!(t, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
    });
    let open = gap_none(
        cursor.advance_to_token(end, |t| matches!(t, Token::LAngle)),
        style,
    );
    let base_gap = cursor.advance_to_token(end, |t| matches!(t, Token::Id(_)));
    let (comma1_b, comma1_a) = take_separator_gap_split(cursor, end, |t| matches!(t, Token::Comma));

    // After the first comma, the forms diverge:
    //   Poly: M, `,`, N    — both sizes present
    //   Uni:  N            — M=1 is implicit, skip it
    //   Mle:  M            — N=1 is implicit, skip it
    let (m_gap, m_doc, comma2_b, comma2_a, n_gap, n_doc) = match source {
        SourceForm::Poly => {
            let (m_gap, m_doc) = format_size(m, cursor, end, style);
            let (comma2_b, comma2_a) =
                take_separator_gap_split(cursor, end, |t| matches!(t, Token::Comma));
            let (n_gap, n_doc) = format_size(n, cursor, end, style);
            (m_gap, m_doc, comma2_b, comma2_a, n_gap, n_doc)
        }
        SourceForm::Uni => {
            // M is implicit — only N is in the source
            let (n_gap, n_doc) = format_size(n, cursor, end, style);
            (
                TriviaGap::default(),
                ALLOC.nil(),
                TriviaGap::default(),
                TriviaGap::default(),
                n_gap,
                n_doc,
            )
        }
        SourceForm::Mle => {
            // N is implicit — only M is in the source
            let (m_gap, m_doc) = format_size(m, cursor, end, style);
            (
                m_gap,
                m_doc,
                TriviaGap::default(),
                TriviaGap::default(),
                TriviaGap::default(),
                ALLOC.nil(),
            )
        }
    };
    let close_comments = cursor.advance_to_token(end, |t| matches!(t, Token::RAngle));

    // ── Phase 3: Decide output form ──
    // If the source is already in sugar form, preserve it — comments are
    // already in the right places. Only apply comment-loss checks when
    // converting from Poly to sugar (where skipping an arg would drop
    // its attached comments).
    let (is_uni, is_mle) = match source {
        SourceForm::Uni if matches!(m, Size::Lit(1)) => (true, false),
        SourceForm::Mle if matches!(n, Size::Lit(1)) => (false, true),
        _ => {
            // Poly→sugar: only if no comments on the skipped arg's gaps.
            // Uni<F, N> skips M, so check gaps around M (comma1_a, comma2_b).
            // Mle<F, N> skips N, so check gaps around N (comma2_a, close).
            let is_uni =
                matches!(m, Size::Lit(1)) && !comma1_a.has_comments() && !comma2_b.has_comments();
            let is_mle = matches!(n, Size::Lit(1))
                && !comma2_a.has_comments()
                && !close_comments.has_comments();
            (is_uni, is_mle)
        }
    };

    // ── Phase 4: Build doc ──
    let name = if is_uni {
        "Uni"
    } else if is_mle {
        "Mle"
    } else {
        "Poly"
    };

    let mut list = DelimList::new(style, ",", true);
    list.push_sep(base_gap, ALLOC.as_string(base), comma1_b, comma1_a);
    if is_uni {
        list.push(n_gap, n_doc);
    } else if is_mle {
        list.push(m_gap, m_doc);
    } else {
        list.push_sep(m_gap, m_doc, comma2_b, comma2_a);
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
            cursor.advance_to_token(end, |token| matches!(token, Token::Colon)),
            style,
        );
        let (value_gap, value_doc) = format_value(value, cursor, value.span.end, style);
        let field = ALLOC.concat([
            ALLOC.as_string(name),
            colon,
            ALLOC.text(":"),
            gap_space(value_gap, style),
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
