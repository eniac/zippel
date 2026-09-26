//! Kind formatting.

use lang::parser::Token;
use lang::typ::Kind;
use pretty::DocAllocator;

use crate::ctx::{ALLOC, Doc};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::size::format_range;
use crate::style::Style;
use crate::trivia::{TokenCursor, TriviaGap, gap_none};

pub(crate) fn format_kind(
    kind: &Kind<lang::ast::Size>,
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
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
                style,
            );
            let ids_len = ids.len();
            let mut list = DelimList::new(style, ",", true);
            for (index, id) in ids.iter().enumerate() {
                let id_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let id_doc = ALLOC.as_string(id);
                if index + 1 < ids_len {
                    let (before, after) = take_separator_gap_split(cursor, end, |token| {
                        matches!(token, Token::Comma)
                    });
                    list.push_sep(id_gap, id_doc, before, after);
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
                cursor.advance_to_token(end, |token| matches!(token, Token::LAngle)),
                style,
            );
            let first_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let (comma_b, comma_a) =
                take_separator_gap_split(cursor, end, |token| matches!(token, Token::Comma));
            let second_gap = cursor.advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let close_comments =
                cursor.advance_to_token(end, |token| matches!(token, Token::RAngle));
            let mut list = DelimList::new(style, ",", true);
            list.push_sep(first_gap, ALLOC.as_string(g1), comma_b, comma_a);
            list.push(second_gap, ALLOC.as_string(g2));
            let args = list.finish("<", ">", close_comments);
            (
                keyword_gap,
                ALLOC.concat([ALLOC.text("Pairing"), open, args]),
            )
        }
        Kind::Range(range) => format_range(range, cursor, end, style),
    }
}
