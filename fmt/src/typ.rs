//! Type formatting.

use lang::ast::{Size, Spanned};
use lang::id::Tid;
use lang::parser::Token;
use lang::stack_guard;
use lang::typ::{GTyp, PolyTyp, Typ, TypeVar, TypeVars};
use pretty::DocAllocator;

use crate::ctx::{Doc, Formatter};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::trivia::{TriviaGap, gap_none, gap_space};

impl<'doc> Formatter<'doc, '_> {
    pub(crate) fn format_typevars(&mut self, typevars: &TypeVars<Size>, end: usize) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        let open_comments = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LAngle)),
            style,
        );
        let mut list = DelimList::new(alloc, style, ",", true);
        for (index, typevar) in typevars.0.iter().enumerate() {
            let (typevar_gap, typevar_doc) = self.format_typevar(typevar);
            if index + 1 < typevars.0.len() {
                let (before, after) = take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
                list.push_sep(typevar_gap, typevar_doc, before, after);
            } else {
                list.push(typevar_gap, typevar_doc);
            }
        }
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RAngle));
        alloc.concat([open_comments, list.finish("<", ">", close_comments)])
    }

    fn format_typevar(&mut self, typevar: &Spanned<TypeVar<Size>>) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let end = typevar.span.end;
        let id_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::Id(_)));
        let colon = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::Colon)),
            style,
        );
        let (kind_gap, kind_doc) = self.format_kind(&typevar.node.kind, end);
        let doc = alloc.concat([
            alloc.as_string(&typevar.node.id.node),
            colon,
            alloc.text(":"),
            gap_space(alloc, kind_gap, style),
            kind_doc,
        ]);
        (id_gap, doc)
    }

    #[stack_guard]
    pub(crate) fn format_typ(&mut self, typ: &GTyp<Size>, end: usize) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        match typ {
            Typ::Poly(base, shape) => {
                let keyword = match shape {
                    PolyTyp::Uni { .. } => "Uni",
                    PolyTyp::Mle { .. } => "Mle",
                    PolyTyp::General { .. } => "Poly",
                };
                let sizes: Vec<&Size> = shape.sizes().into_iter().map(|s| &s.node).collect();
                self.format_poly(keyword, base, &sizes, end)
            }
            Typ::Vec(typ, size) => {
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBrack));
                let (inner_gap, inner_doc) = self.format_typ(&typ.node, typ.span.end);
                let (semi_gap_b, semi_gap_a) =
                    take_separator_gap_split(&mut self.cursor, end, |token| {
                        matches!(token, Token::Semi)
                    });
                let (size_gap, size_doc) = self.format_size(size, end);
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RBrack));

                let mut list = DelimList::new(alloc, style, ";", false);
                list.push_sep(inner_gap, inner_doc, semi_gap_b, semi_gap_a);
                list.push(size_gap, size_doc);

                (open_gap, list.finish("[", "]", close_comments))
            }
            Typ::Base(base) => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                (gap, alloc.as_string(base))
            }
            Typ::Fin(range) => {
                let keyword_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwFin));
                let open = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::LAngle)),
                    style,
                );
                let (range_gap, range_doc) = self.format_range(range, end);
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RAngle));
                let mut list = DelimList::new(alloc, style, ",", true);
                list.push(range_gap, range_doc);
                (
                    keyword_gap,
                    alloc.concat([
                        alloc.text("Fin"),
                        open,
                        list.finish("<", ">", close_comments),
                    ]),
                )
            }
            Typ::Unit => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwUnit));
                (gap, alloc.text("Unit"))
            }
            Typ::Bool => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwBool));
                (gap, alloc.text("Bool"))
            }
            Typ::FieldLiteral => {
                unreachable!("field literals are internal and have no source syntax")
            }
            Typ::Record(fields) => {
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBrace));
                let mut fields: Vec<_> = fields.iter().collect();
                fields.sort_by_key(|(_, typ)| typ.span.start);
                let mut list = DelimList::new(alloc, style, ",", true);
                self.format_field_items(
                    &fields,
                    |typ| typ.span.end,
                    |fmt, typ, end| fmt.format_typ(&typ.node, end),
                    end,
                    &mut list,
                );
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RBrace));
                (open_gap, list.finish("{", "}", close_comments))
            }
        }
    }
}

impl<'doc> Formatter<'doc, '_> {
    /// Format a polynomial type `name<base, sizes...>` (`Uni<F, D>`, `Mle<F, N>` or
    /// `Poly<F, V, D>`), keeping the comments around each argument.
    fn format_poly(
        &mut self,
        name: &'static str,
        base: &Tid,
        sizes: &[&Size],
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let keyword_gap = self.cursor.advance_to_token(end, |t| {
            matches!(t, Token::KwPolyTy | Token::KwUni | Token::KwMleTy)
        });
        let open = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |t| matches!(t, Token::LAngle)),
            style,
        );
        let base_gap = self
            .cursor
            .advance_to_token(end, |t| matches!(t, Token::Id(_)));
        let mut list = DelimList::new(alloc, style, ",", true);
        let (mut comma_b, mut comma_a) =
            take_separator_gap_split(&mut self.cursor, end, |t| matches!(t, Token::Comma));
        list.push_sep(base_gap, alloc.as_string(base), comma_b, comma_a);
        let (last, init) = sizes.split_last().expect("a polynomial type has a size");
        for size in init {
            let (gap, doc) = self.format_size(size, end);
            (comma_b, comma_a) =
                take_separator_gap_split(&mut self.cursor, end, |t| matches!(t, Token::Comma));
            list.push_sep(gap, doc, comma_b, comma_a);
        }
        let (gap, doc) = self.format_size(last, end);
        list.push(gap, doc);
        let close_comments = self
            .cursor
            .advance_to_token(end, |t| matches!(t, Token::RAngle));
        (
            keyword_gap,
            alloc.concat([
                alloc.text(name),
                open,
                list.finish("<", ">", close_comments),
            ]),
        )
    }

    /// Format a list of `name: value` fields as comma-terminated items.
    /// Used by both Typ::Record and Exp::Record.
    pub(crate) fn format_field_items<N, V, F>(
        &mut self,
        fields: &[(&N, V)],
        value_end: impl Fn(&V) -> usize,
        format_value: F,
        end: usize,
        list: &mut DelimList<'doc, '_>,
    ) where
        N: std::fmt::Display,
        F: Fn(&mut Self, &V, usize) -> (TriviaGap, Doc<'doc>),
    {
        let alloc = self.alloc;
        let style = self.style;
        for (index, (name, value)) in fields.iter().enumerate() {
            let name_gap = self
                .cursor
                .advance_to_token(end, |token| matches!(token, Token::Id(_)));
            let colon = gap_none(
                alloc,
                self.cursor
                    .advance_to_token(end, |token| matches!(token, Token::Colon)),
                style,
            );
            let (value_gap, value_doc) = format_value(self, value, value_end(value));
            let field = alloc.concat([
                alloc.as_string(name),
                colon,
                alloc.text(":"),
                gap_space(alloc, value_gap, style),
                value_doc,
            ]);
            if index + 1 < fields.len() {
                let (before, after) = take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
                list.push_sep(name_gap, field, before, after);
            } else {
                list.push(name_gap, field);
            }
        }
    }
}
