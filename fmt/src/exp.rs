//! Expression formatting.
//!
//! See crate-level docs for the gap ownership convention. Notable
//! cases in this module:
//!
//! - `format_body` — owns the gap after `{` (or between `{` and `}`).
//! - `format_relation` — owns the gap after `where`.
//! - `format_relation_inner` — does NOT own a leading gap; called by
//!   `format_relation` after the leading gap is consumed, and
//!   recursively for `;`-separated relations (where `gap_hard` after
//!   `;` provides the break).

use lang::ast::ExpId;
use lang::ast::exp::{BinOp, Exp, Exps, URef};
use lang::ast::{Block, Exclusion, Size, Spanned, Stmt};
use lang::id::Tid;
use lang::parser::Token;
use lang::stack_guard;
use pretty::DocAllocator;

use crate::ctx::{Doc, Formatter, parenthesize};
use crate::delim_list::{DelimList, take_separator_gap_split};
use crate::trivia::{TriviaGap, format_gap, gap_hard, gap_none, gap_space};

impl<'doc> Formatter<'doc, '_> {
    #[stack_guard]
    fn format_exp(&mut self, exp: URef<'_>) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let end = exp.span().end;
        let at = |id: &ExpId| exp.at(*id);
        match exp.node() {
            Exp::Lit(value) => self.format_size(value, end),
            Exp::Unit => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LParen));
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RParen));
                let list = DelimList::new(alloc, style, ",", true);
                (gap, list.finish("(", ")", close_comments))
            }
            Exp::Var(var) => {
                let gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                (gap, alloc.as_string(var))
            }
            Exp::Neg(inner) => {
                let inner = at(inner);
                let minus_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Minus));
                let (inner_gap, inner_doc) = self.format_exp(inner);
                let inner = parenthesize(alloc, inner_doc, inner.node().needs_paren_under_neg());
                (
                    minus_gap,
                    alloc.concat([
                        alloc.text("-"),
                        gap_none(alloc, inner_gap, style),
                        inner.group(),
                    ]),
                )
            }
            Exp::Bin(BinOp::Dot, lhs, rhs) => self.format_binary_call(
                "dot",
                |token| matches!(token, Token::KwDot),
                [at(lhs), at(rhs)],
                end,
            ),
            Exp::Bin(op, lhs, rhs) => {
                // Flatten left-associative same-operator chain:
                //   a * b * c  =  Bin(*, Bin(*, a, b), c)  →  [a, b, c]
                // so all operators align at the same indent instead of nesting
                // deeper for each left-recursion level.
                // Right-associative operators (Pow) are excluded: flattening
                //   (a ^ b) ^ c  =  Bin(^, Bin(^, a, b), c)  →  [a, b, c]
                // would output `a ^ b ^ c`, which re-parses as `a ^ (b ^ c)`.
                let mut inner_rhs_list: Vec<URef<'_>> = Vec::new();
                let mut current: URef<'_> = at(lhs);
                while let Exp::Bin(inner_op, inner_lhs, inner_rhs) = current.node() {
                    if inner_op == op && !op.is_right_assoc() {
                        inner_rhs_list.push(at(inner_rhs));
                        current = at(inner_lhs);
                    } else {
                        break;
                    }
                }
                inner_rhs_list.reverse();

                let mut chain: Vec<URef<'_>> = Vec::new();
                chain.push(current);
                chain.extend(inner_rhs_list);
                chain.push(at(rhs));

                let indent = style.indent_width() as isize;
                let mut parts = Vec::with_capacity(chain.len() * 3);

                // First operand — no operator before it.
                // Return its gap to the caller so the caller can apply
                // appropriate gap formatting (e.g. gap_none after `[`).
                let (first_gap, first_doc) = self.format_exp(chain[0]);
                let first = parenthesize(alloc, first_doc, op.lhs_needs_paren(chain[0].node()));
                parts.push(first);

                // Remaining operands — each preceded by `op`.
                for &operand in &chain[1..] {
                    let op_gap = self
                        .cursor
                        .advance_to_token(end, |token| matches_binop(*op, token));
                    let (operand_gap, operand_doc) = self.format_exp(operand);
                    let operand =
                        parenthesize(alloc, operand_doc, op.rhs_needs_paren(operand.node()));
                    // Line comments need a hardline after (forces break);
                    // inline block comments need nil (line() before op
                    // provides the space). When hardline is used, suppress
                    // line() to avoid double newline.
                    let needs_break = op_gap.needs_end_newline();
                    let op_end = if needs_break {
                        Some(alloc.hardline())
                    } else {
                        Some(alloc.nil())
                    };
                    let op_line = if needs_break {
                        alloc.nil()
                    } else {
                        alloc.line()
                    };
                    parts.push(
                        alloc
                            .concat([
                                format_gap(alloc, op_gap, None, op_end, None, style),
                                alloc.concat([op_line, alloc.text(binop_symbol(*op))]),
                                gap_space(alloc, operand_gap, style),
                                operand,
                            ])
                            .nest(indent),
                    );
                }

                (first_gap, alloc.concat(parts).group())
            }
            Exp::App(function, args) => {
                let function_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let open = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::LParen)),
                    style,
                );
                let mut list = DelimList::new(alloc, style, ",", true);
                self.format_exps_items(exp, args, end, &mut list);
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RParen));
                let args = list.finish("(", ")", close_comments);

                (
                    function_gap,
                    alloc.concat([alloc.as_string(function), open, args]),
                )
            }
            Exp::Interpolate(None, evals) => self.format_unary_call(
                "interpolate",
                |token| matches!(token, Token::KwInterpolate),
                at(evals),
                end,
            ),
            Exp::Interpolate(Some(points), evals) => self.format_binary_call(
                "interpolate",
                |token| matches!(token, Token::KwInterpolate),
                [at(points), at(evals)],
                end,
            ),
            Exp::Poly(value) => self.format_unary_call(
                "poly",
                |token| matches!(token, Token::KwPoly),
                at(value),
                end,
            ),
            Exp::Coef(value) => self.format_unary_call(
                "coef",
                |token| matches!(token, Token::KwCoef),
                at(value),
                end,
            ),
            Exp::Mle(value) => {
                self.format_unary_call("mle", |token| matches!(token, Token::KwMle), at(value), end)
            }
            Exp::Evaluate(poly, range, point) => {
                self.format_evaluate(at(poly), range.as_ref(), point.as_ref().map(at), end)
            }
            Exp::Vec(values) => {
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBrack));
                let mut list = DelimList::new(alloc, style, ",", true);
                self.format_exps_items(exp, values, end, &mut list);
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RBrack));
                (open_gap, list.finish("[", "]", close_comments))
            }
            Exp::Range(range) => self.format_range(range, end),
            Exp::Map(body, var, range) => {
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBrack));
                let (body_gap, body_doc) = self.format_seq_exp(at(body));
                let for_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwFor));
                let var_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let in_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwIn));
                let (range_gap, range_doc) = self.format_exp(at(range));
                let close = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::RBrack)),
                    style,
                );

                (
                    open_gap,
                    alloc.concat([
                        alloc.text("["),
                        alloc
                            .concat([
                                alloc.line_(),
                                alloc
                                    .concat([
                                        format_gap(
                                            alloc,
                                            body_gap.trim_start(),
                                            Some(alloc.nil()),
                                            None,
                                            None,
                                            style,
                                        ),
                                        body_doc,
                                    ])
                                    .group(),
                                gap_space(alloc, for_gap, style),
                                alloc.line_(),
                                alloc
                                    .concat([
                                        alloc.text("for"),
                                        gap_space(alloc, var_gap, style),
                                        alloc.as_string(var),
                                        gap_space(alloc, in_gap, style),
                                        alloc.text("in"),
                                        gap_space(alloc, range_gap, style),
                                        range_doc,
                                    ])
                                    .group(),
                                alloc.line_(),
                            ])
                            .nest(style.indent_width() as isize)
                            .group(),
                        close,
                        alloc.text("]"),
                    ]),
                )
            }
            Exp::Reduce(op, value) => {
                let keyword_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwReduce));
                let open = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::LParen)),
                    style,
                );
                let op_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches_binop(*op, token));
                let (comma_b, comma_a) = take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
                let (value_gap, value_doc) = self.format_exp(at(value));
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RParen));
                let mut list = DelimList::new(alloc, style, ",", true);
                list.push_sep(op_gap, alloc.text(binop_symbol(*op)), comma_b, comma_a);
                list.push(value_gap, value_doc);
                let args = list.finish("(", ")", close_comments);

                (
                    keyword_gap,
                    alloc.concat([alloc.text("reduce"), open, args]),
                )
            }
            Exp::Ram(base, index) => {
                let (base_gap, base_doc) = self.format_exp(at(base));
                let open = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::LBrack)),
                    style,
                );
                let (index_gap, index_doc) = self.format_exp(at(index));
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RBrack));
                let mut list = DelimList::new(alloc, style, ",", false);
                list.push(index_gap, index_doc);
                (
                    base_gap,
                    alloc.concat([
                        base_doc.group(),
                        open,
                        list.finish("[", "]", close_comments),
                    ]),
                )
            }
            Exp::Pair(lhs, rhs) => self.format_binary_call(
                "pair",
                |token| matches!(token, Token::KwPair),
                [at(lhs), at(rhs)],
                end,
            ),
            Exp::Random(typ, exclusion) => self.format_sampling(
                "random",
                |t| matches!(t, Token::KwRandom),
                typ,
                exclusion
                    .as_ref()
                    .map(|x| x.node.as_ref().map_values(|v| exp.at(*v))),
                end,
            ),
            Exp::Challenge(typ, exclusion) => self.format_sampling(
                "challenge",
                |t| matches!(t, Token::KwChallenge),
                typ,
                exclusion
                    .as_ref()
                    .map(|x| x.node.as_ref().map_values(|v| exp.at(*v))),
                end,
            ),
            Exp::Block(_) => {
                // Reached only from operand (`exp_no_seq`) positions, where the
                // source must have parenthesized the sequence: without parens
                // `(let a = b; a) + a` would print as `let a = b; a + a`.
                // Positions that accept a bare sequence use `format_seq_exp`.
                let (gap, doc) = self.format_seq_exp(exp);
                let doc = alloc
                    .concat([
                        alloc.text("("),
                        alloc
                            .concat([alloc.line_(), doc])
                            .nest(style.indent_width() as isize),
                        alloc.line_(),
                        alloc.text(")"),
                    ])
                    .group();
                (gap, doc)
            }
            Exp::Verify(exp) => {
                self.format_assertion("verify", |t| matches!(t, Token::KwVerify), at(exp), end)
            }
            Exp::Fun(vars, body) => {
                let keyword_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::KwFun));
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LParen));
                let mut list = DelimList::new(alloc, style, ",", true);
                for (index, var) in vars.iter().enumerate() {
                    let var_gap = self
                        .cursor
                        .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                    let var_doc = alloc.as_string(var);
                    if index + 1 < vars.len() {
                        let (before, after) =
                            take_separator_gap_split(&mut self.cursor, end, |token| {
                                matches!(token, Token::Comma)
                            });
                        list.push_sep(var_gap, var_doc, before, after);
                    } else {
                        list.push(var_gap, var_doc);
                    }
                }
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RParen));
                let arrow_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::FatArrow));
                let (body_gap, body_doc) = self.format_seq_exp(at(body));

                (
                    keyword_gap,
                    alloc.concat([
                        alloc.text("fun"),
                        gap_space(alloc, open_gap, style),
                        list.finish("(", ")", close_comments),
                        gap_space(alloc, arrow_gap, style),
                        alloc.text("=>"),
                        gap_space(alloc, body_gap, style),
                        body_doc.group(),
                    ]),
                )
            }
            Exp::Record(fields) => {
                let open_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::LBraceBar));
                let mut fields: Vec<_> = fields
                    .iter()
                    .map(|(name, value)| (name, at(value)))
                    .collect();
                fields.sort_by_key(|(_, value)| value.span().start);
                let mut list = DelimList::new(alloc, style, ",", true);
                self.format_field_items(
                    &fields,
                    |value| value.span().end,
                    |fmt, value, _end| fmt.format_exp(*value),
                    end,
                    &mut list,
                );
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::BarRBrace));
                (open_gap, list.finish("{|", "|}", close_comments))
            }
            Exp::Proj(base, field) => {
                let (base_gap, base_doc) = self.format_exp(at(base));
                let dot = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::Dot)),
                    style,
                );
                let field_comments = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::Id(_))),
                    style,
                );
                (
                    base_gap,
                    alloc.concat([
                        base_doc.group(),
                        dot,
                        alloc.text("."),
                        field_comments,
                        alloc.as_string(field),
                    ]),
                )
            }
            Exp::SetRecord(record, field, value) => {
                let (record_gap, record_doc) = self.format_exp(at(record));
                let dot = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::Dot)),
                    style,
                );
                let set = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::Id(_))),
                    style,
                );
                let open = gap_none(
                    alloc,
                    self.cursor
                        .advance_to_token(end, |token| matches!(token, Token::LParen)),
                    style,
                );
                let field_gap = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                let (comma_b, comma_a) = take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
                let (value_gap, value_doc) = self.format_exp(at(value));
                let close_comments = self
                    .cursor
                    .advance_to_token(end, |token| matches!(token, Token::RParen));
                let mut list = DelimList::new(alloc, style, ",", true);
                list.push_sep(field_gap, alloc.as_string(field), comma_b, comma_a);
                list.push(value_gap, value_doc);

                (
                    record_gap,
                    alloc.concat([
                        record_doc.group(),
                        dot,
                        alloc.text("."),
                        set,
                        alloc.text("set"),
                        open,
                        list.finish("(", ")", close_comments),
                    ]),
                )
            }
        }
    }

    /// Format an expression in a position whose grammar rule is the full `exp`
    /// (comprehension body, `fun` body, relation), where a `let`/`<-` sequence
    /// needs no parentheses. Everything else goes through `format_exp`.
    fn format_seq_exp(&mut self, exp: URef<'_>) -> (TriviaGap, Doc<'doc>) {
        match exp.node() {
            Exp::Block(_) => {
                // Hand the leading trivia back to the caller like every other
                // arm, so it is placed for the caller's context instead of by
                // `format_body_inner`'s statement-level `gap_none`.
                let gap = self.cursor.advance_to(exp.span().start).trim_if_clean();
                let doc = self.format_body_inner(exp);
                (gap, doc)
            }
            _ => self.format_exp(exp),
        }
    }

    fn format_unary_call(
        &mut self,
        name: &'static str,
        pred: impl Fn(&Token) -> bool,
        arg: URef<'_>,
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        self.format_call1(name, pred, |fmt| fmt.format_exp(arg), end)
    }

    /// `name(arg)`, with `arg` formatted by `format_arg`.
    fn format_call1(
        &mut self,
        name: &'static str,
        pred: impl Fn(&Token) -> bool,
        format_arg: impl FnOnce(&mut Self) -> (TriviaGap, Doc<'doc>),
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let keyword_gap = self.cursor.advance_to_token(end, pred);
        let open = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LParen)),
            style,
        );
        let (arg_gap, arg_doc) = format_arg(self);
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RParen));
        let mut list = DelimList::new(alloc, style, ",", true);
        list.push(arg_gap, arg_doc);

        (
            keyword_gap,
            alloc.concat([
                alloc.text(name),
                open,
                list.finish("(", ")", close_comments),
            ]),
        )
    }

    fn format_binary_call(
        &mut self,
        name: &'static str,
        pred: impl Fn(&Token) -> bool,
        [lhs, rhs]: [URef<'_>; 2],
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let keyword_gap = self.cursor.advance_to_token(end, pred);
        let open = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LParen)),
            style,
        );
        let (lhs_gap, lhs_doc) = self.format_exp(lhs);
        let (comma_comments_b, comma_comments_a) =
            take_separator_gap_split(&mut self.cursor, end, |token| matches!(token, Token::Comma));
        let (rhs_gap, rhs_doc) = self.format_exp(rhs);
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RParen));
        let mut list = DelimList::new(alloc, style, ",", true);
        list.push_sep(lhs_gap, lhs_doc, comma_comments_b, comma_comments_a);
        list.push(rhs_gap, rhs_doc);

        (
            keyword_gap,
            alloc.concat([
                alloc.text(name),
                open,
                list.finish("(", ")", close_comments),
            ]),
        )
    }

    fn format_evaluate(
        &mut self,
        poly: URef<'_>,
        range: Option<&lang::ast::Range<Size>>,
        point: Option<URef<'_>>,
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let keyword_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::KwEval));
        let selector = if let Some(range) = range {
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
            alloc.concat([open, list.finish("<", ">", close_comments)])
        } else {
            alloc.nil()
        };

        let open = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LParen)),
            style,
        );
        let (poly_gap, poly_doc) = self.format_exp(poly);

        let mut list = DelimList::new(alloc, style, ",", true);
        if let Some(point) = point {
            let (comma_comments_b, comma_comments_a) =
                take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
            list.push_sep(poly_gap, poly_doc, comma_comments_b, comma_comments_a);
            let (point_gap, point_doc) = self.format_exp(point);
            list.push(point_gap, point_doc);
        } else {
            list.push(poly_gap, poly_doc);
        }
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RParen));

        (
            keyword_gap,
            alloc.concat([
                alloc.text("eval"),
                selector,
                open,
                list.finish("(", ")", close_comments),
            ]),
        )
    }

    fn format_sampling(
        &mut self,
        name: &'static str,
        pred: impl Fn(&Token) -> bool,
        typ: &Tid,
        exclusion: Option<Exclusion<URef<'_>, &Spanned<Size>>>,
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let keyword_gap = self.cursor.advance_to_token(end, pred);
        let open = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LAngle)),
            style,
        );
        let typ_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::Id(_)));
        let exclusion = match exclusion {
            None => alloc.nil(),
            Some(Exclusion::Values(values)) => {
                self.format_excluded(end, |fmt| fmt.format_exp(values))
            }
            Some(Exclusion::RootsOfUnity(n)) => self.format_excluded(end, |fmt| {
                fmt.format_call1(
                    "roots_of_unity",
                    |token| matches!(token, Token::KwRootsOfUnity),
                    |fmt| fmt.format_size(&n.node, end),
                    end,
                )
            }),
        };
        let content = alloc.concat([alloc.as_string(typ), exclusion]);
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RAngle));

        let mut list = DelimList::new(alloc, style, ",", true);
        list.push(typ_gap, content);
        (
            keyword_gap,
            alloc.concat([
                alloc.text(name),
                open,
                list.finish("<", ">", close_comments),
            ]),
        )
    }

    /// ` - ` followed by what a sample excludes, which `excluded` formats.
    fn format_excluded(
        &mut self,
        end: usize,
        excluded: impl FnOnce(&mut Self) -> (TriviaGap, Doc<'doc>),
    ) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        let minus_gap = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::Minus));
        let (excluded_gap, excluded_doc) = excluded(self);
        alloc.concat([
            gap_space(alloc, minus_gap, style),
            alloc.text("-"),
            gap_space(alloc, excluded_gap, style),
            excluded_doc,
        ])
    }

    fn format_assertion(
        &mut self,
        name: &'static str,
        pred: impl Fn(&Token) -> bool,
        exp: URef<'_>,
        end: usize,
    ) -> (TriviaGap, Doc<'doc>) {
        let alloc = self.alloc;
        let style = self.style;
        let keyword_gap = self.cursor.advance_to_token(end, pred);
        let open = gap_none(
            alloc,
            self.cursor
                .advance_to_token(end, |token| matches!(token, Token::LParen)),
            style,
        );
        let (exp_gap, exp_doc) = self.format_exp(exp);
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RParen));
        let mut list = DelimList::new(alloc, style, ",", true);
        list.push(exp_gap, exp_doc);
        (
            keyword_gap,
            alloc.concat([
                alloc.text(name),
                open,
                list.finish("(", ")", close_comments),
            ]),
        )
    }

    fn format_exps_items(
        &mut self,
        parent: URef<'_>,
        exps: &Exps,
        end: usize,
        list: &mut DelimList<'doc, '_>,
    ) {
        for (index, exp) in exps.iter().enumerate() {
            let (exp_gap, exp_doc) = self.format_exp(parent.at(exp));
            if index + 1 < exps.0.len() {
                let (before, after) = take_separator_gap_split(&mut self.cursor, end, |token| {
                    matches!(token, Token::Comma)
                });
                list.push_sep(exp_gap, exp_doc, before, after);
            } else {
                list.push(exp_gap, exp_doc);
            }
        }
    }

    pub(crate) fn format_relation(&mut self, exp: URef<'_>) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        // Leading gap — between `where` and the first relation.
        // `line()` as open for inline comments (space in flat, newline in
        // broken); at_line_start comments get auto `hardline` open.
        // `line()` as sep for empty gaps (separates `where` from relation).
        let leading_gap = self.cursor.advance_to(exp.span().start).trim_start();
        let leading_open = match leading_gap.first() {
            Some(e) if !e.needs_start_newline() => Some(alloc.line()),
            _ => None,
        };
        let leading = format_gap(
            alloc,
            leading_gap,
            leading_open,
            None,
            Some(alloc.line()),
            style,
        );

        let content = self.format_relation_inner(exp);
        alloc.concat([leading, content])
    }

    fn format_relation_inner(&mut self, exp: URef<'_>) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        match exp.node() {
            Exp::Block(body) => self.format_stmts(exp, body, true),
            _ => {
                let (gap, doc) = self.format_seq_exp(exp);
                alloc.concat([
                    format_gap(alloc, gap, Some(alloc.nil()), None, None, style),
                    doc,
                ])
            }
        }
    }

    pub(crate) fn format_body(&mut self, body: Option<URef<'_>>, end: usize) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        let Some(body) = body else {
            // Empty body — comments between `{` and `}`. Empty gap → nil.
            // Line comments always go on their own line (even if inline in
            // source after `{`), so `open = hardline` when the gap forces a
            // break. `end` is auto (hardline for breaking, space for inline).
            let inner_comments = self
                .cursor
                .advance_to_token(end, |token| matches!(token, Token::RBrace))
                .trim();
            let open = if inner_comments.needs_end_newline() {
                Some(alloc.hardline())
            } else {
                Some(alloc.text(" "))
            };
            return format_gap(alloc, inner_comments, open, None, Some(alloc.nil()), style);
        };

        // Gap after `{` — strip blank lines. `sep = hardline` provides
        // the structural break for empty gaps; `open = hardline` puts
        // comments on their own line; `end = hardline` breaks after.
        let body_leading = format_gap(
            alloc,
            self.cursor.advance_to(body.span().start).trim_start(),
            Some(alloc.hardline()),
            Some(alloc.hardline()),
            Some(alloc.hardline()),
            style,
        );
        let body_doc = self.format_body_inner(body);

        // Gap before `}` — strip blank lines (structural hardline precedes).
        let close_comments = self
            .cursor
            .advance_to_token(end, |token| matches!(token, Token::RBrace))
            .trim_end();

        alloc.concat([
            body_leading,
            body_doc,
            gap_hard(alloc, close_comments, style),
        ])
    }

    fn format_body_inner(&mut self, exp: URef<'_>) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        match exp.node() {
            Exp::Block(body) => self.format_stmts(exp, body, false),
            _ => {
                let (gap, doc) = self.format_exp(exp);
                // Body context: comments go on their own line. `open = nil`
                // because body_leading already provides the initial line break;
                // `end = hardline` breaks after the comment; `sep = nil` for
                // empty gaps (body_leading handles the break).
                alloc.concat([
                    format_gap(
                        alloc,
                        gap,
                        Some(alloc.nil()),
                        Some(alloc.hardline()),
                        Some(alloc.nil()),
                        style,
                    ),
                    doc,
                ])
            }
        }
    }

    /// Render the gap before `;`. Inline comments get no trailing space
    /// (`;` follows immediately); line comments get a hardline after
    /// (`;` goes on the next line).
    fn gap_before_semi(&self, gap: TriviaGap) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        let needs_break = gap.needs_end_newline();
        let end = if needs_break {
            Some(alloc.hardline())
        } else {
            Some(alloc.nil())
        };
        format_gap(alloc, gap, None, end, None, style)
    }

    /// A block's statements, each through its `;`, then its value. In a relation (`where`), a
    /// value statement keeps the relation's gap style; a `<-` statement switches the rest of the
    /// block to the body's.
    fn format_stmts(&mut self, expr: URef<'_>, block: &Block, mut relation: bool) -> Doc<'doc> {
        let alloc = self.alloc;
        let style = self.style;
        let tail = block.tail.map(|t| expr.at(t));
        let mut docs = Vec::new();
        for (i, stmt) in block.stmts.iter().enumerate() {
            let end = stmt.span.end;
            relation &= !matches!(stmt.node, Stmt::Log(..));
            docs.push(match &stmt.node {
                Stmt::Let(var, value) => {
                    let keyword = gap_none(
                        alloc,
                        self.cursor
                            .advance_to_token(end, |token| matches!(token, Token::KwLet)),
                        style,
                    );
                    let name_gap = self
                        .cursor
                        .advance_to_token(end, |token| matches!(token, Token::Id(_)));
                    let eq_gap = self
                        .cursor
                        .advance_to_token(end, |token| matches!(token, Token::Eq));
                    let (value_gap, value_doc) = self.format_exp(expr.at(*value));
                    alloc.concat([
                        keyword,
                        alloc.text("let"),
                        gap_space(alloc, name_gap, style),
                        alloc.as_string(var),
                        gap_space(alloc, eq_gap, style),
                        alloc.text("="),
                        gap_space(alloc, value_gap, style),
                        value_doc,
                    ])
                }
                // The value is an operand (`exp_no_seq`): a block there was parenthesized in the
                // source and must stay so, which `format_exp` does.
                Stmt::Discard(value) if relation => {
                    let (value_gap, value_doc) = self.format_exp(expr.at(*value));
                    alloc.concat([
                        format_gap(alloc, value_gap, Some(alloc.nil()), None, None, style),
                        value_doc,
                    ])
                }
                Stmt::Discard(value) => {
                    let (value_gap, value_doc) = self.format_exp(expr.at(*value));
                    alloc.concat([gap_none(alloc, value_gap, style), value_doc])
                }
                Stmt::Log(var, value) => {
                    let name = gap_none(
                        alloc,
                        self.cursor
                            .advance_to_token(end, |token| matches!(token, Token::Id(_))),
                        style,
                    );
                    let arrow_gap = self
                        .cursor
                        .advance_to_token(end, |token| matches!(token, Token::LArrow));
                    let (value_gap, value_doc) = self.format_exp(expr.at(*value));
                    alloc.concat([
                        name,
                        alloc.as_string(var),
                        gap_space(alloc, arrow_gap, style),
                        alloc.text("<-"),
                        gap_space(alloc, value_gap, style),
                        value_doc,
                    ])
                }
            });
            let before_semi = self
                .cursor
                .advance_to_token(end, |token| matches!(token, Token::Semi));
            docs.push(self.gap_before_semi(before_semi));
            docs.push(alloc.text(";"));
            let next = block
                .stmts
                .get(i + 1)
                .map(|s| s.span.start)
                .or(tail.map(|t| t.span().start));
            if let Some(next) = next {
                docs.push(gap_hard(alloc, self.cursor.advance_to(next), style));
            }
        }
        if let Some(tail) = tail {
            docs.push(if relation {
                self.format_relation_inner(tail)
            } else {
                self.format_body_inner(tail)
            });
        }
        alloc.concat(docs)
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
        BinOp::Equ => matches!(token, Token::EqEq),
        BinOp::And => matches!(token, Token::AmpAmp),
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
        BinOp::Equ => "==",
        BinOp::And => "&&",
    }
}
