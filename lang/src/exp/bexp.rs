use std::fmt;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::traversal::ToTraversal1;
use share::{BoxAllocator, Pretty, DocAllocator, DocBuilder};
use crate::typ::{Size, Range, RangeTraversal};
use crate::exp::{AExp, UAExp, AExps, UAExps, AExpTraversal};
use crate::id::{Tid, TidTraversal, Fid};

/// Represents boolean expressions in the Zippel language.
/// It is parameterized by the type `A` of annotations:
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum BExp<N> {
    ///     Represents an application of a protocol to a list of arguments.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(sumcheck(a, b, c));
    ///     ```
    App(Fid, AExps<N>),

    ///     Represents inclusion of an element in a vector
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(x in v);
    ///     ```
    Contains(AExp<N>, AExp<N>),

    ///     Represents the equality comparison between two arithmetic expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(5 == 5);
    ///     ```
    Equ(AExp<N>, AExp<N>),

    ///     Represents the logical AND of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(true && false);
    ///     ```
    And(Box<BExp<N>>, Box<BExp<N>>),

    ///     Represents the logical OR of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(true || false);
    ///     ```
    Or(Box<BExp<N>>, Box<BExp<N>>),

    ///     Represents the negation of a boolean expression.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(!true);
    ///     ```
    Not(Box<BExp<N>>),
}

/// Untyped AST node with symbolic sizes
pub type UBExp = BExp<Size>;

/// Untyped AST node with concrete sizes
pub type CBExp = BExp<usize>;

/// Traverse parameter (N) inside BExp
impl<N> ToTraversal1<N> for BExp<N> {
    type Output<Z> = BExp<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<BExp<Z>, E> {
        match self {
            BExp::Equ(a, b) =>
                Ok(BExp::Equ(a.traverse1(f)?, b.traverse1(f)?)),
            BExp::App(id, v) =>
                Ok(BExp::App(id, v.aexp_traverse(&mut |x| x.traverse1(f))? )),
            BExp::Contains(a, b) =>
                Ok(BExp::Contains(a.traverse1(f)?, b.traverse1(f)?)),
            BExp::And(a, b) =>
                Ok(BExp::And(a.traverse1(&mut |x| x.traverse1(f))?, b.traverse1(&mut |x| x.traverse1(f))?)),
            BExp::Or(a, b) =>
                Ok(BExp::Or(a.traverse1(&mut |x| x.traverse1(f))?, b.traverse1(&mut |x| x.traverse1(f))?)),
            BExp::Not(a) => Ok(BExp::Not(a.traverse1(&mut |x| x.traverse1(f))?)),
        }
    }
}

/// Traverse [Tid] inside [TBExp]
impl TidTraversal for CBExp {
    fn tid_traverse<E>(self, f: &mut dyn FnMut(Tid) -> Result<Tid, E>) -> Result<Self, E> {
        match self {
            BExp::Equ(a, b) =>
                Ok(BExp::Equ(a.tid_traverse(f)?, b.tid_traverse(f)?)),
            BExp::App(id, v) =>
                Ok(BExp::App(id, v.tid_traverse(f)?)),
            BExp::Contains(a, b) =>
                Ok(BExp::Contains(a.tid_traverse(f)?, b.tid_traverse(f)?)),
            BExp::And(a, b) =>
                Ok(BExp::And(
                    a.traverse1(&mut |x| x.tid_traverse(f))?,
                    b.traverse1(&mut |x| x.tid_traverse(f))?
                )),
            BExp::Or(a, b) =>
                Ok(BExp::Or(
                    a.traverse1(&mut |x| x.tid_traverse(f))?,
                    b.traverse1(&mut |x| x.tid_traverse(f))?
                )),
            BExp::Not(a) =>
                Ok(BExp::Not(a.traverse1(&mut |x| x.tid_traverse(f))?)),
        }
    }
}

impl<N> RangeTraversal<N> for BExp<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        match self {
            BExp::Equ(a, b) =>
                Ok(BExp::Equ(a.range_traverse(f)?, b.range_traverse(f)?)),
            BExp::App(id, v) =>
                Ok(BExp::App(id, v.range_traverse(f)?)),
            BExp::Contains(a, b) =>
                Ok(BExp::Contains(a.range_traverse(f)?, b.range_traverse(f)?)),
            BExp::And(a, b) =>
                Ok(BExp::And(a.traverse1(&mut |x| x.range_traverse(f))?, b.traverse1(&mut |x| x.range_traverse(f))?)),
            BExp::Or(a, b) =>
                Ok(BExp::Or(a.traverse1(&mut |x| x.range_traverse(f))?, b.traverse1(&mut |x| x.range_traverse(f))?)),
            BExp::Not(a) =>
                Ok(BExp::Not(a.traverse1(&mut |x| x.range_traverse(f))?)),
        }
    }
}

/// Constructor for BExp
impl<N> BExp<N> {
    pub fn and(l: Self, r: Self) -> Self {
        BExp::And(Box::new(l), Box::new(r))
    }
    pub fn or(l: Self, r: Self) -> Self {
        BExp::Or(Box::new(l), Box::new(r))
    }
    pub fn equ(l: AExp<N>, r: AExp<N>) -> Self {
        BExp::Equ(l, r)
    }
    pub fn app(id: Fid, args: AExps<N>) -> Self {
        BExp::App(id, args)
    }
    pub fn contains(a: AExp<N>, b: AExp<N>) -> Self {
        BExp::Contains(a, b)
    }
    pub fn not(a: Self) -> Self {
        BExp::Not(Box::new(a))
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for BExp<N>
where
    N: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            BExp::Equ(a, b) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" == "),
                b.pretty(allocator),
            ]),
            BExp::App(id, args) => allocator.concat([
                id.pretty(allocator),
                allocator.text("("),
                args.pretty(allocator),
                allocator.text(")"),
            ]),
            BExp::And(a, b) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" && "),
                (*b).pretty(allocator),
            ]),
            BExp::Or(a, b) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" || "),
                (*b).pretty(allocator),
            ]),
            BExp::Contains(a, b) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" in "),
                b.pretty(allocator),
            ]),
            BExp::Not(a) => allocator.concat([
                allocator.text("!"),
                (*a).pretty(allocator),
            ]),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for BExp<N>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <BExp<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

lazy_static! {
    pub static ref BOOL_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(and_op, Left))
            .op(Op::infix(or_op, Left))
    };
}

impl<'pest> FromPest<'pest> for UBExp {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        BOOL_PARSER
            .map_primary(|pair| match pair.as_rule() {
                Rule::eq_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(BExp::equ(
                        UAExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        UAExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::contains_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(BExp::contains(
                        UAExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        UAExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::not_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(BExp::not(UBExp::from_pest(&mut inner)?))
                },
                Rule::app_bexp => {
                    let mut inner = pair.into_inner();
                    // Call a protocol
                    let func = Fid::from_pest(&mut inner)?;
                    // Parameters
                    let params = UAExps::from_pest(&mut inner)?;
                    Ok(BExp::app(func, params))
                },
                Rule::bexp => BExp::from_pest(&mut pair.into_inner()),
                _ => unreachable!()
            })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::and_op => Ok(BExp::and(lhs?, rhs?)),
                    Rule::or_op => Ok(BExp::or(lhs?, rhs?)),
                    _ => unreachable!(),
                })
            .parse(expression)
    }
}


/// BExp parser tests
#[cfg(test)] use pest::Parser;
#[test]
fn parser_equ() {
    let ex = "x == 2";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::equ(UAExp::varstr("x"), UAExp::from(2)))
    )
}

#[test]
fn parser_and() {
    let ex = "(x == 2) && (0 == 0)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::and(
            UBExp::equ(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::equ(UAExp::from(0), UAExp::from(0))
        ))
    )
}

#[test]
fn parser_or() {
    let ex = "x == 2 || 0 == 0";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::or(
            UBExp::equ(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::equ(UAExp::from(0), UAExp::from(0))
        ))
    )
}

#[test]
fn parser_contains() {
    let ex = "x in [1, 2]";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::contains(
            UAExp::varstr("x"),
            UAExp::vec(vec![UAExp::from(1), UAExp::from(2)])
        ))
    )
}

#[test]
fn parser_call() {
    let ex = "proto(x) && foo(y)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).unwrap();
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(BExp::and(
            BExp::app(Fid::from("proto"), AExps(vec![AExp::varstr("x")])),
            BExp::app(Fid::from("foo"), AExps(vec![AExp::varstr("y")]))
        ))
    );
}

#[test]
fn parser_and_or1() {
    let ex = "x == 2 && (x == 2 || 0 == 0)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::and(
            UBExp::equ(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::or(
                UBExp::equ(UAExp::varstr("x"), UAExp::from(2)),
                UBExp::equ(UAExp::from(0), UAExp::from(0))
            )
        ))
    )
}

#[test]
fn parser_and_or2() {
    let ex = "x == 2 && x == 2 || 0 == 0";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::and(
            UBExp::equ(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::or(
                UBExp::equ(UAExp::varstr("x"), UAExp::from(2)),
                UBExp::equ(UAExp::from(0), UAExp::from(0))
            )
        ))
    )
}

#[test]
fn parser_not() {
    let ex = "!x == 0";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::not(UBExp::equ(UAExp::varstr("x"), UAExp::lit(Size::from(0)))))
    )
}
