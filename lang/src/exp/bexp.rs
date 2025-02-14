use std::fmt;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::{Traversable2, Traversable1, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use crate::typ::{Typ, Size, Nothing};
use crate::exp::{AExp, UAExp, AExps, UAExps};
use crate::id::Fid;

/// Represents boolean expressions in the Zippel language.
/// It is parameterized by the type `A` of annotations:
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum BExp<N, T> {

    ///     Represents an application of a protocol to a list of arguments.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(sumcheck(a, b, c));
    ///     ```
    App(Fid, AExps<N, T>, T),

    ///     Represents inclusion of an element in a vector
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     assert(x in v);
    ///     ```
    Contains(AExp<N, T>, AExp<N, T>, T),

    ///     Represents the equality comparison between two arithmetic expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = (5 == 5);
    ///     ```
    ///
    ///     **Rust Representation:**
    ///     ```rust
    ///     BExp::Eq(AExp::Lit(5), AExp::Lit(5))
    ///     ```
    Eq(AExp<N, T>, AExp<N, T>, T),

    ///     Represents the logical AND of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = (true && false);
    ///     ```
    ///
    ///     **Rust Representation:**
    ///     ```rust
    ///     BExp::And(Box::new(BExp::TrueE), Box::new(BExp::FalseE))
    ///     ```
    And(Box<BExp<N, T>>, Box<BExp<N, T>>, T),

    ///     Represents the logical OR of two boolean expressions.
    ///
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = (true || false);
    ///     ```
    ///
    ///     **Rust Representation:**
    ///     ```rust
    ///     BExp::Or(Box::new(BExp::TrueE), Box::new(BExp::FalseE))
    ///     ```
    Or(Box<BExp<N, T>>, Box<BExp<N, T>>, T),
}

/// Typed AST node
pub type TBExp<N, A> = BExp<N, (A, Typ<N>)>;

/// Untyped AST node with symbolic sizes
pub type UBExp = BExp<Size, Nothing>;

/// Implement get/set operations on the type parameters using [Traversable1] and [Traversable2]
impl<N, T> Traversable1<N> for BExp<N, T> {
    type Output<Z> = BExp<Z, T>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<BExp<Z, T>, E> {
        match self {
            BExp::Eq(a, b, t) =>
                Ok(BExp::Eq(a.traverse1(f)?, b.traverse1(f)?, t)),
            BExp::App(id, v, t) =>
                Ok(BExp::App(id, v.traverse1(f)?, t)),
            BExp::Contains(a, b, t) =>
                Ok(BExp::Contains(
                    a.traverse1(f)?,
                    b.traverse1(f)?,
                    t
                )),
            BExp::And(box a, box b, t) =>
                Ok(BExp::And(
                    Box::new(a.traverse1(f)?),
                    Box::new(b.traverse1(f)?),
                    t
                )),
            BExp::Or(box a, box b, t) =>
                Ok(BExp::Or(
                    Box::new(a.traverse1(f)?),
                    Box::new(b.traverse1(f)?),
                    t
                ))
        }
    }
}

impl<N, T> Traversable2<T> for BExp<N, T> {
    type Output<Z> = BExp<N, Z>;

    fn traverse2<Z, E>(self, f: &mut dyn FnMut(T) -> Result<Z, E>) -> Result<BExp<N, Z>, E> {
        match self {
            BExp::Eq(a, b, t) => Ok(BExp::Eq(a.traverse2(f)?, b.traverse2(f)?, f(t)?)),
            BExp::App(id, v, t) =>
                Ok(BExp::App(id, v.traverse2(f)?, f(t)?)),
            BExp::Contains(a, b, t) =>
                Ok(BExp::Contains(
                    a.traverse2(f)?,
                    b.traverse2(f)?,
                    f(t)?,
                )),
            BExp::And(box a, box b, t) =>
                Ok(BExp::And(
                    Box::new(a.traverse2(f)?),
                    Box::new(b.traverse2(f)?),
                    f(t)?
                )),
            BExp::Or(box a, box b, t) =>
                Ok(BExp::Or(
                    Box::new(a.traverse2(f)?),
                    Box::new(b.traverse2(f)?),
                    f(t)?
                ))
        }
    }
}

/// Constructor for BExp
impl UBExp {
    pub fn and(l: Self, r: Self) -> Self {
        BExp::And(Box::new(l), Box::new(r), Nothing)
    }
    pub fn or(l: Self, r: Self) -> Self {
        BExp::Or(Box::new(l), Box::new(r), Nothing)
    }
    pub fn eq(l: UAExp, r: UAExp) -> Self {
        BExp::Eq(l, r, Nothing)
    }
    pub fn app(id: Fid, args: UAExps) -> Self {
        BExp::App(id, args, Nothing)
    }
    pub fn contains(a: UAExp, b: UAExp) -> Self {
        BExp::Contains(a, b, Nothing)
    }
}

/// Pretty printer instance
impl<'a, D, A, N, T> Pretty<'a, D, A> for BExp<N, T>
where
    T: Pretty<'a, D, A>,
    N: Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            BExp::Eq(a, b, t) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" == "),
                b.pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            BExp::App(id, args, t) => allocator.concat([
                id.pretty(allocator),
                allocator.text("("),
                args.pretty(allocator),
                allocator.text(")"),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            BExp::And(a, b, t) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" && "),
                (*b).pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            BExp::Or(a, b, t) => allocator.concat([
                (*a).pretty(allocator),
                allocator.text(" || "),
                (*b).pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
            BExp::Contains(a, b, t) => allocator.concat([
                a.pretty(allocator),
                allocator.text(" in "),
                b.pretty(allocator),
                if t.is_nil() {
                    allocator.nil()
                } else {
                    allocator.text(" ⇝ ").append(t.pretty(allocator))
                }]),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N, T> fmt::Display for BExp<N, T>
where
    N: Clone + Pretty<'a, BoxAllocator, ()>,
    T: Clone + Pretty<'a, BoxAllocator, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <BExp<N, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
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
                    Ok(BExp::eq(
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
fn parser_eq() {
    let ex = "x == 2";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::eq(UAExp::varstr("x"), UAExp::from(2)))
    )
}

#[test]
fn parser_and() {
    let ex = "(x == 2) && (0 == 0)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::and(
            UBExp::eq(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::eq(UAExp::from(0), UAExp::from(0))
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
            UBExp::eq(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::eq(UAExp::from(0), UAExp::from(0))
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
            UBExp::eq(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::or(
                UBExp::eq(UAExp::varstr("x"), UAExp::from(2)),
                UBExp::eq(UAExp::from(0), UAExp::from(0))
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
            UBExp::eq(UAExp::varstr("x"), UAExp::from(2)),
            UBExp::or(
                UBExp::eq(UAExp::varstr("x"), UAExp::from(2)),
                UBExp::eq(UAExp::from(0), UAExp::from(0))
            )
        ))
    )
}
