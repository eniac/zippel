use std::fmt;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};

use share::{Proj1, Proj2, Traversable2, Traversable1, BoxAllocator, Pretty, DocAllocator, DocBuilder};
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

/// Modular get/set acccess to expression annotations using [Proj1] and [Proj2]
impl<N, A, B> Proj1<A> for BExp<N, (A, B)> {
    type Output<Z> = BExp<N, (Z, B)>;

    fn get_proj1(&self) -> &A {
        match self {
            BExp::Eq(_, _, t) => &t.0,
            BExp::App(_, _, t) => &t.0,
            BExp::Contains(_, _, t) => &t.0,
            BExp::And(_, _, t) => &t.0,
            BExp::Or(_, _, t) => &t.0,
        }
    }

    fn map_proj1<Z>(self, f: &mut dyn FnMut(A)->Z) -> Self::Output<Z> {
        match self {
            BExp::Eq(a, b, (x, y)) =>
                BExp::Eq(a.map_proj1(f), b.map_proj1(f), (f(x), y)),
            BExp::App(id, v, (x, y)) =>
                BExp::App(id, AExps(v.0.into_iter().map(|e| e.map_proj1(f)).collect()), (f(x), y)),
            BExp::Contains(a, b, (x, y)) =>
                BExp::contains(a.map_proj1(f), b.map_proj1(f), (f(x), y)),
            BExp::And(box a, box b, (x, y)) =>
                BExp::and(a.map_proj1(f), b.map_proj1(f), (f(x), y)),
            BExp::Or(box a, box b, (x, y)) =>
                BExp::or(a.map_proj1(f), b.map_proj1(f), (f(x), y)),
        }
    }

    fn modify_proj1(&mut self, f: &mut dyn FnMut(&mut A)) {
        match self {
            BExp::Eq(a, b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x);
            },
            BExp::App(_, v, (x, _)) => {
                for e in v.0.iter_mut() {
                    e.modify_proj1(f);
                }
                f(x);
            },
            BExp::Contains(a, b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x);
            },
            BExp::And(box a, box b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x);
            },
            BExp::Or(box a, box b, (x, _)) => {
                a.modify_proj1(f);
                b.modify_proj1(f);
                f(x);
            }
        }
    }
}

impl<N, A, B> Proj2<B> for BExp<N, (A, B)> {
    type Output<Z> = BExp<N, (A, Z)>;

    fn get_proj2(&self) -> &B {
        match self {
            BExp::Eq(_, _, t) => &t.1,
            BExp::App(_, _, t) => &t.1,
            BExp::Contains(_, _, t) => &t.1,
            BExp::And(_, _, t) => &t.1,
            BExp::Or(_, _, t) => &t.1,
        }
    }

    fn map_proj2<Z>(self, f: &mut dyn FnMut(B)->Z) -> Self::Output<Z> {
        match self {
            BExp::Eq(a, b, (x, y)) =>
                BExp::Eq(a.map_proj2(f), b.map_proj2(f), (x, f(y))),
            BExp::App(id, v, (x, y)) =>
                BExp::App(id, AExps(v.0.into_iter().map(|e| e.map_proj2(f)).collect()), (x, f(y))),
            BExp::Contains(a, b, (x, y)) =>
                BExp::contains(a.map_proj2(f), b.map_proj2(f), (x, f(y))),
            BExp::And(box a, box b, (x, y)) =>
                BExp::and(a.map_proj2(f), b.map_proj2(f), (x, f(y))),
            BExp::Or(box a, box b, (x, y)) =>
                BExp::or(a.map_proj2(f), b.map_proj2(f), (x, f(y))),
        }
    }

    fn modify_proj2(&mut self, f: &mut dyn FnMut(&mut B)) {
        match self {
            BExp::Eq(a, b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y);
            },
            BExp::App(_, v, (_, y)) => {
                for e in v.0.iter_mut() {
                    e.modify_proj2(f);
                }
                f(y);
            },
            BExp::Contains(a, b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y);
            },
            BExp::And(box a, box b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y);
            },
            BExp::Or(box a, box b, (_, y)) => {
                a.modify_proj2(f);
                b.modify_proj2(f);
                f(y);
            }
        }
    }
}

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
                Ok(BExp::contains(
                    a.traverse1(f)?,
                    b.traverse1(f)?,
                    t
                )),
            BExp::And(box a, box b, t) =>
                Ok(BExp::and(
                    a.traverse1(f)?,
                    b.traverse1(f)?,
                       t
                )),
            BExp::Or(box a, box b, t) =>
                Ok(BExp::or(
                    a.traverse1(f)?,
                    b.traverse1(f)?,
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
                Ok(BExp::contains(
                    a.traverse2(f)?,
                    b.traverse2(f)?,
                    f(t)?,
                )),
            BExp::And(box a, box b, t) =>
                Ok(BExp::and(
                a.traverse2(f)?,
                b.traverse2(f)?,
                f(t)?
            )),
            BExp::Or(box a, box b, t) => Ok(BExp::or(
                a.traverse2(f)?,
                b.traverse2(f)?,
                f(t)?
            )),
        }
    }
}

/// Constructor for BExp
impl<N, T> BExp<N, T> {
    pub fn and(l: Self, r: Self, t: T) -> Self {
        BExp::And(Box::new(l), Box::new(r), t)
    }
    pub fn or(l: Self, r: Self, t: T) -> Self {
        BExp::Or(Box::new(l), Box::new(r), t)
    }
    pub fn eq(l: AExp<N, T>, r: AExp<N, T>, t: T) -> Self {
        BExp::Eq(l, r, t)
    }
    pub fn app(id: Fid, args: AExps<N, T>, t: T) -> Self {
        BExp::App(id, args, t)
    }
    pub fn contains(a: AExp<N, T>, b: AExp<N, T>, t: T) -> Self {
        BExp::Contains(a, b, t)
    }
}

/// Constructor for Untyped, symbolic sized BExp
impl UBExp {
    pub fn uand(l: Self, r: Self) -> Self {
        BExp::and(l, r, Nothing)
    }
    pub fn uor(l: Self, r: Self) -> Self {
        BExp::or(l, r, Nothing)
    }
    pub fn ueq(l: UAExp, r: UAExp) -> Self {
        BExp::eq(l, r, Nothing)
    }
    pub fn uapp(id: Fid, args: UAExps) -> Self {
        BExp::App(id, args, Nothing)
    }
    pub fn ucontains(a: UAExp, b: UAExp) -> Self {
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
                    Ok(BExp::ueq(
                        UAExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?,
                        UAExp::from_pest(&mut Pairs::single(inner.next().unwrap()))?
                    ))
                },
                Rule::contains_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(BExp::ucontains(
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
                    Ok(BExp::uapp(func, params))
                },
                Rule::bexp => BExp::from_pest(&mut pair.into_inner()),
                _ => unreachable!()
            })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::and_op => Ok(BExp::uand(lhs?, rhs?)),
                    Rule::or_op => Ok(BExp::uor(lhs?, rhs?)),
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
        Ok(UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)))
    )
}

#[test]
fn parser_and() {
    let ex = "(x == 2) && (0 == 0)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::uand(
            UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)),
            UBExp::ueq(UAExp::ulit(0), UAExp::ulit(0))
        ))
    )
}

#[test]
fn parser_or() {
    let ex = "x == 2 || 0 == 0";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::uor(
            UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)),
            UBExp::ueq(UAExp::ulit(0), UAExp::ulit(0))
        ))
    )
}

#[test]
fn parser_contains() {
    let ex = "x in [1, 2]";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::ucontains(
            UAExp::uvarstr("x"),
            UAExp::uvec(vec![UAExp::ulit(1), UAExp::ulit(2)])
        ))
    )
}

#[test]
fn parser_call() {
    let ex = "proto(x) && foo(y)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).unwrap();
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(BExp::uand(
            BExp::uapp(Fid::from("proto"), AExps(vec![AExp::uvarstr("x")])),
            BExp::uapp(Fid::from("foo"), AExps(vec![AExp::uvarstr("y")]))
        ))
    );
}

#[test]
fn parser_and_or1() {
    let ex = "x == 2 && (x == 2 || 0 == 0)";
    let mut pairs = ZippelParser::parse(Rule::bexp, ex).expect("Failure to parse");
    assert_eq!(
        UBExp::from_pest(&mut pairs),
        Ok(UBExp::uand(
            UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)),
            UBExp::uor(
                UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)),
                UBExp::ueq(UAExp::ulit(0), UAExp::ulit(0))
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
        Ok(UBExp::uand(
            UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)),
            UBExp::uor(
                UBExp::ueq(UAExp::uvarstr("x"), UAExp::ulit(2)),
                UBExp::ueq(UAExp::ulit(0), UAExp::ulit(0))
            )
        ))
    )
}
