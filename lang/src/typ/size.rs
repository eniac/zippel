use from_pest::{ConversionError, FromPest};
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use std::ops::{Add, Sub, Mul, Div};
use std::fmt;
use thiserror::Error;
use lazy_static::lazy_static;

use crate::id::Tid;
use crate::parser::*;
use share::{Ctx, Set};
use share::{Pretty, DocBuilder, DocAllocator, BoxAllocator};

lazy_static! {
    pub static ref SIZE_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add_op, Left) | Op::infix(sub_op, Left))
            .op(Op::infix(mul_op, Left) | Op::infix(div_op, Left))
            .op(Op::infix(pow_op, Right))
            .op(Op::infix(max_op, Left) | Op::infix(min_op, Left))
    };
}

impl<'pest> FromPest<'pest> for BExp<Nothing> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        SIZE_PARSER
            .map_primary(|pair| match pair.as_rule() {
                // LEF: Copied from BExp parser, adapt to size_ty from zippel.pest
                Rule::eq_bexp => {
                    let mut inner = pair.into_inner();
                    Ok(BExp::eq(
                        AExp::from_pest(&mut inner)?,
                        AExp::from_pest(&mut inner)?
                    ))
                },
                Rule::app_bexp => {
                    let mut inner = pair.into_inner();
                    let func = Fid::from_pest(&mut inner)?;
                    let mut ve = Vec::new();
                    for x in inner {
                        ve.push(AExp::from_pest(&mut Pairs::single(x))?);
                    }
                    Ok(BExp::app(func, ve))
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Size {
    Var(Tid),            // N
    Lit(u32),            // 15
    Bin(Box<Size>),      // 2^N
    Add(Box<Size>, Box<Size>), // A + B
    Sub(Box<Size>, Box<Size>), // A - B
    Mul(Box<Size>, Box<Size>), // A * B
    Div(Box<Size>, Box<Size>), // A / B
    Max(Box<Size>, Box<Size>), // max(A, B)
    Min(Box<Size>, Box<Size>), // min(A, B)
}

impl Size {
    pub fn var(id: Tid) -> Self {
        Size::Var(id)
    }

    pub fn varstr<'a>(v: &'a str) -> Self {
        Size::var(Tid::from(v))
    }

    pub fn bin(b: Size) -> Self {
        Size::Bin(Box::new(b))
    }

    pub fn max(a: Size, b: Size) -> Self {
        Size::Max(Box::new(a), Box::new(b))
    }

    pub fn min(a: Size, b: Size) -> Self {
        Size::Min(Box::new(a), Box::new(b))
    }

    pub fn neg(self) -> Self {
        Size::Lit(0) - self
    }

    pub fn zero() -> Self {
        Size::Lit(0)
    }

    pub fn one() -> Self {
        Size::Lit(1)
    }

    pub fn free_vars(&self) -> Set<Tid> {
        match self {
            Size::Var(id) => Set::from([id.clone()]),
            Size::Lit(_) => Set::new(),
            Size::Bin(b) => b.free_vars(),
            Size::Add(a, b) => a.free_vars().union(b.free_vars()),
            Size::Sub(a, b) => a.free_vars().union(b.free_vars()),
            Size::Mul(a, b) => a.free_vars().union(b.free_vars()),
            Size::Div(a, b) => a.free_vars().union(b.free_vars()),
            Size::Max(a, b) => a.free_vars().union(b.free_vars()),
            Size::Min(a, b) => a.free_vars().union(b.free_vars()),
        }
    }

    pub fn eval(&self, ctx: &Ctx<Tid, u8>) -> Option<u64> {
        match self {
            Size::Var(id) => ctx.get(id).map(|&x| x as u64),
            Size::Lit(i) => Some(*i as u64),
            Size::Bin(box b) => b.eval(ctx).map(|x| 1 << x),
            Size::Add(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Some(x + y)
            }
            Size::Sub(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Some(x - y)
            }
            Size::Mul(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Some(x * y)
            }
            Size::Div(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                if y != 0 {
                    Some(x / y)
                } else {
                    None
                }
            }
            Size::Max(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Some(x.max(y))
            }
            Size::Min(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Some(x.min(y))
            }
        }
    }

    pub fn multieval(&self, ctx: Ctx<Tid, Set<u8>>) -> Set<u64> {
        let free = self.free_vars();

        ctx.into_iter()
               .filter(|(k, _)| free.contains(k))
               .map(|(k, v)| v.into_iter().map(|x| (k.clone(), x)).collect::<Vec<_>>())
               .multi_cartesian_product()
               .filter_map(|vals| self.eval(&Ctx::from(vals)))
               .collect::<Set<u64>>()
    }
}

// Which size to choose?


//////////////////////////////////////////////////////////////////////////////////////////////
/// Addition of sizes
//////////////////////////////////////////////////////////////////////////////////////////////
impl Add for Size {
    type Output = Size;
    fn add(self, other: Self) -> Self::Output {
        Size::Add(Box::new(self), Box::new(other))
    }
}
impl Add<u32> for Size {
    type Output = Size;
    fn add(self, other: u32) -> Self::Output {
        Size::Add(Box::new(self), Box::new(Size::Lit(other)))
    }
}
impl Add<Tid> for Size {
    type Output = Size;
    fn add(self, other: Tid) -> Self::Output {
        Size::Add(Box::new(self), Box::new(Size::Var(other)))
    }
}
impl Add for &Size {
    type Output = Size;
    fn add(self, other: Self) -> Self::Output {
        self.clone() + other.clone()
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////
/// Subtraction of sizes
//////////////////////////////////////////////////////////////////////////////////////////////
impl Sub for Size {
    type Output = Size;
    fn sub(self, other: Self) -> Self::Output {
        Size::Sub(Box::new(self), Box::new(other))
    }
}
impl Sub<u32> for Size {
    type Output = Size;
    fn sub(self, other: u32) -> Self::Output {
        Size::Sub(Box::new(self), Box::new(Size::Lit(other)))
    }
}
impl Sub<Tid> for Size {
    type Output = Size;
    fn sub(self, other: Tid) -> Self::Output {
        Size::Sub(Box::new(self), Box::new(Size::Var(other)))
    }
}
impl Sub for &Size {
    type Output = Size;
    fn sub(self, other: Self) -> Self::Output {
        self.clone() - other.clone()
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////
/// Multiplication of sizes
//////////////////////////////////////////////////////////////////////////////////////////////
impl Mul for Size {
    type Output = Size;
    fn mul(self, other: Self) -> Self::Output {
        Size::Mul(Box::new(self), Box::new(other))
    }
}
impl Mul<u32> for Size {
    type Output = Size;
    fn mul(self, other: u32) -> Self::Output {
        Size::Mul(Box::new(self), Box::new(Size::Lit(other)))
    }
}
impl Mul<Tid> for Size {
    type Output = Size;
    fn mul(self, other: Tid) -> Self::Output {
        Size::Sub(Box::new(self), Box::new(Size::Var(other)))
    }
}
impl Mul for &Size {
    type Output = Size;
    fn mul(self, other: Self) -> Self::Output {
        self.clone() * other.clone()
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////
/// Division of sizes
//////////////////////////////////////////////////////////////////////////////////////////////
impl Div for Size {
    type Output = Size;
    fn div(self, other: Self) -> Self::Output {
        Size::Div(Box::new(self), Box::new(other))
    }
}
impl Div<u32> for Size {
    type Output = Size;
    fn div(self, other: u32) -> Self::Output {
        Size::Div(Box::new(self), Box::new(Size::Lit(other)))
    }
}
impl Div<Tid> for Size {
    type Output = Size;
    fn div(self, other: Tid) -> Self::Output {
        Size::Div(Box::new(self), Box::new(Size::Var(other)))
    }
}
impl Div for &Size {
    type Output = Size;
    fn div(self, other: Self) -> Self::Output {
        self.clone() / other.clone()
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////
/// Pretty printing, display and Arbitrary for Size
//////////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Size
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Size::Var(id) => id.pretty(allocator),
            Size::Lit(n) => allocator.text(n.to_string()),
            Size::Bin(box b) => allocator.text("2^").append(b.pretty(allocator)),
            Size::Add(box a, box b) => a.pretty(allocator).append(allocator.text(" + ")).append(b.pretty(allocator)),
            Size::Sub(box a, box b) => a.pretty(allocator).append(allocator.text(" - ")).append(b.pretty(allocator)),
            Size::Mul(box a, box b) => a.pretty(allocator).append(allocator.text(" * ")).append(b.pretty(allocator)),
            Size::Div(box a, box b) => a.pretty(allocator).append(allocator.text(" / ")).append(b.pretty(allocator)),
            Size::Max(box a, box b) => allocator.text("max(").append(a.pretty(allocator)).append(allocator.text(", ")).append(b.pretty(allocator)).append(allocator.text(")")),
            Size::Min(box a, box b) => allocator.text("min(").append(a.pretty(allocator)).append(allocator.text(", ")).append(b.pretty(allocator)).append(allocator.text(")")),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a> fmt::Display for Size {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Size as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'pest> FromPest<'pest> for Size {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::size_ty => Size::from_pest(&mut pair.into_inner()),
            Rule::
            Rule::typ => Typ::from_pest(&mut pair.into_inner()), // Go into typ here
            Rule::tid => Ok(Typ::Base(Tid::from_pest(&mut pair.into_inner())?)),
            Rule::uni_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::Uni(id, size))
            }
            Rule::mle_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::Mle(id, size))
            }
            Rule::ind_ty =>
                Ok(Typ::Index(Range::from_pest(&mut pair.into_inner())?)),
            Rule::vec_ty => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut inner)?;
                let size = Size::from_pest(&mut inner)?;
                Ok(Typ::Vec(id, size))
            }
            Rule::mat_ty => {
                let mut innest = pair.into_inner();
                let base = Tid::from_pest(&mut innest)?;
                // Lef: The Pratt parser is too greedy.
                // Split A1, A2 in [F; A1, A2] before calling it.
                let mut pn = Pairs::single(innest.next().ok_or(ConversionError::NoMatch)?);
                let mut pm = Pairs::single(innest.next().ok_or(ConversionError::NoMatch)?);
                let n = Size::from_pest(&mut pn)?;
                let m = Size::from_pest(&mut pm)?;
                Ok(Typ::Mat(base, n, m))
            }
            _ => unreachable!(),
        }
    }
}

/// Arbitrary instance for Size
#[cfg(test)] use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)]
impl<'a> Arbitrary<'a> for Size {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let variant = u.choose(&[
            0, 1, 2, 3, 4, 5, 6, 7, 8
        ])?;

        Ok(match variant {
            0 => Size::Var(u.arbitrary()?),
            1 => Size::Lit(u.arbitrary()?),
            2 => Size::Bin(Box::new(u.arbitrary()?)),
            3 => Size::Add(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            4 => Size::Sub(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            5 => Size::Mul(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            6 => Size::Div(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            7 => Size::Max(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            8 => Size::Min(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            _ => unreachable!(),
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/// Prop tests
////////////////////////////////////////////////////////////////////////////////////////
#[cfg(test)] use arbtest::arbtest;
#[test]
fn test_size_add_prop() {
    // Associativity of addition
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;
        let b = u.arbitrary::<Size>()?;
        let c = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        b.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        c.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = (a + b) + c;
        let r = a + (b + c);
        assert_eq!(l.eval(ctx), r.eval(ctx));
        Ok(())
    });

    // Commutativity of addition
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;
        let b = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        b.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = a + b;
        let r = b + a;
        assert_eq!(l.eval(ctx), r.eval(ctx));
        Ok(())
    });


    // Unit of addition
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = a;
        let r1 = a + Size::zero();
        let r2 = Size::zero() + a;
        assert_eq!(l.eval(ctx), r1.eval(ctx));
        assert_eq!(l.eval(ctx), r2.eval(ctx));
        Ok(())
    });
}


#[test]
fn test_size_sub_prop() {
    // Distributivity of Subtraction
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;
        let b = u.arbitrary::<Size>()?;
        let c = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        b.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        c.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = a - (b + c);
        let r = a - b - c;
        assert_eq!(l.eval(ctx), r.eval(ctx));
        Ok(())
    });

    // Unit of subtraction and involution
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = a;
        let r1 = a - Size::zero();
        let r2 = a.neg().neg();
        assert_eq!(l.eval(ctx), r1.eval(ctx));
        assert_eq!(l.eval(ctx), r2.eval(ctx));
        Ok(())
    });
}

#[test]
fn test_size_mul_prop() {
    // Associativity of Multiplication
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;
        let b = u.arbitrary::<Size>()?;
        let c = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        b.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        c.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = (a * b) * c;
        let r = a * (b * c);
        assert_eq!(l.eval(ctx), r.eval(ctx));
        Ok(())
    });

    // Commutativity of addition
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;
        let b = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });
        b.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = a * b;
        let r = b * a;
        assert_eq!(l.eval(ctx), r.eval(ctx));
        Ok(())
    });


    // Unit of addition
    arbtest(|u| {
        let a = u.arbitrary::<Size>()?;

        let mut ctx = Ctx::new();
        a.free_vars().into_iter().for_each(|x| { ctx.insert(x, u.arbitrary()?); });

        let l = a;
        let r1 = a * Size::one();
        let r2 = Size::one() * a;
        assert_eq!(l.eval(ctx), r1.eval(ctx));
        assert_eq!(l.eval(ctx), r2.eval(ctx));
        Ok(())
    });
}
