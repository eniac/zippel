use from_pest::{ConversionError, FromPest};
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use std::ops::{Add, Sub, Mul, Div, Rem, BitXor};
use std::fmt;
use pest::Parser;
use thiserror::Error;
use lazy_static::lazy_static;
use itertools::Itertools;

use crate::id::Tid;
use crate::parser::*;
use share::{Ctx, Set};
use share::{Pretty, DocBuilder, DocAllocator, BoxAllocator};


#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Size {
    Var(Tid),            // N
    Lit(u32),            // 15
    Add(Box<Size>, Box<Size>), // A + B
    Sub(Box<Size>, Box<Size>), // A - B
    Mul(Box<Size>, Box<Size>), // A * B
    Div(Box<Size>, Box<Size>), // A / B
    Mod(Box<Size>, Box<Size>), // A % B
    Pow(Box<Size>, Box<Size>), // A ^ B
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
            Size::Add(a, b) => a.free_vars().union(b.free_vars()),
            Size::Sub(a, b) => a.free_vars().union(b.free_vars()),
            Size::Mul(a, b) => a.free_vars().union(b.free_vars()),
            Size::Div(a, b) => a.free_vars().union(b.free_vars()),
            Size::Mod(a, b) => a.free_vars().union(b.free_vars()),
            Size::Pow(a, b) => a.free_vars().union(b.free_vars()),
            Size::Max(a, b) => a.free_vars().union(b.free_vars()),
            Size::Min(a, b) => a.free_vars().union(b.free_vars()),
        }
    }

    pub fn eval(&self, ctx: &Ctx<Tid, u8>) -> Option<u64> {
        match self {
            Size::Var(id) => ctx.get(id).map(|&x| x as u64),
            Size::Lit(i) => Some(*i as u64),
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
            Size::Mod(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                if y != 0 {
                    Some(x % y)
                } else {
                    None
                }
            }
            Size::Pow(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Some(x.pow(y as u32))
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

/// Addition of sizes
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
impl Add<&Size> for Size {
    type Output = Size;
    fn add(self, other: &Size) -> Self::Output {
        Size::add(self, other.clone())
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
impl Add<Size> for &Size {
    type Output = Size;
    fn add(self, other: Size) -> Self::Output {
        Size::add(self.clone(), other)
    }
}

/// Subtraction of sizes
impl Sub for Size {
    type Output = Size;
    fn sub(self, other: Self) -> Self::Output {
        Size::Sub(Box::new(self), Box::new(other))
    }
}
impl Sub<&Size> for Size {
    type Output = Size;
    fn sub(self, other: &Size) -> Self::Output {
        Size::sub(self, other.clone())
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
impl Sub<Size> for &Size {
    type Output = Size;
    fn sub(self, other: Size) -> Self::Output {
        Size::sub(self.clone(), other)
    }
}

/// Multiplication of sizes
impl Mul for Size {
    type Output = Size;
    fn mul(self, other: Self) -> Self::Output {
        Size::Mul(Box::new(self), Box::new(other))
    }
}
impl Mul<&Size> for Size {
    type Output = Size;
    fn mul(self, other: &Size) -> Self::Output {
        Size::mul(self, other.clone())
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
        Size::Mul(Box::new(self), Box::new(Size::Var(other)))
    }
}
impl Mul for &Size {
    type Output = Size;
    fn mul(self, other: Self) -> Self::Output {
        self.clone() * other.clone()
    }
}
impl Mul<Size> for &Size {
    type Output = Size;
    fn mul(self, other: Size) -> Self::Output {
        Size::mul(self.clone(), other)
    }
}

/// Division of sizes
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
impl Div<&Size> for Size {
    type Output = Size;
    fn div(self, other: &Size) -> Self::Output {
        Size::div(self, other.clone())
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
impl Div<Size> for &Size {
    type Output = Size;
    fn div(self, other: Size) -> Self::Output {
        Size::div(self.clone(), other)
    }
}

/// Modulo of sizes
impl Rem for Size {
    type Output = Size;
    fn rem(self, other: Self) -> Self::Output {
        Size::Mod(Box::new(self), Box::new(other))
    }
}

impl Rem<u32> for Size {
    type Output = Size;
    fn rem(self, other: u32) -> Self::Output {
        Size::Mod(Box::new(self), Box::new(Size::Lit(other)))
    }
}
impl Rem<&Size> for Size {
    type Output = Size;
    fn rem(self, other: &Size) -> Self::Output {
        self % other.clone()
    }
}
impl Rem<Tid> for Size {
    type Output = Size;
    fn rem(self, other: Tid) -> Self::Output {
        Size::Mod(Box::new(self), Box::new(Size::Var(other)))
    }
}

impl Rem for &Size {
    type Output = Size;
    fn rem(self, other: Self) -> Self::Output {
        self.clone() % other.clone()
    }
}
impl Rem<Size> for &Size {
    type Output = Size;
    fn rem(self, other: Size) -> Self::Output {
        self.clone() % other
    }
}

/// Exponentiation of sizes
impl BitXor for Size {
    type Output = Size;
    fn bitxor(self, other: Self) -> Self::Output {
        Size::Pow(Box::new(self), Box::new(other))
    }
}

impl BitXor<u32> for Size {
    type Output = Size;
    fn bitxor(self, other: u32) -> Self::Output {
        Size::Pow(Box::new(self), Box::new(Size::Lit(other)))
    }
}
impl BitXor<&Size> for Size {
    type Output = Size;
    fn bitxor(self, other: &Size) -> Self::Output {
        self ^ other.clone()
    }
}
impl BitXor<Tid> for Size {
    type Output = Size;
    fn bitxor(self, other: Tid) -> Self::Output {
        Size::Pow(Box::new(self), Box::new(Size::Var(other)))
    }
}
impl BitXor for &Size {
    type Output = Size;
    fn bitxor(self, other: Self) -> Self::Output {
        self.clone() ^ other.clone()
    }
}
impl BitXor<Size> for &Size {
    type Output = Size;
    fn bitxor(self, other: Size) -> Self::Output {
        self.clone() ^ other
    }
}

/// To and from integers and strings
impl From<u32> for Size {
    fn from(n: u32) -> Self {
        Size::Lit(n)
    }
}

impl From<&str> for Size {
    fn from(s: &str) -> Self {
        Size::Var(Tid::from(s))
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
            Size::Add(box a, box b) => a.pretty(allocator).append(allocator.text(" + ")).append(b.pretty(allocator)),
            Size::Sub(box a, box b) => a.pretty(allocator).append(allocator.text(" - ")).append(b.pretty(allocator)),
            Size::Mul(box a, box b) => a.pretty(allocator).append(allocator.text(" * ")).append(b.pretty(allocator)),
            Size::Div(box a, box b) => a.pretty(allocator).append(allocator.text(" / ")).append(b.pretty(allocator)),
            Size::Mod(box a, box b) => a.pretty(allocator).append(allocator.text(" % ")).append(b.pretty(allocator)),
            Size::Pow(box a, box b) => a.pretty(allocator).append(allocator.text(" ^ ")).append(b.pretty(allocator)),
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

lazy_static! {
    pub static ref SIZE_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add_op, Left) | Op::infix(sub_op, Left))
            .op(Op::infix(mul_op, Left) | Op::infix(div_op, Left) | Op::infix(mod_op, Left))
            .op(Op::infix(pow_op, Right))
    };
}

impl<'pest> FromPest<'pest> for Size {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        expression: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        SIZE_PARSER
            .map_primary(|pair|
                match pair.as_rule() {
                    Rule::size_ty => Size::from_pest(&mut pair.into_inner()),
                    Rule::size_var => Ok(Size::var(Tid::from_pest(&mut pair.into_inner())?)),
                    Rule::positive => Ok(Size::Lit(pair.as_str().parse().unwrap())),
                    _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair)))
                })
            .map_infix(|lhs, op, rhs|
                match op.clone().as_rule() {
                    Rule::add_op => Ok(lhs? + rhs?),
                    Rule::sub_op => Ok(lhs? - rhs?),
                    Rule::mul_op => Ok(lhs? * rhs?),
                    Rule::div_op => Ok(lhs? / rhs?),
                    Rule::mod_op => Ok(lhs? % rhs?),
                    Rule::pow_op => Ok(lhs? ^ rhs?),
                    _ => unreachable!(),
                })
            .parse(expression)
    }
}

/// Arbitrary instance for Size
#[cfg(test)] use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)]
impl<'a> Arbitrary<'a> for Size {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let variant = u.choose(&[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9
        ])?;

        Ok(match variant {
            0 => Size::Var(u.arbitrary()?),
            1 => Size::Lit(u.arbitrary()?),
            2 => Size::Add(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            3 => Size::Sub(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            4 => Size::Mul(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            5 => Size::Div(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            6 => Size::Mod(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            7 => Size::Pow(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            8 => Size::Max(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            9 => Size::Min(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            _ => unreachable!(),
        })
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/// Parser tests
////////////////////////////////////////////////////////////////////////////////////////
#[test]
fn size_parser() {
    let mut pairs = ZippelParser::parse(Rule::size_ty, "N+1").unwrap();
    assert_eq!(Size::from_pest(&mut pairs).unwrap(), Size::varstr("N") + 1);

    pairs = ZippelParser::parse(Rule::size_ty, "2*N+1").unwrap();
    assert_eq!(Size::from_pest(&mut pairs).unwrap(), Size::from(2) * Size::varstr("N") + 1);

    pairs = ZippelParser::parse(Rule::size_ty, "2^N*2").unwrap();
    assert_eq!(Size::from_pest(&mut pairs).unwrap(), (Size::from(2) ^ Size::varstr("N")) * 2);

    pairs = ZippelParser::parse(Rule::size_ty, "2^(N-1) / N").unwrap();
    assert_eq!(Size::from_pest(&mut pairs).unwrap(), (Size::from(2) ^ (Size::varstr("N") - 1)) / Size::varstr("N"));

    pairs = ZippelParser::parse(Rule::size_ty, "N % 2").unwrap();
    assert_eq!(Size::from_pest(&mut pairs).unwrap(), Size::varstr("N") % 2);
}
