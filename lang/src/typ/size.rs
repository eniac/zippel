use from_pest::{ConversionError, FromPest};
use lazy_static::lazy_static;
use pest::iterators::Pairs;
use pest::pratt_parser::{Assoc, Op, PrattParser};
use std::fmt;
use std::ops::{Add, BitXor, Div, Mul, Sub};
use thiserror::Error;

use crate::id::Tid;
use crate::parser::*;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};
use share::{Ctx, Set};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Size {
    Var(Tid),                  // N
    Lit(u32),                  // 15
    Add(Box<Size>, Box<Size>), // A + B
    Sub(Box<Size>, Box<Size>), // A - B
    Mul(Box<Size>, Box<Size>), // A * B
    Div(Box<Size>, Box<Size>), // A / B
    Pow(Box<Size>, Box<Size>), // A ^ B
    Max(Box<Size>, Box<Size>), // max(A, B)
    Min(Box<Size>, Box<Size>), // min(A, B)
}

#[derive(Error, PartialEq, Debug)]
pub enum EvalError {
    #[error("Division by zero: {0} / {1}")]
    DivisionByZero(Size, Size),
    #[error("Underflow by subtraction: {0} - {1}")]
    UnderflowBySubtraction(Size, Size),
    #[error("Negative variable value: {0}")]
    NegativeVariableValue(Size),
    #[error("Variable not found: {0}")]
    VariableNotFound(Tid),
}

impl Size {
    pub fn var(id: Tid) -> Self {
        Size::Var(id)
    }

    pub fn varstr(v: &str) -> Self {
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
            Size::Pow(a, b) => a.free_vars().union(b.free_vars()),
            Size::Max(a, b) => a.free_vars().union(b.free_vars()),
            Size::Min(a, b) => a.free_vars().union(b.free_vars()),
        }
    }

    pub fn eval(&self, ctx: &Ctx<Tid, usize>) -> Result<usize, EvalError> {
        match self {
            Size::Var(id) => ctx
                .get(id)
                .map_or(Err(EvalError::VariableNotFound(id.clone())), |x| Ok(*x)),
            Size::Lit(i) => Ok(*i as usize),
            Size::Add(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Ok(x + y)
            }
            Size::Sub(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                if x < y {
                    Err(EvalError::UnderflowBySubtraction(a.clone(), b.clone()))
                } else {
                    Ok(x - y)
                }
            }
            Size::Mul(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Ok(x * y)
            }
            Size::Div(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                if y != 0 {
                    Ok(x / y)
                } else {
                    Err(EvalError::DivisionByZero(a.clone(), b.clone()))
                }
            }
            Size::Pow(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Ok(x.pow(y as u32))
            }
            Size::Max(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Ok(x.max(y))
            }
            Size::Min(box a, box b) => {
                let x = a.eval(ctx)?;
                let y = b.eval(ctx)?;
                Ok(x.min(y))
            }
        }
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
            Size::Add(box a, box b) => a
                .pretty(allocator)
                .append(allocator.text(" + "))
                .append(b.pretty(allocator)),
            Size::Sub(box a, box b) => a
                .pretty(allocator)
                .append(allocator.text(" - "))
                .append(b.pretty(allocator)),
            Size::Mul(box a, box b) => a
                .pretty(allocator)
                .append(allocator.text(" * "))
                .append(b.pretty(allocator)),
            Size::Div(box a, box b) => a
                .pretty(allocator)
                .append(allocator.text(" / "))
                .append(b.pretty(allocator)),
            Size::Pow(box a, box b) => a
                .pretty(allocator)
                .append(allocator.text(" ^ "))
                .append(b.pretty(allocator)),
            Size::Max(box a, box b) => allocator
                .text("max(")
                .append(a.pretty(allocator))
                .append(allocator.text(", "))
                .append(b.pretty(allocator))
                .append(allocator.text(")")),
            Size::Min(box a, box b) => allocator
                .text("min(")
                .append(a.pretty(allocator))
                .append(allocator.text(", "))
                .append(b.pretty(allocator))
                .append(allocator.text(")")),
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
            .op(Op::infix(mul_op, Left) | Op::infix(div_op, Left))
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
            .map_primary(|pair| match pair.as_rule() {
                Rule::size_ty => Size::from_pest(&mut pair.into_inner()),
                Rule::size_var => Ok(Size::var(Tid::from_pest(&mut pair.into_inner())?)),
                Rule::positive => Ok(Size::Lit(pair.as_str().parse().unwrap())),
                _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
            })
            .map_infix(|lhs, op, rhs| match op.clone().as_rule() {
                Rule::add_op => Ok(lhs? + rhs?),
                Rule::sub_op => Ok(lhs? - rhs?),
                Rule::mul_op => Ok(lhs? * rhs?),
                Rule::div_op => Ok(lhs? / rhs?),
                Rule::pow_op => Ok(lhs? ^ rhs?),
                _ => unreachable!(),
            })
            .parse(expression)
    }
}

/// Arbitrary instance for Size
#[cfg(test)]
use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)]
impl<'a> Arbitrary<'a> for Size {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let variant = u.choose(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9])?;

        Ok(match variant {
            0 => Size::Var(u.arbitrary()?),
            1 => Size::Lit(u.arbitrary()?),
            2 => Size::Add(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            3 => Size::Sub(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            4 => Size::Mul(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
            5 => Size::Div(Box::new(u.arbitrary()?), Box::new(u.arbitrary()?)),
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
#[cfg(test)]
use pest::Parser;
#[test]
fn size_parser() {
    let mut pairs = ZippelParser::parse(Rule::size_ty, "N+1").unwrap();
    assert_eq!(Size::from_pest(&mut pairs).unwrap(), Size::varstr("N") + 1);

    pairs = ZippelParser::parse(Rule::size_ty, "2*N+1").unwrap();
    assert_eq!(
        Size::from_pest(&mut pairs).unwrap(),
        Size::from(2) * Size::varstr("N") + 1
    );

    pairs = ZippelParser::parse(Rule::size_ty, "2^N*2").unwrap();
    assert_eq!(
        Size::from_pest(&mut pairs).unwrap(),
        (Size::from(2) ^ Size::varstr("N")) * 2
    );

    pairs = ZippelParser::parse(Rule::size_ty, "2^(N-1) / N").unwrap();
    assert_eq!(
        Size::from_pest(&mut pairs).unwrap(),
        (Size::from(2) ^ (Size::varstr("N") - 1)) / Size::varstr("N")
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test Size constructors
    #[test]
    fn test_size_var() {
        let size = Size::var(Tid::from("N"));
        assert_eq!(size, Size::Var(Tid::from("N")));
    }

    #[test]
    fn test_size_varstr() {
        let size = Size::varstr("M");
        assert_eq!(size, Size::Var(Tid::from("M")));
    }

    #[test]
    fn test_size_max() {
        let size = Size::max(Size::Lit(5), Size::Lit(10));
        assert!(matches!(size, Size::Max(_, _)));
    }

    #[test]
    fn test_size_min() {
        let size = Size::min(Size::Lit(5), Size::Lit(10));
        assert!(matches!(size, Size::Min(_, _)));
    }

    #[test]
    fn test_size_neg() {
        let size = Size::Lit(5).neg();
        assert_eq!(
            size,
            Size::Sub(Box::new(Size::Lit(0)), Box::new(Size::Lit(5)))
        );
    }

    #[test]
    fn test_size_zero() {
        let size = Size::zero();
        assert_eq!(size, Size::Lit(0));
    }

    #[test]
    fn test_size_one() {
        let size = Size::one();
        assert_eq!(size, Size::Lit(1));
    }

    // Test free_vars
    #[test]
    fn test_free_vars_var() {
        let size = Size::varstr("N");
        let vars = size.free_vars();
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&Tid::from("N")));
    }

    #[test]
    fn test_free_vars_lit() {
        let size = Size::Lit(42);
        let vars = size.free_vars();
        assert!(vars.is_empty());
    }

    #[test]
    fn test_free_vars_add() {
        let size = Size::varstr("N") + Size::varstr("M");
        let vars = size.free_vars();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Tid::from("N")));
        assert!(vars.contains(&Tid::from("M")));
    }

    #[test]
    fn test_free_vars_complex() {
        let size = (Size::varstr("N") * Size::Lit(2)) + (Size::varstr("M") / Size::varstr("K"));
        let vars = size.free_vars();
        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&Tid::from("N")));
        assert!(vars.contains(&Tid::from("M")));
        assert!(vars.contains(&Tid::from("K")));
    }

    // Test eval
    #[test]
    fn test_eval_lit() {
        let size = Size::Lit(42);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 42);
    }

    #[test]
    fn test_eval_var() {
        let size = Size::varstr("N");
        let mut ctx = Ctx::new();
        ctx.insert(&Tid::from("N"), &10);
        assert_eq!(size.eval(&ctx).unwrap(), 10);
    }

    #[test]
    fn test_eval_var_not_found() {
        let size = Size::varstr("N");
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(result, Err(EvalError::VariableNotFound(_))));
    }

    #[test]
    fn test_eval_add() {
        let size = Size::Lit(5) + Size::Lit(10);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 15);
    }

    #[test]
    fn test_eval_sub() {
        let size = Size::Lit(10) - Size::Lit(3);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 7);
    }

    #[test]
    fn test_eval_sub_underflow() {
        let size = Size::Lit(3) - Size::Lit(10);
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(
            result,
            Err(EvalError::UnderflowBySubtraction(_, _))
        ));
    }

    #[test]
    fn test_eval_mul() {
        let size = Size::Lit(5) * Size::Lit(10);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 50);
    }

    #[test]
    fn test_eval_div() {
        let size = Size::Lit(20) / Size::Lit(4);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 5);
    }

    #[test]
    fn test_eval_div_zero() {
        let size = Size::Lit(10) / Size::Lit(0);
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(result, Err(EvalError::DivisionByZero(_, _))));
    }

    #[test]
    fn test_eval_pow() {
        let size = Size::Lit(2) ^ Size::Lit(5);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 32);
    }

    #[test]
    fn test_eval_max() {
        let size = Size::max(Size::Lit(5), Size::Lit(10));
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 10);
    }

    #[test]
    fn test_eval_min() {
        let size = Size::min(Size::Lit(5), Size::Lit(10));
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 5);
    }

    #[test]
    fn test_eval_complex() {
        let size = (Size::Lit(2) ^ Size::varstr("N")) * Size::Lit(3);
        let mut ctx = Ctx::new();
        ctx.insert(&Tid::from("N"), &4);
        assert_eq!(size.eval(&ctx).unwrap(), 48); // 2^4 * 3 = 16 * 3 = 48
    }

    // Test operator overloads with various types
    #[test]
    fn test_add_u32() {
        let size = Size::Lit(5) + 10u32;
        assert_eq!(
            size,
            Size::Add(Box::new(Size::Lit(5)), Box::new(Size::Lit(10)))
        );
    }

    #[test]
    fn test_add_ref() {
        let a = Size::Lit(5);
        let b = Size::Lit(10);
        let size = &a + &b;
        assert_eq!(
            size,
            Size::Add(Box::new(Size::Lit(5)), Box::new(Size::Lit(10)))
        );
    }

    #[test]
    fn test_add_tid() {
        let size = Size::Lit(5) + Tid::from("N");
        assert!(matches!(size, Size::Add(_, _)));
    }

    #[test]
    fn test_sub_u32() {
        let size = Size::Lit(10) - 5u32;
        assert_eq!(
            size,
            Size::Sub(Box::new(Size::Lit(10)), Box::new(Size::Lit(5)))
        );
    }

    #[test]
    fn test_sub_ref() {
        let a = Size::Lit(10);
        let b = Size::Lit(5);
        let size = &a - &b;
        assert_eq!(
            size,
            Size::Sub(Box::new(Size::Lit(10)), Box::new(Size::Lit(5)))
        );
    }

    #[test]
    fn test_sub_tid() {
        let size = Size::Lit(10) - Tid::from("N");
        assert!(matches!(size, Size::Sub(_, _)));
    }

    #[test]
    fn test_mul_u32() {
        let size = Size::Lit(5) * 10u32;
        assert_eq!(
            size,
            Size::Mul(Box::new(Size::Lit(5)), Box::new(Size::Lit(10)))
        );
    }

    #[test]
    fn test_mul_ref() {
        let a = Size::Lit(5);
        let b = Size::Lit(10);
        let size = &a * &b;
        assert_eq!(
            size,
            Size::Mul(Box::new(Size::Lit(5)), Box::new(Size::Lit(10)))
        );
    }

    #[test]
    fn test_mul_tid() {
        let size = Size::Lit(5) * Tid::from("N");
        assert!(matches!(size, Size::Mul(_, _)));
    }

    #[test]
    fn test_div_u32() {
        let size = Size::Lit(20) / 4u32;
        assert_eq!(
            size,
            Size::Div(Box::new(Size::Lit(20)), Box::new(Size::Lit(4)))
        );
    }

    #[test]
    fn test_div_ref() {
        let a = Size::Lit(20);
        let b = Size::Lit(4);
        let size = &a / &b;
        assert_eq!(
            size,
            Size::Div(Box::new(Size::Lit(20)), Box::new(Size::Lit(4)))
        );
    }

    #[test]
    fn test_div_tid() {
        let size = Size::Lit(20) / Tid::from("N");
        assert!(matches!(size, Size::Div(_, _)));
    }

    #[test]
    fn test_pow_u32() {
        let size = Size::Lit(2) ^ 5u32;
        assert_eq!(
            size,
            Size::Pow(Box::new(Size::Lit(2)), Box::new(Size::Lit(5)))
        );
    }

    #[test]
    fn test_pow_ref() {
        let a = Size::Lit(2);
        let b = Size::Lit(5);
        let size = &a ^ &b;
        assert_eq!(
            size,
            Size::Pow(Box::new(Size::Lit(2)), Box::new(Size::Lit(5)))
        );
    }

    #[test]
    fn test_pow_tid() {
        let size = Size::Lit(2) ^ Tid::from("N");
        assert!(matches!(size, Size::Pow(_, _)));
    }

    // Test From implementations
    #[test]
    fn test_from_u32() {
        let size = Size::from(42u32);
        assert_eq!(size, Size::Lit(42));
    }

    #[test]
    fn test_from_str() {
        let size = Size::from("N");
        assert_eq!(size, Size::Var(Tid::from("N")));
    }

    // Test Display
    #[test]
    fn test_display_var() {
        let size = Size::varstr("N");
        assert_eq!(size.to_string(), "N");
    }

    #[test]
    fn test_display_lit() {
        let size = Size::Lit(42);
        assert_eq!(size.to_string(), "42");
    }

    #[test]
    fn test_display_add() {
        let size = Size::Lit(5) + Size::Lit(10);
        assert_eq!(size.to_string(), "5 + 10");
    }

    #[test]
    fn test_display_complex() {
        let size = Size::max(Size::Lit(5), Size::Lit(10));
        assert_eq!(size.to_string(), "max(5, 10)");
    }

    #[test]
    fn test_display_min() {
        let size = Size::min(Size::Lit(5), Size::Lit(10));
        assert_eq!(size.to_string(), "min(5, 10)");
    }

    // Test is_nil
    #[test]
    fn test_is_nil() {
        let size = Size::Lit(42);
        assert!(!<Size as Pretty<'_, BoxAllocator, ()>>::is_nil(&size));
    }
}
