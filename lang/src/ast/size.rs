use num::{BigUint, One, ToPrimitive, Zero};
use std::fmt;
use thiserror::Error;

use crate::ast::exp::ExpLiteral;
use crate::ast::spanned::Spanned;
use crate::id::Tid;
use share::{Ctx, Set};

/// A symbolic size expression appearing in source-level types, such as the
/// length of a `Vec` or the degree of a polynomial.
///
/// Sizes are built from size-type variables (`Tid`, written with a leading
/// uppercase letter in `.zippel` source) and literals, and are eliminated by
/// [`Size::eval`] when a `UModule` is concretized into a `CModule`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Size {
    /// A size-type variable, resolved from the substitution context at
    /// concretization time.
    Var(Tid), // N
    /// A literal known at parse time. Expression literals keep their full
    /// magnitude; size positions only admit values that fit in `usize`.
    Lit(BigUint), // 15
    /// Sum of two sizes.
    Add(Box<Spanned<Size>>, Box<Spanned<Size>>), // A + B
    /// Difference of two sizes; must not underflow when evaluated.
    Sub(Box<Spanned<Size>>, Box<Spanned<Size>>), // A - B
    /// Product of two sizes.
    Mul(Box<Spanned<Size>>, Box<Spanned<Size>>), // A * B
    /// Integer (truncating) quotient of two sizes.
    Div(Box<Spanned<Size>>, Box<Spanned<Size>>), // A / B
    /// Exponentiation of a size by a size.
    Pow(Box<Spanned<Size>>, Box<Spanned<Size>>), // A ^ B
}

/// Failure while evaluating a [`Size`] to a concrete `usize`.
#[derive(Error, Debug)]
pub enum EvalError {
    /// The divisor evaluated to zero.
    #[error("Division by zero: {0} / {1}")]
    DivisionByZero(Size, Size),
    /// The right operand of a subtraction exceeded the left one; sizes are
    /// unsigned.
    #[error("Underflow by subtraction: {0} - {1}")]
    UnderflowBySubtraction(Size, Size),
    /// A size-type variable was bound to a negative value.
    #[error("Negative variable value: {0}")]
    NegativeVariableValue(Size),
    /// A size-type variable is not bound in the substitution context.
    #[error("Variable not found: {0}")]
    VariableNotFound(Tid),
    /// A literal used as a size does not fit in `usize`.
    #[error("Size exceeds usize range: {0}")]
    SizeOutOfRange(Size),
    /// Size arithmetic overflowed `usize`.
    #[error("Size arithmetic overflow: {0}")]
    SizeOverflow(Size),
    /// An exponent does not fit in `u32`.
    #[error("Size exponent exceeds u32 range: {0}")]
    ExponentOutOfRange(Size),
}

impl ExpLiteral for Size {
    type Size = Size;
    fn lit(value: usize) -> Self {
        Size::Lit(value.into())
    }
}

impl Size {
    /// Precedence for parenthesization.
    /// Non-binary variants (Var, Lit) return 4 — higher than any
    /// binary op, so they never need parentheses.
    pub fn precedence(&self) -> usize {
        match self {
            Size::Add(_, _) | Size::Sub(_, _) => 1,
            Size::Mul(_, _) | Size::Div(_, _) => 2,
            Size::Pow(_, _) => 3,
            Size::Var(_) | Size::Lit(_) => 4,
        }
    }

    /// Right-associative? (Only Pow; all other size binops are left-assoc.)
    pub fn is_right_assoc(&self) -> bool {
        matches!(self, Size::Pow(_, _))
    }

    /// Whether `lhs` needs parentheses as the left operand of `self` to parse back unchanged.
    pub fn lhs_needs_paren(&self, lhs: &Size) -> bool {
        let (parent, child) = (self.precedence(), lhs.precedence());
        child < parent || (child == parent && self.is_right_assoc())
    }

    /// Whether `rhs` needs parentheses as the right operand of `self` to parse back unchanged.
    pub fn rhs_needs_paren(&self, rhs: &Size) -> bool {
        let (parent, child) = (self.precedence(), rhs.precedence());
        child < parent || (child == parent && !self.is_right_assoc())
    }

    /// Whether this is the literal `1`, the implicit dimension of `Uni`/`Mle` sugar.
    pub fn is_lit_one(&self) -> bool {
        matches!(self, Size::Lit(n) if n.is_one())
    }

    /// The size-type variables this expression depends on.
    pub fn free_vars(&self) -> Set<Tid> {
        match self {
            Size::Var(id) => Set::from([id.clone()]),
            Size::Lit(_) => Set::new(),
            Size::Add(a, b) => a.node.free_vars().union(b.node.free_vars()),
            Size::Sub(a, b) => a.node.free_vars().union(b.node.free_vars()),
            Size::Mul(a, b) => a.node.free_vars().union(b.node.free_vars()),
            Size::Div(a, b) => a.node.free_vars().union(b.node.free_vars()),
            Size::Pow(a, b) => a.node.free_vars().union(b.node.free_vars()),
        }
    }

    /// Evaluates this size expression to a concrete `usize` under the
    /// size-variable bindings `ctx`, for type shapes and ranges.
    ///
    /// # Errors
    /// Returns `EvalError::VariableNotFound` for an unbound variable,
    /// `EvalError::UnderflowBySubtraction` when a subtraction would go below
    /// zero, `EvalError::DivisionByZero` for a zero divisor,
    /// `EvalError::SizeOutOfRange` for a literal above `usize::MAX`,
    /// `EvalError::SizeOverflow` when arithmetic overflows `usize`, and
    /// `EvalError::ExponentOutOfRange` for an exponent above `u32::MAX`.
    pub fn eval(&self, ctx: &Ctx<Tid, usize>) -> Result<usize, EvalError> {
        let overflow = || EvalError::SizeOverflow(self.clone());
        match self {
            Size::Var(id) => ctx
                .get(id)
                .map_or(Err(EvalError::VariableNotFound(id.clone())), |x| Ok(*x)),
            Size::Lit(i) => i
                .to_usize()
                .ok_or_else(|| EvalError::SizeOutOfRange(self.clone())),
            Size::Add(a, b) => a
                .node
                .eval(ctx)?
                .checked_add(b.node.eval(ctx)?)
                .ok_or_else(overflow),
            Size::Sub(a, b) => a
                .node
                .eval(ctx)?
                .checked_sub(b.node.eval(ctx)?)
                .ok_or_else(|| EvalError::UnderflowBySubtraction(a.node.clone(), b.node.clone())),
            Size::Mul(a, b) => a
                .node
                .eval(ctx)?
                .checked_mul(b.node.eval(ctx)?)
                .ok_or_else(overflow),
            Size::Div(a, b) => a
                .node
                .eval(ctx)?
                .checked_div(b.node.eval(ctx)?)
                .ok_or_else(|| EvalError::DivisionByZero(a.node.clone(), b.node.clone())),
            Size::Pow(a, b) => {
                let x = a.node.eval(ctx)?;
                let y = u32::try_from(b.node.eval(ctx)?)
                    .map_err(|_| EvalError::ExponentOutOfRange(self.clone()))?;
                x.checked_pow(y).ok_or_else(overflow)
            }
        }
    }

    /// Evaluates this size expression exactly, for a numeric expression
    /// literal: no `usize` bound applies, so the full magnitude survives.
    ///
    /// # Errors
    /// As [`Size::eval`], except that only subtraction underflow, division by
    /// zero, unbound variables and exponents above `u32::MAX` fail.
    pub fn eval_literal(&self, ctx: &Ctx<Tid, usize>) -> Result<BigUint, EvalError> {
        match self {
            Size::Var(id) => ctx
                .get(id)
                .map(|x| BigUint::from(*x))
                .ok_or_else(|| EvalError::VariableNotFound(id.clone())),
            Size::Lit(i) => Ok(i.clone()),
            Size::Add(a, b) => Ok(a.node.eval_literal(ctx)? + b.node.eval_literal(ctx)?),
            Size::Sub(a, b) => {
                let x = a.node.eval_literal(ctx)?;
                let y = b.node.eval_literal(ctx)?;
                if x < y {
                    Err(EvalError::UnderflowBySubtraction(
                        a.node.clone(),
                        b.node.clone(),
                    ))
                } else {
                    Ok(x - y)
                }
            }
            Size::Mul(a, b) => Ok(a.node.eval_literal(ctx)? * b.node.eval_literal(ctx)?),
            Size::Div(a, b) => {
                let x = a.node.eval_literal(ctx)?;
                let y = b.node.eval_literal(ctx)?;
                if y.is_zero() {
                    Err(EvalError::DivisionByZero(a.node.clone(), b.node.clone()))
                } else {
                    Ok(x / y)
                }
            }
            Size::Pow(a, b) => {
                let x = a.node.eval_literal(ctx)?;
                let y = b
                    .node
                    .eval_literal(ctx)?
                    .to_u32()
                    .ok_or_else(|| EvalError::ExponentOutOfRange(self.clone()))?;
                Ok(x.pow(y))
            }
        }
    }
}

/// Infix, parenthesizing an operand only where needed to parse back to the same tree.
impl fmt::Display for Size {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (a, op, b) = match self {
            Size::Var(id) => return write!(f, "{id}"),
            Size::Lit(n) => return write!(f, "{n}"),
            Size::Add(a, b) => (a, "+", b),
            Size::Sub(a, b) => (a, "-", b),
            Size::Mul(a, b) => (a, "*", b),
            Size::Div(a, b) => (a, "/", b),
            Size::Pow(a, b) => (a, "^", b),
        };
        if self.lhs_needs_paren(&a.node) {
            write!(f, "({})", a.node)?;
        } else {
            write!(f, "{}", a.node)?;
        }
        write!(f, " {op} ")?;
        if self.rhs_needs_paren(&b.node) {
            write!(f, "({})", b.node)
        } else {
            write!(f, "{}", b.node)
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/// Parser tests
////////////////////////////////////////////////////////////////////////////////////////
#[cfg(test)]
mod tests {
    use super::*;
    use arbitrary::{Arbitrary, Unstructured};

    fn varstr(v: &str) -> Size {
        Size::Var(Tid::from(v))
    }

    impl<'a> Arbitrary<'a> for Size {
        fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
            fn arb(u: &mut Unstructured, depth: usize) -> arbitrary::Result<Size> {
                let max_variant = if depth > 3 { 1 } else { 6 };
                let variant = u.int_in_range(0..=max_variant)?;
                Ok(match variant {
                    0 => Size::Var(u.arbitrary()?),
                    1 => Size::Lit(u.arbitrary::<u32>()?.into()),
                    2 => Size::Add(
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                    ),
                    3 => Size::Sub(
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                    ),
                    4 => Size::Mul(
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                    ),
                    5 => Size::Div(
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                    ),
                    6 => Size::Pow(
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                        Box::new(Spanned::dummy(arb(u, depth + 1)?)),
                    ),
                    _ => unreachable!(),
                })
            }
            arb(u, 0)
        }
    }

    // Test free_vars
    #[test]
    fn test_free_vars_var() {
        let size = varstr("N");
        let vars = size.free_vars();
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&Tid::from("N")));
    }

    #[test]
    fn test_free_vars_lit() {
        let size = Size::lit(42);
        let vars = size.free_vars();
        assert!(vars.is_empty());
    }

    #[test]
    fn test_free_vars_add() {
        let size = Size::Add(
            Box::new(Spanned::dummy(varstr("N"))),
            Box::new(Spanned::dummy(varstr("M"))),
        );
        let vars = size.free_vars();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Tid::from("N")));
        assert!(vars.contains(&Tid::from("M")));
    }

    #[test]
    fn test_free_vars_complex() {
        let size = Size::Mul(
            Box::new(Spanned::dummy(Size::Add(
                Box::new(Spanned::dummy(varstr("N"))),
                Box::new(Spanned::dummy(Size::lit(2))),
            ))),
            Box::new(Spanned::dummy(Size::Div(
                Box::new(Spanned::dummy(varstr("M"))),
                Box::new(Spanned::dummy(varstr("K"))),
            ))),
        );
        let vars = size.free_vars();
        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&Tid::from("N")));
        assert!(vars.contains(&Tid::from("M")));
        assert!(vars.contains(&Tid::from("K")));
    }

    // Test eval
    #[test]
    fn test_eval_lit() {
        let size = Size::lit(42);
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 42);
    }

    #[test]
    fn test_eval_var() {
        let size = varstr("N");
        let mut ctx = Ctx::new();
        ctx.insert(&Tid::from("N"), &10);
        assert_eq!(size.eval(&ctx).unwrap(), 10);
    }

    #[test]
    fn test_eval_var_not_found() {
        let size = varstr("N");
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(result, Err(EvalError::VariableNotFound(_))));
    }

    #[test]
    fn test_eval_add() {
        let size = Size::Add(
            Box::new(Spanned::dummy(Size::lit(5))),
            Box::new(Spanned::dummy(Size::lit(10))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 15);
    }

    #[test]
    fn test_eval_sub() {
        let size = Size::Sub(
            Box::new(Spanned::dummy(Size::lit(10))),
            Box::new(Spanned::dummy(Size::lit(3))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 7);
    }

    #[test]
    fn test_eval_sub_underflow() {
        let size = Size::Sub(
            Box::new(Spanned::dummy(Size::lit(3))),
            Box::new(Spanned::dummy(Size::lit(10))),
        );
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(
            result,
            Err(EvalError::UnderflowBySubtraction(_, _))
        ));
    }

    #[test]
    fn test_eval_mul() {
        let size = Size::Mul(
            Box::new(Spanned::dummy(Size::lit(5))),
            Box::new(Spanned::dummy(Size::lit(10))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 50);
    }

    #[test]
    fn test_eval_div() {
        let size = Size::Div(
            Box::new(Spanned::dummy(Size::lit(20))),
            Box::new(Spanned::dummy(Size::lit(4))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 5);
    }

    #[test]
    fn test_eval_div_zero() {
        let size = Size::Div(
            Box::new(Spanned::dummy(Size::lit(10))),
            Box::new(Spanned::dummy(Size::lit(0))),
        );
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(result, Err(EvalError::DivisionByZero(_, _))));
    }

    #[test]
    fn test_eval_pow() {
        let size = Size::Pow(
            Box::new(Spanned::dummy(Size::lit(2))),
            Box::new(Spanned::dummy(Size::lit(5))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 32);
    }

    #[test]
    fn test_eval_complex() {
        let size = Size::Mul(
            Box::new(Spanned::dummy(Size::Pow(
                Box::new(Spanned::dummy(Size::lit(2))),
                Box::new(Spanned::dummy(varstr("N"))),
            ))),
            Box::new(Spanned::dummy(Size::lit(3))),
        );
        let mut ctx = Ctx::new();
        ctx.insert(&Tid::from("N"), &4);
        assert_eq!(size.eval(&ctx).unwrap(), 48); // 2^4 * 3 = 16 * 3 = 48
    }

    #[test]
    fn test_eval_add_overflow() {
        let size = Size::Add(
            Box::new(Spanned::dummy(varstr("N"))),
            Box::new(Spanned::dummy(Size::lit(1))),
        );
        let mut ctx = Ctx::new();
        ctx.insert(&Tid::from("N"), &usize::MAX);
        assert!(matches!(size.eval(&ctx), Err(EvalError::SizeOverflow(_))));
    }
}
