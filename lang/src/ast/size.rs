use std::fmt;
use thiserror::Error;

use crate::ast::spanned::Spanned;
use crate::id::Tid;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};
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
    /// A literal size known at parse time.
    Lit(u32), // 15
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
    /// size-variable bindings `ctx`.
    ///
    /// # Errors
    /// Returns `EvalError::VariableNotFound` for an unbound variable,
    /// `EvalError::UnderflowBySubtraction` when a subtraction would go below
    /// zero, and `EvalError::DivisionByZero` for a zero divisor.
    ///
    /// # Panics
    /// Panics on arithmetic overflow of addition, multiplication, or
    /// exponentiation when overflow checks are enabled; exponents larger than
    /// `u32::MAX` are truncated.
    pub fn eval(&self, ctx: &Ctx<Tid, usize>) -> Result<usize, EvalError> {
        match self {
            Size::Var(id) => ctx
                .get(id)
                .map_or(Err(EvalError::VariableNotFound(id.clone())), |x| Ok(*x)),
            Size::Lit(i) => Ok(*i as usize),
            Size::Add(a, b) => {
                let x = a.node.eval(ctx)?;
                let y = b.node.eval(ctx)?;
                Ok(x + y)
            }
            Size::Sub(a, b) => {
                let x = a.node.eval(ctx)?;
                let y = b.node.eval(ctx)?;
                if x < y {
                    Err(EvalError::UnderflowBySubtraction(
                        a.node.clone(),
                        b.node.clone(),
                    ))
                } else {
                    Ok(x - y)
                }
            }
            Size::Mul(a, b) => {
                let x = a.node.eval(ctx)?;
                let y = b.node.eval(ctx)?;
                Ok(x * y)
            }
            Size::Div(a, b) => {
                let x = a.node.eval(ctx)?;
                let y = b.node.eval(ctx)?;
                x.checked_div(y)
                    .ok_or_else(|| EvalError::DivisionByZero(a.node.clone(), b.node.clone()))
            }
            Size::Pow(a, b) => {
                let x = a.node.eval(ctx)?;
                let y = b.node.eval(ctx)?;
                Ok(x.pow(y as u32))
            }
        }
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////
/// Pretty printing and display for Size
//////////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Size
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        fn pretty_child<'a, D, A>(
            child: Size,
            parent_prec: usize,
            is_right: bool,
            allocator: &'a D,
        ) -> DocBuilder<'a, D, A>
        where
            D: DocAllocator<'a, A>,
            D::Doc: Clone,
            A: 'a + Clone,
        {
            let child_prec = child.precedence();
            let need_parens = if child_prec < parent_prec {
                true
            } else if child_prec == parent_prec {
                match parent_prec {
                    1 => is_right,
                    2 => is_right,
                    3 => !is_right,
                    _ => false,
                }
            } else {
                false
            };

            if need_parens {
                allocator
                    .text("(")
                    .append(child.pretty(allocator))
                    .append(allocator.text(")"))
            } else {
                child.pretty(allocator)
            }
        }

        match self {
            Size::Var(id) => id.pretty(allocator),
            Size::Lit(n) => allocator.text(n.to_string()),
            Size::Add(a, b) => pretty_child(a.node.clone(), 1, false, allocator)
                .append(allocator.text(" + "))
                .append(pretty_child(b.node.clone(), 1, true, allocator)),
            Size::Sub(a, b) => pretty_child(a.node.clone(), 1, false, allocator)
                .append(allocator.text(" - "))
                .append(pretty_child(b.node.clone(), 1, true, allocator)),
            Size::Mul(a, b) => pretty_child(a.node.clone(), 2, false, allocator)
                .append(allocator.text(" * "))
                .append(pretty_child(b.node.clone(), 2, true, allocator)),
            Size::Div(a, b) => pretty_child(a.node.clone(), 2, false, allocator)
                .append(allocator.text(" / "))
                .append(pretty_child(b.node.clone(), 2, true, allocator)),
            Size::Pow(a, b) => pretty_child(a.node.clone(), 3, false, allocator)
                .append(allocator.text(" ^ "))
                .append(pretty_child(b.node.clone(), 3, true, allocator)),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl fmt::Display for Size {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Size as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
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
                    1 => Size::Lit(u.arbitrary()?),
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
        let size = Size::Lit(42);
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
                Box::new(Spanned::dummy(Size::Lit(2))),
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
        let size = Size::Lit(42);
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
            Box::new(Spanned::dummy(Size::Lit(5))),
            Box::new(Spanned::dummy(Size::Lit(10))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 15);
    }

    #[test]
    fn test_eval_sub() {
        let size = Size::Sub(
            Box::new(Spanned::dummy(Size::Lit(10))),
            Box::new(Spanned::dummy(Size::Lit(3))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 7);
    }

    #[test]
    fn test_eval_sub_underflow() {
        let size = Size::Sub(
            Box::new(Spanned::dummy(Size::Lit(3))),
            Box::new(Spanned::dummy(Size::Lit(10))),
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
            Box::new(Spanned::dummy(Size::Lit(5))),
            Box::new(Spanned::dummy(Size::Lit(10))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 50);
    }

    #[test]
    fn test_eval_div() {
        let size = Size::Div(
            Box::new(Spanned::dummy(Size::Lit(20))),
            Box::new(Spanned::dummy(Size::Lit(4))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 5);
    }

    #[test]
    fn test_eval_div_zero() {
        let size = Size::Div(
            Box::new(Spanned::dummy(Size::Lit(10))),
            Box::new(Spanned::dummy(Size::Lit(0))),
        );
        let ctx = Ctx::new();
        let result = size.eval(&ctx);
        assert!(matches!(result, Err(EvalError::DivisionByZero(_, _))));
    }

    #[test]
    fn test_eval_pow() {
        let size = Size::Pow(
            Box::new(Spanned::dummy(Size::Lit(2))),
            Box::new(Spanned::dummy(Size::Lit(5))),
        );
        let ctx = Ctx::new();
        assert_eq!(size.eval(&ctx).unwrap(), 32);
    }

    #[test]
    fn test_eval_complex() {
        let size = Size::Mul(
            Box::new(Spanned::dummy(Size::Pow(
                Box::new(Spanned::dummy(Size::Lit(2))),
                Box::new(Spanned::dummy(varstr("N"))),
            ))),
            Box::new(Spanned::dummy(Size::Lit(3))),
        );
        let mut ctx = Ctx::new();
        ctx.insert(&Tid::from("N"), &4);
        assert_eq!(size.eval(&ctx).unwrap(), 48); // 2^4 * 3 = 16 * 3 = 48
    }

    // Test is_nil
    #[test]
    fn test_is_nil() {
        let size = Size::Lit(42);
        assert!(!<Size as Pretty<'_, BoxAllocator, ()>>::is_nil(&size));
    }
}
