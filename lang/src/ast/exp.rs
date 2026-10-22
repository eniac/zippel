use num::BigUint;
use share::Ctx;
use std::fmt;
use std::ops::Index;

use share::traversal::ToTraversal1;

use crate::ast::arena::{ExpId, ExpRef, Expr, Exprs};
use crate::ast::exclusion::Exclusion;
use crate::ast::range::{Range, RangeTraversal};
use crate::ast::spanned::Spanned;
use crate::ast::walk::{InScope, Visit};
use crate::ast::{Block, Size};
use crate::id::{Tid, TidSubst, Vid};

/// The carrier of an [`Exp`]'s numeric literals, paired with the size type of its ranges
/// and evaluation selectors: symbolic [`Size`] for both before concretization, a
/// full-magnitude [`BigUint`] literal with machine-sized `usize` ranges afterwards.
pub trait ExpLiteral: Clone {
    /// Representation of the sizes in ranges and `eval<range>` selectors.
    type Size: Clone + Eq + Ord + fmt::Debug;
    /// The small compiler-synthesized literal `value`.
    fn lit(value: usize) -> Self;
}

impl ExpLiteral for BigUint {
    type Size = usize;
    fn lit(value: usize) -> Self {
        value.into()
    }
}

/// Represents binary operations in the Zippel language.
/// Each variant corresponds to a different kind of binary operation that can be performed on arithmetic expressions.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum BinOp {
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Add,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let difference = 5 - 3;
    ///     ```
    Sub,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let product = 2 * 3;
    ///     ```
    Mul,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let quotient = 6 / 2;
    ///     ```
    Div,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let result = 2 ^ 3;
    ///     ```
    Pow,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let inner: F = [1,2,3] . [2,4,6];
    ///     ```
    Dot,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let inner: F = [1,2] ++ [2,4];
    ///     ```
    Concat,

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let inner: F = 5 % 2;
    ///     ```
    Rem,

    ///     Equality comparison: returns a single `Bool` for every operand shape;
    ///     two vectors are equal when all their elements are.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = x == y;
    ///     ```
    Equ,

    ///     Logical AND: both operands must be `Bool`, result is `Bool`.
    ///     In the GB encoding, `&&` is multiplication (`a * b`), since `Bool`
    ///     values are 0/1 field elements.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = x == y && z == w;
    ///     ```
    And,
}

/// Represents arithmetic expressions in the Zippel language: one node of an [`Exprs`] arena,
/// whose children are [`ExpId`]s in the same arena.
/// It is parameterized by the literal carrier `N`; ranges and selectors use `N::Size`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Exp<N: ExpLiteral> {
    ///     Numeric literal
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = 5;
    ///     ```
    Lit(N),

    ///     Unit value (the empty value of type Unit)
    Unit,

    ///     Variable reference
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let b = a;
    ///     ```
    Var(Spanned<Vid>),

    ///     Function application
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let result1 = f(x + 2, x)
    ///     ```
    App(Spanned<Vid>, Exps),

    /// Interpolate to a univariate polynomial: unary `interpolate(v)` uses the FFT
    /// evaluation grid (inverse FFT); binary `interpolate(xs, ys)` uses explicit points.
    ///
    /// **Zippel:**
    /// ```zippel
    /// let p_grid = interpolate(evals_on_fft_domain);
    /// let q = interpolate([0, 1, 2], [a, b, c]);
    /// ```
    Interpolate(Option<ExpId>, ExpId),

    ///     Polynomial from coefficients
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = poly(1,2,3);
    ///     ```
    Poly(ExpId),

    /// Evaluate a polynomial. Unary `eval(p)` evaluates on the FFT grid (FFT);
    /// binary `eval(p, points)` evaluates at explicit points (scalar or vector);
    /// selected `eval<range>(p, fixed)` keeps a contiguous range of variables
    /// free and fixes every variable outside that range.
    ///
    /// **Zippel:**
    /// ```zippel
    /// let evs = eval(p);                    // FFT-grid evaluation
    /// let v   = eval(p, point);             // single-point eval
    /// let vs  = eval(p, [x0, x1, x2]);      // batch eval
    /// let g   = eval<0>(p, tail);           // unit-range sugar for eval<0..1>
    /// let h   = eval<1..3>(p, fixed);       // keep variables 1 and 2 free
    /// ```
    Evaluate(ExpId, Option<Range<N::Size>>, Option<ExpId>),

    ///     Get vector of coefficients of polynomial
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = coef(poly(1,2,3));
    ///     ```
    Coef(ExpId),

    ///     Multilinear extension of a matrix, polynomial, etc.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = mle x;
    ///     ```
    Mle(ExpId),

    ///     A vector of elements
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let v = [1, 2*x, x+y];
    ///     ```
    Vec(Exps),

    ///     Binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = 2 + 3;
    ///     ```
    Bin(BinOp, ExpId, ExpId),

    ///     Unary negation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let neg = -x;
    ///     ```
    Neg(ExpId),

    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r = 0..5;
    ///     ```
    Range(Range<N::Size>),

    ///     Map comprehension
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let squares = [x^2 for x in 0,2..10];
    ///     ```
    Map(ExpId, Spanned<Vid>, ExpId),

    ///     Reduce a vector with a binary operation
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let sum = reduce(+, [1,2,3]);
    ///     ```
    Reduce(BinOp, ExpId),

    ///     Random access or slice a vector
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let first = v[0]
    ///     ```
    Ram(ExpId, ExpId),

    ///     Bilinear pairing
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let g = pair(g1, g2);
    ///     ```
    Pair(ExpId, ExpId),

    ///     Random sample, resampled while excluded
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let r = random<F - [0]>;
    ///     ```
    Random(Spanned<Tid>, Option<Spanned<ExpExclusion<N>>>),

    ///     Random oracle challenge, resampled while excluded
    ///     **Zippel Code:**
    ///     ```zippel
    ///     r <- challenge<F - [1]>;
    ///     ```
    Challenge(Spanned<Tid>, Option<Spanned<ExpExclusion<N>>>),

    ///     A block: typed statements in order, then the expression it evaluates to; a block without one
    ///     evaluates to `()`. A statement's binding is in scope in the rest of its block.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let x = 5 + 3;
    ///     p <- interpolate(v, [0,1,2]);
    ///     verify(x == 8)
    ///     ```
    Block(Block),

    ///     Verifier check: verifies that the expression is true.
    ///     The expression must be `Bool`.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     verify(a == a)
    ///     ```
    Verify(ExpId),

    ///     Polynomial function definition
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let p = fun x, y => x^2 + 2*x*y + 3*y^2;
    ///     ```
    Fun(Vec<Spanned<Vid>>, ExpId),

    ///     Record construction
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let a = {| name: "Sydnie", balance: 100 |};
    ///     ```
    Record(Ctx<Spanned<String>, ExpId>),

    ///     Field projection
    ///     **Zippel Code:**
    ///     ```zippel
    ///     a.name
    ///     ```
    Proj(ExpId, Spanned<String>),

    ///     Record update: create a new record identical to the given record
    ///     except with the specified field set to the given value.
    ///     **Zippel Code:**
    ///     ```zippel
    ///     let new_record = old_record.set(name, 3);
    ///     ```
    SetRecord(ExpId, Spanned<String>, ExpId),
}

/// A sequence of expressions: a vector literal's elements or a call's actual arguments.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Exps(pub Vec<ExpId>);

/// The values a sample in an [`Exp`] excludes.
pub type ExpExclusion<N> = Exclusion<ExpId, Spanned<<N as ExpLiteral>::Size>>;

/// Symbolic sized AST node, as parsed from input
pub type UExp = Exp<Size>;
/// Sequence of symbolically sized expressions.
pub type UExps = Exps;
/// A symbolically sized expression tree.
pub type UExpr = Expr<Size>;
/// A node of a symbolically sized expression tree, for reading it.
pub type URef<'a> = ExpRef<'a, Size>;

/// Concrete AST node: full-magnitude literals, machine-sized ranges
pub type CExp = Exp<BigUint>;
/// Sequence of concrete expressions.
pub type CExps = Exps;
/// A concrete expression tree.
pub type CExpr = Expr<BigUint>;
/// A node of a concrete expression tree, for reading it.
pub type CRef<'a> = ExpRef<'a, BigUint>;

impl<N: ExpLiteral> Exp<N> {
    /// The same node over the literal carrier `M`: literals mapped by `literal`, range and
    /// selector bounds and root orders by `size`; children keep their ids.
    fn map_leaves<M: ExpLiteral, E>(
        self,
        literal: &mut dyn FnMut(N) -> Result<M, E>,
        size: &mut dyn FnMut(N::Size) -> Result<M::Size, E>,
    ) -> Result<Exp<M>, E> {
        let exclusion = |x: Option<Spanned<ExpExclusion<N>>>,
                         size: &mut dyn FnMut(N::Size) -> Result<M::Size, E>|
         -> Result<Option<Spanned<ExpExclusion<M>>>, E> {
            x.map(|x| {
                let Spanned { node, span } = x;
                let node = match node {
                    Exclusion::Values(v) => Exclusion::Values(v),
                    Exclusion::RootsOfUnity(n) => {
                        Exclusion::RootsOfUnity(Spanned::new(size(n.node)?, n.span))
                    }
                };
                Ok(Spanned::new(node, span))
            })
            .transpose()
        };
        Ok(match self {
            Exp::Lit(x) => Exp::Lit(literal(x)?),
            Exp::Unit => Exp::Unit,
            Exp::Var(v) => Exp::Var(v),
            Exp::Range(r) => Exp::Range(r.traverse1(size)?),
            Exp::Evaluate(p, selector, ox) => {
                Exp::Evaluate(p, selector.map(|r| r.traverse1(size)).transpose()?, ox)
            }
            Exp::Challenge(t, x) => Exp::Challenge(t, exclusion(x, size)?),
            Exp::Random(t, x) => Exp::Random(t, exclusion(x, size)?),
            Exp::App(g, args) => Exp::App(g, args),
            Exp::Vec(args) => Exp::Vec(args),
            Exp::Interpolate(p, e) => Exp::Interpolate(p, e),
            Exp::Poly(p) => Exp::Poly(p),
            Exp::Coef(p) => Exp::Coef(p),
            Exp::Mle(p) => Exp::Mle(p),
            Exp::Pair(a, b) => Exp::Pair(a, b),
            Exp::Bin(op, a, b) => Exp::Bin(op, a, b),
            Exp::Neg(a) => Exp::Neg(a),
            Exp::Map(a, x, b) => Exp::Map(a, x, b),
            Exp::Reduce(op, a) => Exp::Reduce(op, a),
            Exp::Ram(a, b) => Exp::Ram(a, b),
            Exp::Block(block) => Exp::Block(block),
            Exp::Verify(a) => Exp::Verify(a),
            Exp::Fun(vars, a) => Exp::Fun(vars, a),
            Exp::Record(fields) => Exp::Record(fields),
            Exp::Proj(a, field) => Exp::Proj(a, field),
            Exp::SetRecord(a, field, b) => Exp::SetRecord(a, field, b),
        })
    }
}

/// Maps an expression's literal carrier and its size carrier separately: literals with
/// `literal`, range and selector sizes with `size`.
pub trait ExpTraversal<N: ExpLiteral>: Sized {
    /// The same shape over the literal carrier `M`.
    type Output<M: ExpLiteral>;
    /// Rebuilds `self` over `M`, short-circuiting on the first error.
    ///
    /// # Errors
    /// Returns the first `E` produced by `literal` or `size`.
    fn traverse_exp<M: ExpLiteral, E>(
        self,
        literal: &mut dyn FnMut(N) -> Result<M, E>,
        size: &mut dyn FnMut(N::Size) -> Result<M::Size, E>,
    ) -> Result<Self::Output<M>, E>;
}

/// Node by node, in arena order; every id stays the same.
impl<N: ExpLiteral> ExpTraversal<N> for Expr<N> {
    type Output<M: ExpLiteral> = Expr<M>;
    fn traverse_exp<M: ExpLiteral, E>(
        self,
        literal: &mut dyn FnMut(N) -> Result<M, E>,
        size: &mut dyn FnMut(N::Size) -> Result<M::Size, E>,
    ) -> Result<Expr<M>, E> {
        let Exprs { nodes, spans } = self.exprs;
        let nodes = nodes
            .into_iter()
            .map(|node| node.map_leaves(literal, size))
            .collect::<Result<_, _>>()?;
        Ok(Expr {
            exprs: Exprs { nodes, spans },
            root: self.root,
        })
    }
}

impl<T: ExpTraversal<N>, N: ExpLiteral> ExpTraversal<N> for Option<T> {
    type Output<M: ExpLiteral> = Option<T::Output<M>>;
    fn traverse_exp<M: ExpLiteral, E>(
        self,
        literal: &mut dyn FnMut(N) -> Result<M, E>,
        size: &mut dyn FnMut(N::Size) -> Result<M::Size, E>,
    ) -> Result<Self::Output<M>, E> {
        self.map(|x| x.traverse_exp(literal, size)).transpose()
    }
}

/// Range and `eval` selector bounds, node by node in arena order.
impl<N: ExpLiteral> RangeTraversal<N::Size> for Expr<N> {
    fn range_traverse<E>(
        mut self,
        f: &mut dyn FnMut(Range<N::Size>) -> Result<Range<N::Size>, E>,
    ) -> Result<Self, E> {
        for node in &mut self.exprs.nodes {
            match node {
                Exp::Range(r) | Exp::Evaluate(_, Some(r), _) => *r = f(r.clone())?,
                _ => {}
            }
        }
        Ok(self)
    }
}

/// Traverse `Tid` inside `TExp`: the sampled types, node by node.
impl TidSubst for CExpr {
    fn map_tids(&mut self, f: &dyn Fn(&Tid) -> Option<Tid>) {
        for node in &mut self.exprs.nodes {
            if let Exp::Challenge(t, _) | Exp::Random(t, _) = node
                && let Some(n) = f(&t.node)
            {
                t.node = n;
            }
        }
    }
}

impl<N: ExpLiteral> ExpRef<'_, N> {
    /// Whether the tree reads `name` where the tree itself does not bind it.
    pub fn reads_free(self, name: &Vid) -> bool {
        let mut in_scope = InScope::new();
        for visit in self.walk() {
            match visit {
                Visit::Bind(x, _) => in_scope.bind(x, ()),
                Visit::Unbind(x) => in_scope.unbind(x),
                Visit::Enter(e) => {
                    if let Exp::Var(x) = e.node()
                        && x.node == *name
                        && in_scope.get(name).is_none()
                    {
                        return true;
                    }
                }
                Visit::EnterStmt(_) | Visit::LeaveStmt(_) | Visit::Leave(_) => {}
            }
        }
        false
    }
}

impl Exps {
    /// The expressions, in source order.
    pub fn iter(&self) -> std::iter::Copied<std::slice::Iter<'_, ExpId>> {
        self.0.iter().copied()
    }
    /// Whether the sequence holds no expressions.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Number of expressions in the sequence.
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl IntoIterator for Exps {
    type Item = ExpId;
    type IntoIter = std::vec::IntoIter<ExpId>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<ExpId> for Exps {
    fn from_iter<I: IntoIterator<Item = ExpId>>(iter: I) -> Self {
        Exps(iter.into_iter().collect())
    }
}

impl Index<usize> for Exps {
    type Output = ExpId;

    fn index(&self, index: usize) -> &ExpId {
        &self.0[index]
    }
}

impl BinOp {
    /// Precedence matching the parser's Pratt table; lower binds looser. Printers use it to
    /// produce text that parses back to the same AST.
    pub fn precedence(&self) -> usize {
        match self {
            BinOp::And => 0, // lowest precedence
            BinOp::Equ => 1,
            BinOp::Add | BinOp::Sub => 2,
            BinOp::Mul | BinOp::Div | BinOp::Rem => 3,
            BinOp::Concat => 4,
            BinOp::Pow => 5,
            BinOp::Dot => 6, // not infix in grammar; programmatic-only
        }
    }

    /// Right-associative? (Only Pow; all other infix binops are left-assoc.)
    pub fn is_right_assoc(&self) -> bool {
        matches!(self, BinOp::Pow)
    }

    /// Whether `lhs` needs parentheses as the left operand of `self` to parse back unchanged.
    pub fn lhs_needs_paren<N: ExpLiteral>(&self, lhs: &Exp<N>) -> bool {
        match lhs {
            // `-x op y` parses as `(-x) op y` only when `op` binds looser than prefix minus.
            Exp::Neg(_) => self.precedence() >= NEG_PRECEDENCE,
            // `..` binds looser than every operator.
            Exp::Range(_) => true,
            Exp::Bin(child, _, _) => {
                child.precedence() < self.precedence()
                    || (child.precedence() == self.precedence() && self.is_right_assoc())
            }
            _ => false,
        }
    }

    /// Whether `rhs` needs parentheses as the right operand of `self` to parse back unchanged.
    pub fn rhs_needs_paren<N: ExpLiteral>(&self, rhs: &Exp<N>) -> bool {
        match rhs {
            // Prefix minus is allowed in any operand position.
            Exp::Neg(_) => false,
            Exp::Range(_) => true,
            Exp::Bin(child, _, _) => {
                child.precedence() < self.precedence()
                    || (child.precedence() == self.precedence() && !self.is_right_assoc())
            }
            _ => false,
        }
    }
}

impl<N: ExpLiteral> Exp<N> {
    /// Whether `self` must be parenthesized as the operand of prefix `-`: a binary operator
    /// that binds looser than `-`, or a range, would otherwise take `-` into its left operand.
    pub fn needs_paren_under_neg(&self) -> bool {
        matches!(self, Exp::Bin(op, _, _) if op.precedence() < NEG_PRECEDENCE)
            || matches!(self, Exp::Range(_))
    }
}

/// Binding precedence of prefix `-`, on the scale of [`BinOp::precedence`].
const NEG_PRECEDENCE: usize = 4;

/// The operator as written in source, e.g. `+`.
impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
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
        })
    }
}
