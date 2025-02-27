use lang::exp::BinOp;
use lang::typ::CTyp;
use lang::arg::CArgs;
use lang::id::{Fid, Tid};
use lang::range::CRange;
use share::{Traversal, BoxAllocator, Pretty, DocAllocator, DocBuilder};
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use std::fmt;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Op {
    /// Initial nodes in the graph, public or private inputs
    In { name: Fid, args: CArgs },

    /// Binary operation
    Bin(BinOp),

    /// Numeric literal
    Lit(usize),

    /// Generator of a group [Tid]
    Gen(Tid),

    /// Coefficients of a univariate vector
    Coef,

    /// Multilinear extension of a 2^N vector of coefficients
    Mle,

    /// A vector of elements
    Vec,

    /// Range of numbers
    Range(CRange),

    /// Random access or slice a vector
    Ram,

    /// Sample pseudo-random number generator
    Random(Tid),

    /// Random oracle challenge as a hash
    Hash(Tid),

    /// Convert from evaluation domain to lagrange domain.
    Interpolate,

    /// Equality check
    Equ,

    /// Vector containment check
    Contains,

    /// Logical and
    And,

    /// Logical or
    Or,

    /// Logical not
    Not
}

/// A node in the DAG
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Node<A> {
    pub op: Op,
    pub typ: CTyp,
    pub principal: Principal,
    pub ann: A
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Inputs(p, args) => write!(f, "In<{}>: {}", p, args),
            Op::Bin(op) => write!(f, "{}", op),
            Op::Lit(x) => write!(f, "Lit({})", x),
            Op::Gen(tid) => write!(f, "Gen<{}>", tid),
            Op::Coef => write!(f, "Coef"),
            Op::Mle => write!(f, "Mle"),
            Op::Vec => write!(f, "Vec"),
            Op::Range(r) => write!(f, "Range<{}>", r),
            Op::Ram => write!(f, "Ram"),
            Op::Random(tid) => write!(f, "Random<{}>", tid),
            Op::Hash(tid) => write!(f, "Hash<{}>", tid),
            Op::Interpolate => write!(f, "Interpolate"),
            Op::Equ => write!(f, "=="),
            Op::Contains => write!(f, "Contains"),
            Op::And => write!(f, "&&"),
            Op::Or => write!(f, "||"),
            Op::Not => write!(f, "!"),
        }
    }
}

/// Pretty printer instance for typed AExp
impl<'a, D, T, A> Pretty<'a, D, T> for Node<A>
where
    D: DocAllocator<'a, T>,
    D::Doc: Clone,
    T: 'a + Clone,
    A: Pretty<'a, D, T> + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, T> {
        allocator.intersperse([
            allocator.text(format!("{}, ", self.op)),
            self.typ.pretty(allocator),
            self.principal.pretty(allocator),
            self.ann.pretty(allocator),
        ], ", ")
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, A> fmt::Display for Node<A>
where
    A: Pretty<'a, BoxAllocator, ()> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Node<A> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

struct NodeTraversal1<N>(std::marker::PhantomData<N>);
impl<N, Z> Traversal<N, Z> for NodeTraversal1<N> {
    type Domain = Node<N>;
    type Codomain = Node<Z>;

    fn traverse<E>(on: Self::Domain, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Self::Codomain, E> {
        let Node { op, typ, principal, ann } = on;
        let ann = f(ann)?;
        Ok(Node { op, typ, principal, ann })
    }
}

impl<N> ToTraversal1<N> for Node<N> {
    type Output<Z> = Node<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Node<Z>, E> {
        NodeTraversal1::traverse(self, f)
    }
}

