use lang::ast::{CSig, BinOp};
use lang::typ::CTyp;
use lang::id::Tid;
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use crate::value::Value;
use std::fmt;

/// An operation [Op] is loosely a node in the graph,
/// and it corresponds to one [lang::ast::Exp] in the AST.
/// It is parameterized by some values.
/// - When the value is [Value::Underscore], it is a placeholder for a graph edge (an underscore).
/// - Otherwise, it is a concrete, irreducible value.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Op {
    /// Binary operation
    Bin(BinOp, Value, Value),

    /// Coefficients of a univariate vector
    Coef(Value),

    /// Multilinear extension of a 2^N vector of coefficients
    Mle(Value),

    /// A vector of elements
    Vec(Vec<Value>),

    /// Random oracle challenge
    Challenge(Tid),

    /// Random number generator
    Random(Tid),

    /// Group generator
    Generator(Tid),

    /// Random oracle challenge as a hash
    Hash(Tid),

    /// Convert from evaluation domain to lagrange domain.
    Interpolate(Value, Value),

    /// Equality check
    Equ(Value, Value),

    /// Vector containment check
    Contains(Value, Value),

    /// Logical and
    And(Value, Value),

    /// Logical or
    Or(Value, Value),

    /// Logical not
    Not(Value),

    /// Assertion or verification check
    Check(Value)
}

/// A node in the DAG
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Node<A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(CSig),
    /// Empty transcript node, corresponds to an entry point in the program
    EmptyTranscript,
    /// A side relation that must hold on input arguments for a function
    Pre(CSig),
    /// Operation node
    Op(Op, CTyp, A)
}

/// Node annotated with a principal
pub type PNode = Node<Principal>;

impl Op {
    pub fn bin(op: BinOp, l: Value, r: Value) -> Self {
        Op::Bin(op, l, r)
    }
    pub fn coef(v: Value) -> Self {
        Op::Coef(v)
    }
    pub fn mle(v: Value) -> Self {
        Op::Mle(v)
    }
    pub fn vec(vals: Vec<Value>) -> Self {
        Op::Vec(vals)
    }
}

impl PNode {
    pub fn inp(sig: CSig) -> Self {
        Node::Inp(sig)
    }

    pub fn empty_transcript() -> Self {
        Node::EmptyTranscript
    }

    pub fn pre(sig: CSig) -> Self {
        Node::Pre(sig)
    }

    pub fn coef(v: Value, typ: CTyp) -> Self {
        Node::Op(Op::Coef(v), typ, Principal::Prover)
    }

    pub fn bin(op: BinOp, l: Value, r: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(op, l, r), typ, Principal::Prover)
    }

    pub fn set_principal(&mut self, ann: Principal) {
        match self {
            Node::Op(_, _, a) => *a = ann,
            _ => panic!("UncaughtError: Failed to assign principal {} to node {}", ann, self)
        }
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Bin(op, a, b) => write!(f, "{} {} {}", a, op, b),
            Op::Coef(v) => write!(f, "coef {}", v),
            Op::Mle(v) => write!(f, "mle {}", v),
            Op::Vec(vs) =>
                write!(f, "[ {} ]", vs.iter().map(|v| format!("{}", v)).collect::<Vec<String>>().join(", ")),
            Op::Ram(a, b) => write!(f, "{} [ {} ]", a, b),
            Op::Hash(tid) => write!(f, "hash<{}>", tid),
            Op::Interpolate(a, b) => write!(f, "interpolate {}, {}", a, b),
            Op::Equ(a, b) => write!(f, "{} == {}", a, b),
            Op::Contains(a, b) => write!(f, "{} in {}", a, b),
            Op::And(a, b) => write!(f, "{} && {}", a, b),
            Op::Or(a, b) => write!(f, "{} || {}", a, b),
            Op::Not(a) => write!(f, "! {}", a),
            Op::Challenge(tid) => write!(f, "challenge<{}>", tid),
            Op::Generator(tid) => write!(f, "generator<{}>", tid),
            Op::Random(tid) => write!(f, "random<{}>", tid),
            Op::Check(a) => write!(f, "check {}", a)
        }
    }
}

impl<A: fmt::Display> fmt::Display for Node<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(sig) => write!(f, "{}", sig),
            Node::EmptyTranscript => write!(f, "EmptyTranscript"),
            Node::Pre(sig) => write!(f, "Pre({}, {}, {})", sig.name, sig.typevars, sig.args),
            Node::Op(op, typ, ann) =>
                write!(f, "{} : {} @ {}", op, typ, ann)
        }
    }
}

impl<N> ToTraversal1<N> for Node<N> {
    type Output<Z> = Node<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Node<Z>, E> {
        match self {
            Node::Inp(sig) => Ok(Node::Inp(sig)),
            Node::Pre(sig) => Ok(Node::Pre(sig)),
            Node::EmptyTranscript => Ok(Node::EmptyTranscript),
            Node::Op(op, typ, ann) => {
                let ann = f(ann)?;
                Ok(Node::Op(op, typ, ann))
            }
        }
    }
}

