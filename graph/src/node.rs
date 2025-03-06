use lang::ast::{CSig, CExp, BinOp};
use lang::typ::{CTyp, Nothing};
use lang::id::{Fid, Tid, Vid};
use lang::typ::range::CRange;
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use crate::value::Value;
use std::fmt;

/// An operation [Op] is loosely a node in the graph,
/// and it corresponds to one [lang::ast::Exp] in the AST.
/// It is parameterized by some optional values.
/// - When the value is [None], it is a placeholder for a graph edge (an underscore).
/// - When the value is [Some v], it is a concrete, irreducible value.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Op {
    /// Binary operation
    Bin(BinOp, Option<Value>, Option<Value>),

    /// Coefficients of a univariate vector
    Coef(Option<Value>),

    /// Multilinear extension of a 2^N vector of coefficients
    Mle(Option<Value>),

    /// A vector of elements
    Vec(Vec<Option<Value>>),

    /// Random access or slice a vector
    Ram(Option<Value>, Option<Value>),

    /// Random oracle challenge
    Challenge(Tid),

    /// Random number generator
    Random(Tid),

    /// Group generator
    Generator(Tid),

    /// Random oracle challenge as a hash
    Hash(Tid),

    /// Convert from evaluation domain to lagrange domain.
    Interpolate(Option<Value>, Option<Value>),

    /// Equality check
    Equ(Option<Value>, Option<Value>),

    /// Vector containment check
    Contains(Option<Value>, Option<Value>),

    /// Logical and
    And(Option<Value>, Option<Value>),

    /// Logical or
    Or(Option<Value>, Option<Value>),

    /// Logical not
    Not(Option<Value>)
}

/// A node in the DAG
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Node<A> {
    /// Entry in the graph, annotated with a function or protocol signature
    Inp(CSig),
    /// Empty transcript node, corresponds to an entry point in the program
    EmptyTranscript,
    /// Operation node
    Op(Op, CTyp, Principal, A)
}

/// Unannotated node
pub type UNode = Node<Nothing>;

impl Op {
    pub fn bin(op: BinOp) -> Self {
        Op::Bin(op, None, None)
    }
    pub fn coef() -> Self {
        Op::Coef(None)
    }
    pub fn mle() -> Self {
        Op::Mle(None)
    }
    pub fn vec(size: usize) -> Self {
        Op::Vec(vec![None; 10])
    }
    pub fn ram() -> Self {
        Op::Ram(None, None)
    }
    pub fn challenge(tid: Tid) -> Self {
        Op::Challenge(tid)
    }
    pub fn random(tid: Tid) -> Self {
        Op::Random(tid)
    }
    pub fn generator(tid: Tid) -> Self {
        Op::Generator(tid)
    }
    pub fn hash(tid: Tid) -> Self {
        Op::Hash(tid)
    }
    pub fn interpolate() -> Self {
        Op::Interpolate(None, None)
    }
    pub fn equ() -> Self {
        Op::Equ(None, None)
    }
    pub fn contains() -> Self {
        Op::Contains(None, None)
    }
    pub fn and() -> Self {
        Op::And(None, None)
    }
    pub fn or() -> Self {
        Op::Or(None, None)
    }
    pub fn not() -> Self {
        Op::Not(None)
    }

    /// Replace one of the unbounded arguments in [Op] with a value,
    /// return [true] if the value was successfully pushed, [false] otherwise.
    pub fn push_value(&mut self, v: Value) {
        match self {
            Op::Bin(_, a, b)
            | Op::And(a, b)
            | Op::Or(a, b)
            | Op::Equ(a, b)
            | Op::Contains(a, b)
            | Op::Interpolate(a, b)
            | Op::Ram(a, b) =>
                if a.is_none() {
                    *a = Some(v);
                    true
                } else if b.is_none() {
                    *b = Some(v);
                    true
                } else {
                    panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
                },
            Op::Mle(a)
            | Op::Coef(a)
            | Op::Not(a) =>
                if a.is_none() {
                    *a = Some(v);
                    true
                } else {
                    panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
                },
            Op::Vec(vs) => {
                for v in vs.iter_mut() {
                    if v.is_none() {
                        *v = Some(v);
                        return true;
                    }
                }
                panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
            }
            Op::Hash(_) | Op::Random(_) | Op::Challenge(_) | Op::Generator(_) =>
                panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
        }
    }
}


impl UNode {
    pub fn inp(sig: CSig) -> Self {
        Node::Inp(sig)
    }

    pub fn empty_transcript() -> Self {
        Node::EmptyTranscript
    }

    pub fn ret() -> Self {
        Node::Ret
    }

    pub fn bin(op: BinOp, typ: CTyp) -> Self {
        Node::Op(Op::bin(op), typ, Principal::Any, Nothing)
    }

    pub fn coef(typ: CTyp) -> Self {
        Node::Op(Op::coef(), typ, Principal::Any, Nothing)
    }

    pub fn challenge(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::challenge(tid), typ, Principal::Any, Nothing)
    }
    pub fn random(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::random(tid), typ, Principal::Any, Nothing)
    }
    pub fn generator(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::generator(tid), typ, Principal::Any, Nothing)
    }
    pub fn mle(typ: CTyp) -> Self {
        Node::Op(Op::mle(), typ, Principal::Any, Nothing)
    }

    pub fn vec(inner: CTyp, size: usize) -> Self {
        Node::Op(Op::vec(*size), CTyp::vec(inner, size), Principal::Any, Nothing)
    }

    pub fn ram(typ: CTyp) -> Self {
        Node::Op(Op::ram(), typ, Principal::Any, Nothing)
    }

    pub fn hash(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::hash(tid), typ, Principal::Any, Nothing)
    }

    pub fn interpolate(typ: CTyp) -> Self {
        Node::Op(Op::interpolate(), typ, Principal::Any, Nothing)
    }

    pub fn equ(typ: CTyp) -> Self {
        Node::Op(Op::equ(), typ, Principal::Any, Nothing)
    }

    pub fn and(typ: CTyp) -> Self {
        Node::Op(Op::and(), typ, Principal::Any, Nothing)
    }

    pub fn or(typ: CTyp) -> Self {
        Node::Op(Op::or(), typ, Principal::Any, Nothing)
    }

    pub fn contains(typ: CTyp) -> Self {
        Node::Op(Op::contains(), typ, Principal::Any, Nothing)
    }

    pub fn not(typ: CTyp) -> Self {
        Node::Op(Op::not(), typ, Principal::Any, Nothing)
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Bin(op, a, b) => write!(f, "{} {} {}", a, op, b),
            Op::Coef(v) => write!(f, "coef {}", v),
            Op::Mle(v) => write!(f, "mle {}", v),
            Op::Vec(vs) => write!(f, "[ {} ]", vs),
            Op::Ram(a, b) => write!(f, "{} [ {} ]", a, b),
            Op::Hash(tid) => write!(f, "hash<{}>", tid),
            Op::Interpolate(a, b) => write!(f, "interpolate {}, {}", a, b),
            Op::Equ(a, b) => write!(f, "{} == {}", a, b),
            Op::Contains(a, b) => write!(f, "{} in {}", a, b),
            Op::And(a, b) => write!(f, "{} && {}", a, b),
            Op::Or(a, b) => write!(f, "{} || {}", a, b),
            Op::Not(a) => write!(f, "! {}", a),
            Op::Challenge(tid) => write!(f, "challenge<{}>", tid),
            Op::Random(tid) => write!(f, "random<{}>", tid),
            Op::Generator(tid) => write!(f, "generator<{}>", tid)
        }
    }
}

impl<A: fmt::Display> fmt::Display for Node<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(sig) => write!(f, "{}", sig),
            Node::EmptyTranscript => write!(f, "EmptyTranscript"),
            Node::Op(op, typ, principal, ann) =>
                write!(f, "{} : {} by {} @ {}", op, typ, principal, ann)
        }
    }
}

impl<N> ToTraversal1<N> for Node<N> {
    type Output<Z> = Node<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Node<Z>, E> {
        match self {
            Node::Inp(sig) => Ok(Node::Inp(sig)),
            Node::EmptyTranscript => Ok(Node::EmptyTranscript),
            Node::Op(op, typ, principal, ann) => {
                let ann = f(ann)?;
                Ok(Node::Op(op, typ, principal, ann))
            }
        }
    }
}

