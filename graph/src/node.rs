use lang::ast::{CSig, BinOp};
use lang::typ::CTyp;
use lang::id::Tid;
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use crate::value::Value;
use std::fmt;

/// An operation [Op] is loosely a node in the graph,
/// and it corresponds to one [lang::ast::Exp] in the AST.
/// It is parameterized by some optional values.
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

    /// Random access or slice a vector
    Ram(Value, Value),

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
    /// Operation node
    Op(Op, CTyp, A)
}

/// Node annotated with a principal
pub type PNode = Node<Principal>;

impl Op {
    pub fn bin(op: BinOp) -> Self {
        Op::Bin(op, Value::Underscore, Value::Underscore)
    }
    pub fn coef() -> Self {
        Op::Coef(Value::Underscore)
    }
    pub fn mle() -> Self {
        Op::Mle(Value::Underscore)
    }
    pub fn vec(size: usize) -> Self {
        Op::Vec(vec![Value::Underscore; size])
    }
    pub fn ram() -> Self {
        Op::Ram(Value::Underscore, Value::Underscore)
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
        Op::Interpolate(Value::Underscore, Value::Underscore)
    }
    pub fn equ() -> Self {
        Op::Equ(Value::Underscore, Value::Underscore)
    }
    pub fn contains() -> Self {
        Op::Contains(Value::Underscore, Value::Underscore)
    }
    pub fn and() -> Self {
        Op::And(Value::Underscore, Value::Underscore)
    }
    pub fn or() -> Self {
        Op::Or(Value::Underscore, Value::Underscore)
    }
    pub fn not() -> Self {
        Op::Not(Value::Underscore)
    }
    pub fn check() -> Self {
        Op::Check(Value::Underscore)
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
                match (&a, &b) {
                    (Value::Underscore, _) => *a = v,
                    (_, Value::Underscore) => *b = v,
                    (_, _) => panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
                },
            Op::Mle(a)
            | Op::Coef(a)
            | Op::Check(a)
            | Op::Not(a) =>
                match a {
                    Value::Underscore => *a = v,
                    _ => panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
                },
            Op::Vec(vs) => {
                vs.iter_mut().for_each(|x| {
                    if x.is_underscore() {
                        *x = v.clone();
                        return;
                    }
                });
                panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
            },
            Op::Hash(_) | Op::Random(_) | Op::Challenge(_) | Op::Generator(_) =>
                panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
        }
    }
}


impl PNode {
    pub fn inp(sig: CSig) -> Self {
        Node::Inp(sig)
    }

    pub fn empty_transcript() -> Self {
        Node::EmptyTranscript
    }

    pub fn bin(op: BinOp, typ: CTyp) -> Self {
        Node::Op(Op::bin(op), typ, Principal::Any)
    }

    pub fn coef(typ: CTyp) -> Self {
        Node::Op(Op::coef(), typ, Principal::Any)
    }

    pub fn random(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::random(tid), typ, Principal::Any)
    }
    pub fn generator(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::generator(tid), typ, Principal::Any)
    }
    pub fn mle(typ: CTyp) -> Self {
        Node::Op(Op::mle(), typ, Principal::Any)
    }

    pub fn vec(inner: CTyp, size: usize) -> Self {
        Node::Op(Op::vec(size), CTyp::vec(inner, size), Principal::Any)
    }

    pub fn ram(typ: CTyp) -> Self {
        Node::Op(Op::ram(), typ, Principal::Any)
    }

    pub fn challenge(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::hash(tid), typ, Principal::Verifier)
    }

    pub fn check(typ: CTyp) -> Self {
        Node::Op(Op::check(), typ, Principal::Any)
    }

    pub fn interpolate(typ: CTyp) -> Self {
        Node::Op(Op::interpolate(), typ, Principal::Any)
    }

    pub fn equ(typ: CTyp) -> Self {
        Node::Op(Op::equ(), typ, Principal::Any)
    }

    pub fn and(typ: CTyp) -> Self {
        Node::Op(Op::and(), typ, Principal::Any)
    }

    pub fn or(typ: CTyp) -> Self {
        Node::Op(Op::or(), typ, Principal::Any)
    }

    pub fn contains(typ: CTyp) -> Self {
        Node::Op(Op::contains(), typ, Principal::Any)
    }

    pub fn not(typ: CTyp) -> Self {
        Node::Op(Op::not(), typ, Principal::Any)
    }

    pub fn push_value(&mut self, v: Value) {
        match self {
            Node::Op(op, _, _) => op.push_value(v),
            _ => panic!("UncaughtError: Failed to bind value {} to node {}", v, self)
        }
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
            Node::EmptyTranscript => Ok(Node::EmptyTranscript),
            Node::Op(op, typ, ann) => {
                let ann = f(ann)?;
                Ok(Node::Op(op, typ, ann))
            }
        }
    }
}

