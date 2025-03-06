use lang::ast::{CSig, CExp, BinOp};
use lang::typ::{CTyp, Nothing};
use lang::id::{Fid, Tid, Vid};
use lang::typ::range::CRange;
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use std::fmt;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Op {
    /// Binary operation
    Bin(BinOp, Value, Value),

    /// Coefficients of a univariate vector
    Coef(Value),

    /// Multilinear extension of a 2^N vector of coefficients
    Mle(Value),

    /// A vector of elements
    Vec(Values),

    /// Random access or slice a vector
    Ram(Value, Value),

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
    Not(Value)
}

/// Values are expressions which are (very close to) irreducible
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Value {
    Lit(usize),
    Gen(Tid),
    Random(Tid),
    Range(CRange),
    Underscore // Placeholder for a value that is not yet known
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Values(pub Vec<Value>);

/// A node in the DAG
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Node<A> {
    /// Initial nodes in the graph, public or private inputs
    Inp(CSig),
    /// Empty transcript start
    EmptyTranscript,
    /// Return node
    Ret(Value),
    /// Operation node
    Op(Op, CTyp, Principal, A)
}

/// Unannotated node
pub type UNode = Node<Nothing>;

impl Value {
    pub fn bind_value(&mut self, v: Value) -> bool {
        match self {
            Value::Underscore => {
                *self = v;
                true
            },
            _ => false
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

    pub fn ret(value: Value) -> Self {
        Node::Ret(value)
    }

    pub fn add(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Add, a, b), typ, Principal::Any, Nothing)
    }

    pub fn sub(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Sub, a, b), typ, Principal::Any, Nothing)
    }

    pub fn mul(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Mul, a, b), typ, Principal::Any, Nothing)
    }

    pub fn div(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Div, a, b), typ, Principal::Any, Nothing)
    }

    pub fn dot(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Dot, a, b), typ, Principal::Any, Nothing)
    }

    pub fn concat(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Concat, a, b), typ, Principal::Any, Nothing)
    }

    pub fn pow(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Bin(BinOp::Pow, a, b), typ, Principal::Any, Nothing)
    }

    pub fn coef(v: Value, typ: CTyp) -> Self {
        Node::Op(Op::Coef(v), typ, Principal::Any, Nothing)
    }

    pub fn mle(v: Value, typ: CTyp) -> Self {
        Node::Op(Op::Mle(v), typ, Principal::Any, Nothing)
    }

    pub fn vec(vs: Values, typ: CTyp) -> Self {
        Node::Op(Op::Vec(vs), typ, Principal::Any, Nothing)
    }

    pub fn ram(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Ram(a, b), typ, Principal::Any, Nothing)
    }

    pub fn hash(tid: Tid, typ: CTyp) -> Self {
        Node::Op(Op::Hash(tid), typ, Principal::Any, Nothing)
    }

    pub fn interpolate(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Interpolate(a, b), typ, Principal::Any, Nothing)
    }

    pub fn equ(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Equ(a, b), typ, Principal::Any, Nothing)
    }

    pub fn and(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::And(a, b), typ, Principal::Any, Nothing)
    }

    pub fn or(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Or(a, b), typ, Principal::Any, Nothing)
    }

    pub fn contains(a: Value, b: Value, typ: CTyp) -> Self {
        Node::Op(Op::Contains(a, b), typ, Principal::Any, Nothing)
    }

    pub fn not(a: Value, typ: CTyp) -> Self {
        Node::Op(Op::Not(a), typ, Principal::Any, Nothing)
    }

    pub fn bind_value(&mut self, v: Value) -> bool {
        match self {
            Node::Ret(under) => under.bind_value(v),
            Node::Op(Op::Bin(_, a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::Coef(mv), _, _, _) => mv.bind_value(v),
            Node::Op(Op::Mle(mv), _, _, _) => mv.bind_value(v),
            Node::Op(Op::Vec(vs), _, _, _) => vs.0.iter_mut().any(|mv| mv.bind_value(v.clone())),
            Node::Op(Op::Ram(a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::Hash(_), _, _, _) => false,
            Node::Op(Op::Interpolate(a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::Equ(a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::Contains(a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::And(a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::Or(a, b), _, _, _) => a.bind_value(v.clone()) || b.bind_value(v),
            Node::Op(Op::Not(a), _, _, _) => a.bind_value(v),
            _ => false
        }
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
            Op::Hash(tid) => write!(f, "Hash<{}>", tid),
            Op::Interpolate(a, b) => write!(f, "interpolate {}, {}", a, b),
            Op::Equ(a, b) => write!(f, "{} == {}", a, b),
            Op::Contains(a, b) => write!(f, "{} in {}", a, b),
            Op::And(a, b) => write!(f, "{} && {}", a, b),
            Op::Or(a, b) => write!(f, "{} || {}", a, b),
            Op::Not(a) => write!(f, "! {}", a),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Lit(x) => write!(f, "{}", x),
            Value::Gen(x) => write!(f, "gen<{}>", x),
            Value::Random(x) => write!(f, "random<{}>", x),
            Value::Range(r) => write!(f, "{}", r),
            Value::Underscore => write!(f, "_")
        }
    }
}

impl fmt::Display for Values {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Values(vs) = self;
        write!(f, "{}", vs.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "))
    }
}

impl<A: fmt::Display> fmt::Display for Node<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Inp(sig) => write!(f, "{}", sig),
            Node::EmptyTranscript => write!(f, "EmptyTranscript"),
            Node::Ret(v)  => write!(f, "return {}", v),
            Node::Op(op, typ, principal, ann) => write!(f, "{} : {} by {}, {}", op, typ, principal, ann)
        }
    }
}

impl IntoIterator for Values {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<Value> for Values {
    fn from_iter<I: IntoIterator<Item=Value>>(iter: I) -> Self {
        Values(iter.into_iter().collect())
    }
}

impl Values {
    pub fn iter(&self) -> std::slice::Iter<Value> {
        self.0.iter()
    }
}

impl<N> ToTraversal1<N> for Node<N> {
    type Output<Z> = Node<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Node<Z>, E> {
        match self {
            Node::Inp(sig) => Ok(Node::Inp(sig)),
            Node::EmptyTranscript => Ok(Node::EmptyTranscript),
            Node::Ret(v) => Ok(Node::Ret(v)),
            Node::Op(op, typ, principal, ann) => {
                let ann = f(ann)?;
                Ok(Node::Op(op, typ, principal, ann))
            }
        }
    }
}

