use lang::typ::range::CRange;
use lang::ast::BinOp;
use lang::id::Vid;
use crate::arkworks::{Value, ATyp, ArkConfig};
use crate::graph::Edge;

use petgraph::graph::NodeIndex;
use std::ops::{Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr};
use std::fmt;

/// Typed operands are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Operand<C: ArkConfig> {
    /// Value
    Value(Value<C>),
    /// Boolean not
    Not(Box<Operand<C>>),
    /// Generator for a group
    Gen(ATyp),
    /// Node input
    Underscore(NodeIndex, ATyp),
    /// Variable input
    Var(Vid, NodeIndex, ATyp),
    /// Range of numbers
    Range(CRange),
    /// Random access into a value
    Ram(Box<Operand<C>>, Box<Operand<C>>),
    /// Vector of values
    Vec(Vec<Operand<C>>),
}

/// An operation [Op] is loosely a node in the program graph.
/// It is parameterized by tye type of operands [V] and the type of types [T].
#[derive(PartialEq, Eq, Clone)]
pub enum OpF<T> {

    /// Binary operation
    Bin(BinOp, T, T),

    /// Random element
    Random(ATyp),

    /// Random oracle challenge
    Challenge(ATyp),

    /// Convert from evaluation domain to lagrange domain.
    Coef(T),

    /// Convert from lagrange domain to evaluation domain
    Eval(T),

    /// Hash operation into a cryptographic transcript
    Hash(T),

    /// Vector containment check
    Contains(T, T),

    /// Assertion or verification check
    Check(T),
}

pub type Op<C> = OpF<Operand<C>>;

impl<C: ArkConfig> Operand<C> {
    pub fn typ(&self) -> ATyp {
        match &self {
            Operand::Value(v) => v.typ(),
            Operand::Not(_) => ATyp::Bool,
            Operand::Gen(t) => t.clone(),
            Operand::Underscore(_, t) => t.clone(),
            Operand::Var(_, _, t) => t.clone(),
            Operand::Range(r) => ATyp::vec(ATyp::Fin(r.clone()), r.len()),
            Operand::Ram(box l, box r) =>
                match (l.typ(), r.typ()) {
                    (ATyp::Vec(box typ, _), ATyp::Fin(_)) => typ,
                    (ATyp::Vec(box typ, _), ATyp::Vec(box ATyp::Fin(_), m)) =>
                        ATyp::vec(typ, m),
                    (a, b) =>
                        panic!("UncaughtError: Ram operand must be a vector, not {} [ {} ]", a, b),
                }
            Operand::Vec(vs) => {
                let typ = vs[0].typ();
                for v in vs.iter().skip(1) {
                    if v.typ() != typ {
                        panic!("UncaughtError: Vector operands must be of the same type: {} != {}", typ, v.typ());
                    }
                }
                ATyp::vec(typ, vs.len())
            }
        }
    }

    pub fn bin(op: BinOp, a: &Self, b: &Self, typ: &ATyp) -> Option<Self> {
        match op {
            BinOp::Add => Self::add(a.clone(), b.clone(), typ.clone()),
            BinOp::Sub => Self::sub(a.clone(), b.clone(), typ.clone()),
            BinOp::Mul => Self::mul(a.clone(), b.clone(), typ.clone()),
            BinOp::Div => Self::div(a.clone(), b.clone(), typ.clone()),
            BinOp::Rem => Self::rem(a.clone(), b.clone(), typ.clone()),
            BinOp::Pow => Self::pow(a.clone(), b.clone(), typ.clone()),
            BinOp::Dot => Self::dot(a.clone(), b.clone()),
            BinOp::Concat => Self::concat(a.clone(), b.clone()),
            BinOp::Contains => Self::contains(a.clone(), b.clone()),
            BinOp::Equ => Self::equ(a.clone(), b.clone()),
            BinOp::And => Self::and(a.clone(), b.clone()),
            BinOp::Or => Self::or(a.clone(), b.clone()),
        }
    }

    pub fn index(i: usize) -> Operand<C> {
        Operand::Value(Value::Index(i as u64))
    }

    /// Random access is always done as an operand, never as a node
    pub fn ram(v: Self, i: Self) -> Operand<C> {
        match (v, i) {
            (Operand::Ram(box v, box Operand::Range(l)), Operand::Range(r)) =>
                Operand::ram(v, Operand::range(l.compose(&r))),
            (Operand::Ram(box v, box Operand::Range(r)), Operand::Value(Value::Index(i))) =>
                Operand::ram(v, r.compose_index(i as usize).into()),
            (Operand::Vec(vs), Operand::Value(Value::Index(i))) => vs[i as usize].clone(),
            (Operand::Vec(vs), Operand::Range(r)) =>
                Operand::vec(r.into_iter().map(|i| vs[i].clone()).collect::<Vec<_>>()),
            (Operand::Range(r), Operand::Value(Value::Index(i))) => r.compose_index(i as usize).into(),
            (v, i) => Operand::Ram(Box::new(v), Box::new(i)),
        }
    }

    pub fn concat(v1: Self, v2: Self) -> Option<Self> {
        match (v1, v2) {
            (Operand::Vec(mut vs1), Operand::Vec(vs2)) => {
                vs1.extend(vs2);
                Some(Operand::Vec(vs1))
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.push(v);
                Some(Operand::Vec(vs))
            },
            (_, _) => None
        }
    }

    pub fn add(v1: Self, v2: Self, typ: ATyp) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a + b)),
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Range(l + r)),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Range(l + CRange::singleton(r as usize))),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l, r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Range(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l.into(), r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (_, _) => None
        }
    }

    pub fn sub(v1: Self, v2: Self, typ: ATyp) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a - b)),
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Range(l - r)),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Range(l - CRange::singleton(r as usize))),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l, r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Range(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l.into(), r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (_, _) => None
        }
    }

    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a * b)),
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Range(l * r)),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Range(l * CRange::singleton(r as usize))),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(l, r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(r.into(), l, t.clone()))
                    .collect::<Option<_>>()?))
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter()
                    .map(|l| Operand::mul(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            // Default case, constructor
            (_, _) => None
        }
    }

    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a / b)),
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Range(l / r)),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Range(l / CRange::singleton(r as usize))),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(l, r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(r.into(), l, t.clone()))
                    .collect::<Option<_>>()?))
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter()
                    .map(|l| Operand::div(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            // Default case, constructor
            (_, _) => None
        }
    }

    pub fn rem(v1: Self, v2: Self, typ: ATyp) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a % b)),
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Range(l % r)),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Range(l % CRange::singleton(r as usize))),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::rem(l, r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::rem(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::rem(r.into(), l, t.clone()))
                    .collect::<Option<_>>()?))
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter()
                    .map(|l| Operand::rem(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            // Default case, constructor
            (_, _) => None
        }
    }

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a ^ b)),
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Range(l ^ r)),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Range(l ^ CRange::singleton(r as usize))),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::pow(l, r, t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::pow(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::pow(r.into(), l, t.clone()))
                    .collect::<Option<_>>()?))
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Some(Operand::Vec(l.into_iter()
                    .map(|l| Operand::pow(l, r.into(), t.clone()))
                    .collect::<Option<_>>()?))
            },
            // Default case, constructor
            (_, _) => None
        }
    }

    pub fn dot(v1: Self, v2: Self) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a.dot(b))),
            (Operand::Range(l), Operand::Range(r)) =>
                Some(Operand::Value(Value::Index(
                    l.into_iter()
                    .zip(r.into_iter())
                    .map(|(a, b)| (a * b) as u64)
                    .sum()))),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Some(Operand::Value(Value::Index(
                    l.into_iter()
                    .map(|a| (a * r as usize) as u64)
                    .sum()))),
            // Default case, constructor
            (_, _) => None
        }
    }

    pub fn not(v: Self) -> Operand<C> {
        match v {
            Operand::Not(box v) => v,
            _ => Operand::Not(Box::new(v)),
        }
    }

    pub fn equ(v1: Self, v2: Self) -> Option<Self> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Some(Operand::Value(Value::Bool(l == r))),
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(Value::Bool(a == b))),
            (_, _) => None
        }
    }

    pub fn and(v1: Self, v2: Self) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a & b)),
            (_, _) => None
        }
    }

   pub fn or(v1: Self, v2: Self) -> Option<Self> {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Some(Operand::Value(a | b)),
            (_, _) => None
        }
    }

    pub fn contains(v1: Self, v2: Self) -> Option<Self> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Value(Value::Index(r))) =>
                Some(Operand::Value(Value::Bool(l.contains(r as usize)))),
            (Operand::Vec(vs), v2) =>
                vs.iter().find_map(|v| Operand::equ(v.clone(), v2.clone())),
            (_, _) => None
        }
    }

    pub fn vec(vs: Vec<Operand<C>>) -> Operand<C> {
        Operand::Vec(vs)
    }
    pub fn underscore(n: &NodeIndex, typ: ATyp) -> Operand<C> {
        Operand::Underscore(*n, typ)
    }
    pub fn var(v: &Vid, n: &NodeIndex, typ: ATyp) -> Operand<C> {
        Operand::Var(v.clone(), *n, typ)
    }
    pub fn range(r: CRange) -> Operand<C> {
        Operand::Range(r)
    }
    pub fn edges(&self) -> Vec<(NodeIndex, Edge)> {
        match self {
            Operand::Underscore(n, _) => vec![(*n, Edge::data())],
            Operand::Var(v, n, _) => vec![(*n, Edge::var(v.clone()))],
            Operand::Ram(box a, box b) =>
                a.edges().into_iter()
                    .chain(b.edges().into_iter())
                    .collect(),
            Operand::Vec(vs) =>
                vs.into_iter()
                    .flat_map(|v| v.edges())
                    .collect(),
            Operand::Not(box v) => v.edges(),
            Operand::Value(_)
            | Operand::Gen(_)
            | Operand::Range(_) => vec![],
        }
    }
}

impl<C: ArkConfig> fmt::Display for Operand<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operand::Value(x) => write!(f, "{}", x),
            Operand::Ram(box v, r) => write!(f, "{}[{}]", v, r),
            Operand::Vec(vs) => {
                write!(f, "[")?;
                for v in vs.iter() {
                    write!(f, "{}, ", v)?;
                }
                write!(f, "]")
            },
            Operand::Gen(t) => write!(f, "gen<{}>", t),
            Operand::Not(v) => write!(f, "!{}", v),
            Operand::Range(r) => write!(f, "{}", r),
            Operand::Underscore(n, _) => write!(f, "_"),
            Operand::Var(v, n, _) => write!(f, "{}", v),
        }
    }
}

impl<C: ArkConfig> From<Value<C>> for Operand<C> {
    fn from(v: Value<C>) -> Self {
        Operand::Value(v)
    }
}

impl<C: ArkConfig> From<u64> for Operand<C> {
    fn from(v: u64) -> Self {
        Operand::Value(Value::Index(v))
    }
}

impl<C: ArkConfig> From<usize> for Operand<C> {
    fn from(v: usize) -> Self {
        Operand::Value(Value::Index(v as u64))
    }
}

impl<C: ArkConfig> From<CRange> for Operand<C> {
    fn from(r: CRange) -> Self {
        Operand::Range(r)
    }
}

impl<C: ArkConfig> fmt::Display for Op<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Bin(op, a, b) => write!(f, "({} {} {})", a, op, b),
            Op::Eval(a) => write!(f, "(eval {})", a),
            Op::Coef(a) => write!(f, "(coef {})", a),
            Op::Hash(a) => write!(f, "(hash {})", a),
            Op::Contains(a, b) => write!(f, "({} in {})", a, b),
            Op::Challenge(tid) => write!(f, "challenge<{}>", tid),
            Op::Random(t) => write!(f, "random<{}>", t),
            Op::Check(a) => write!(f, "(check {})", a)
        }
    }
}

impl<C: ArkConfig> Op<C> {
    pub fn coef(op: &Operand<C>) -> Self {
        Op::Coef(op.clone())
    }
    pub fn eval(op: &Operand<C>) -> Self {
        Op::Eval(op.clone())
    }
    pub fn contains(a: &Operand<C>, b: &Operand<C>) -> Self {
        Op::Contains(a.clone(), b.clone())
    }
    pub fn challenge(tid: ATyp) -> Self {
        Op::Challenge(tid)
    }
    pub fn random(tid: ATyp) -> Self {
        Op::Random(tid)
    }
    pub fn hash(op: &Operand<C>) -> Self {
        Op::Hash(op.clone())
    }
    pub fn check(op: &Operand<C>) -> Self {
        Op::Check(op.clone())
    }
    pub fn bin(op: BinOp, a: &Operand<C>, b: &Operand<C>) -> Self {
        Op::Bin(op, a.clone(), b.clone())
    }
}
