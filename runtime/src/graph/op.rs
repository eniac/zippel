use lang::typ::range::CRange;
use lang::typ::ATyp;
use lang::ast::BinOp;

use crate::arkworks::ArkConfig;
use crate::arkworks::Value;

use petgraph::graph::NodeIndex;
use std::fmt;

/// Typed operands are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Operand<C: ArkConfig> {
    /// Value
    Value(Value<C>),
    /// Binary operation
    Bin(BinOp, Box<Operand<C>>, Box<Operand<C>>, ATyp),
    /// Boolean not
    Not(Box<Operand<C>>),
    /// Generator for a group
    Gen(ATyp),
    /// Random element
    Rand(ATyp),
    /// Node input
    Underscore(NodeIndex, ATyp),
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

    /// Random oracle challenge
    Challenge(ATyp),

    /// Absorb values in the transcript
    Hash(T),

    /// Convert from evaluation domain to lagrange domain.
    Coef(T),

    /// Convert from lagrange domain to evaluation domain
    Eval(T),

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
            Operand::Bin(_, _, _, t) => t.clone(),
            Operand::Not(_) => ATyp::bool(),
            Operand::Gen(t) => t.clone(),
            Operand::Rand(t) => t.clone(),
            Operand::Underscore(_, t) => t.clone(),
            Operand::Range(r) => ATyp::vec(ATyp::fin(r.clone()), r.len()),
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

    /// Smart constructors to simplify operands a bit
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

    pub fn concat(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Vec(mut vs1), Operand::Vec(vs2)) => {
                vs1.extend(vs2);
                Operand::Vec(vs1)
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.push(v);
                Operand::Vec(vs)
            },
            (l, r) =>
                Operand::Bin(BinOp::Concat, Box::new(l), Box::new(r), typ),
        }
    }

    pub fn add(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l + r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l + CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l, r, t.clone())).collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l, r.into(), t.clone())).collect())
            },
            (Operand::Range(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l.into(), r, t.clone())).collect())
            },
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Add, Box::new(l), Box::new(r), typ)
        }
    }

    pub fn sub(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l - r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l - CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l, r, t.clone())).collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l, r.into(), t.clone())).collect())
            },
            (Operand::Range(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l.into(), r, t.clone())).collect())
            },
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Sub, Box::new(l), Box::new(r), typ)
        }
    }

    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l * r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l * CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(l, r, t.clone())).collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(l, r.into(), t.clone())).collect())
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(r.into(), l, t.clone())).collect())
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter()
                    .map(|l| Operand::mul(l, r.into(), t.clone())).collect())
            },
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Mul, Box::new(l), Box::new(r), typ),
        }
    }

    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l / r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l / CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(l, r, t.clone())).collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(l, r.into(), t.clone())).collect())
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(r.into(), l, t.clone())).collect())
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter()
                    .map(|l| Operand::div(l, r.into(), t.clone())).collect())
            },
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Div, Box::new(l), Box::new(r), typ),
        }
    }

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l ^ r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l ^ CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::pow(l, r, t.clone())).collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::pow(l, r.into(), t.clone())).collect())
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::pow(r.into(), l, t.clone())).collect())
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter()
                    .map(|l| Operand::pow(l, r.into(), t.clone())).collect())
            },
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Pow, Box::new(l), Box::new(r), typ),
        }
    }

    pub fn dot(v1: Self, v2: Self, typ: ATyp) -> Operand<C> {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) =>
                Operand::Value(Value::Index(
                    l.into_iter()
                    .zip(r.into_iter())
                    .map(|(a, b)| (a * b) as u64)
                    .sum())),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Value(Value::Index(
                    l.into_iter()
                    .map(|a| (a * r as usize) as u64)
                    .sum())),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec().unwrap();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::dot(l, r, t.clone())).collect())
            },
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Dot, Box::new(l), Box::new(r), typ),
        }
    }

    pub fn not(v: Self) -> Operand<C> {
        match v {
            Operand::Not(box v) => v,
            _ => Operand::Not(Box::new(v)),
        }
    }

    pub fn vec(vs: Vec<Operand<C>>) -> Operand<C> {
        Operand::Vec(vs)
    }
    pub fn underscore(n: &NodeIndex, typ: ATyp) -> Operand<C> {
        Operand::Underscore(*n, typ)
    }
    pub fn range(r: CRange) -> Operand<C> {
        Operand::Range(r)
    }
    pub fn nodes(&self) -> Vec<NodeIndex> {
        match self {
            Operand::Underscore(n, _) => vec![*n],
            Operand::Ram(box v, _) => v.nodes(),
            Operand::Vec(vs) => {
                let mut res = Vec::new();
                for v in vs.iter() {
                    res.extend(v.nodes());
                }
                res
            },
            Operand::Bin(_, l, r, _) => {
                let mut res = l.nodes();
                res.extend(r.nodes());
                res
            },
            _ => vec![],
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
            Operand::Rand(t) => write!(f, "rand<{}>", t),
            Operand::Not(v) => write!(f, "!{}", v),
            Operand::Bin(op, l, r, t) =>
                write!(f, "({} {} {}) : {}", l, op, r, t),
            Operand::Range(r) => write!(f, "{}", r),
            Operand::Underscore(n, t) => write!(f, "_{} : {}", n.index(), t),
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
            Op::Bin(op, a, b) => write!(f, "({} {} {})", op, a, b),
            Op::Eval(a) => write!(f, "(eval {})", a),
            Op::Coef(a) => write!(f, "(coef {})", a),
            Op::Hash(a) => write!(f, "(hash {})", a),
            Op::Contains(a, b) => write!(f, "(in {} {})", a, b),
            Op::Challenge(tid) => write!(f, "challenge<{}>", tid),
            Op::Check(a) => write!(f, "(check {})", a)
        }
    }
}

impl<C: ArkConfig> Op<C> {
    pub fn coef(op: Operand<C>) -> Self {
        Op::Coef(op)
    }
    pub fn eval(op: Operand<C>) -> Self {
        Op::Eval(op)
    }
    pub fn hash(op: Operand<C>) -> Self {
        Op::Hash(op)
    }
    pub fn contains(a: Operand<C>, b: Operand<C>) -> Self {
        Op::Contains(a, b)
    }
    pub fn check(op: Operand<C>) -> Self {
        Op::Check(op)
    }
    pub fn challenge(tid: ATyp) -> Self {
        Op::Challenge(tid)
    }
    pub fn bin(op: BinOp, a: Operand<C>, b: Operand<C>) -> Self {
        Op::Bin(op, a, b)
    }
}
