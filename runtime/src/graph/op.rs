use lang::typ::range::CRange;
use lang::typ::{CTyp, TypeError, Nothing, Typeable, Kind};
use lang::ast::{CExp, BinOp, CSig, CBody};
use lang::id::{Tid, Vid};
use crate::arkworks::{Value, ATyp, ArkConfig, ArkGroupOps, ArkScalarOps, ArkPairingOps};
use crate::graph::Edge;

use share::Ctx;
use petgraph::graph::NodeIndex;
use std::ops::{Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr};
use std::fmt;

/// Typed operands are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Operand<C: ArkConfig> {
    /// Value
    Value(Value<C>),

    /// Binary operations
    Bin(BinOp, Box<Operand<C>>, Box<Operand<C>>, ATyp),

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

    /// Random element
    Random(ATyp),

    /// Random oracle challenge
    Challenge(ATyp),

    /// Convert from evaluation domain to lagrange domain.
    Coef(Box<Operand<C>>),

    /// Convert from lagrange domain to evaluation domain
    Eval(Box<Operand<C>>),

    /// Hash operation into a cryptographic transcript
    Hash(Box<Operand<C>>),

    /// Assertion or verification check
    Check(Box<Operand<C>>),
}

impl<C: ArkConfig> Operand<C> {
    pub fn typ(&self) -> ATyp {
        match &self {
            Operand::Value(v) => v.typ(),
            Operand::Bin(_, _, _, typ) => typ.clone(),
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
            Operand::Random(t) => t.clone(),
            Operand::Challenge(t) => t.clone(),
            Operand::Coef(box op) => op.typ(),
            Operand::Eval(box op) => op.typ(),
            Operand::Hash(_) => ATyp::Scalar,
            Operand::Check(box op) => op.typ(),
        }
    }

    pub fn bin(op: BinOp, a: Self, b: Self, typ: ATyp) -> Self {
        match op {
            BinOp::Add => Self::add(a, b, typ),
            BinOp::Sub => Self::sub(a, b, typ),
            BinOp::Mul => Self::mul(a, b, typ),
            BinOp::Div => Self::div(a, b, typ),
            BinOp::Rem => Self::rem(a, b, typ),
            BinOp::Pow => Self::pow(a, b, typ),
            BinOp::Dot => Self::dot(a, b, typ),
            BinOp::Concat => Self::concat(a, b, typ),
            BinOp::Contains => Self::contains(a, b),
            BinOp::Equ => Self::equ(a, b),
            BinOp::And => Self::and(a, b),
            BinOp::Or => Self::or(a, b),
        }
    }

    pub fn index(i: usize) -> Self {
        Operand::Value(Value::Index(i as u64))
    }

    /// Random access simplifications
    pub fn ram(v: Self, i: Self) -> Self {
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

    /// Concatenation simplifications
    pub fn concat(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Vec(mut vs1), Operand::Vec(vs2)) => {
                vs1.extend(vs2);
                Operand::Vec(vs1)
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                let (t, _) = typ.clone().into_vec();
                if v.typ() == t {
                    vs.push(v);
                    Operand::Vec(vs)
                } else {
                    Operand::Bin(BinOp::Concat, Box::new(v), Box::new(Operand::Vec(vs)), typ)
                }
            },
            (v1, v2) => Operand::Bin(BinOp::Concat, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn add(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a + b),
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l + r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l + CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l, r, t.clone()))
                    .collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l, r.into(), t.clone()))
                    .collect())
            },
            (Operand::Range(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::add(l.into(), r, t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Operand::Eval(box l), Operand::Eval(box r)) =>
                Operand::Eval(Box::new(Operand::add(l, r, typ))),
            (Operand::Coef(box l), Operand::Coef(box r)) =>
                Operand::Coef(Box::new(Operand::add(l, r, typ))),
            (v1, v2) => Operand::Bin(BinOp::Add, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn sub(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a - b),
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l - r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l - CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l, r, t.clone()))
                    .collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l, r.into(), t.clone()))
                    .collect())
            },
            (Operand::Range(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::sub(l.into(), r, t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Operand::Eval(box l), Operand::Eval(box r)) =>
                Operand::Eval(Box::new(Operand::sub(l, r, typ))),
            (Operand::Coef(box l), Operand::Coef(box r)) =>
                Operand::Coef(Box::new(Operand::sub(l, r, typ))),
            (v1, v2) => Operand::Bin(BinOp::Sub, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a * b),
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l * r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l * CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(l, r, t.clone()))
                    .collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(l, r.into(), t.clone()))
                    .collect())
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::mul(r.into(), l, t.clone()))
                    .collect())
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter()
                    .map(|l| Operand::mul(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Operand::Coef(box l), Operand::Coef(box r)) => {
                let (_, n) = typ.clone().into_vec();
                Operand::coef(Operand::mul(Operand::pad_zeroes(l, n), Operand::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => Operand::Bin(BinOp::Mul, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn coef(op: Self) -> Operand<C> {
        match op {
            Operand::Eval(box op) => op,
            _ => Operand::Coef(Box::new(op)),
        }
    }

    pub fn eval(op: Self) -> Operand<C> {
        match op {
            Operand::Coef(box op) => op,
            Operand::Bin(op @ (BinOp::Mul | BinOp::Div | BinOp::Rem), box op1, box op2, typ) =>
                Operand::bin(op, Operand::eval(op1), Operand::eval(op2), typ),
            op => Operand::Eval(Box::new(op)),
        }
    }

    pub fn zero(typ: &ATyp) -> Operand<C> {
        match typ {
            ATyp::Fin(_) => Operand::Value(Value::Index(0)),
            ATyp::Vec(box typ, n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(Operand::zero(typ));
                }
                Operand::Vec(vs)
            },
            ATyp::Bool => Operand::Value(Value::Bool(false)),
            ATyp::Scalar => Operand::Value(Value::Scalar(C::FOps::zero())),
            ATyp::G1 => Operand::Value(Value::G1(C::G1Ops::zero())),
            ATyp::G2 => Operand::Value(Value::G2(C::G2Ops::zero())),
            ATyp::GT => Operand::Value(Value::GT(C::POps::zero())),
            ATyp::G1Affine => Operand::Value(Value::G1Affine(C::G1Ops::zero().into())),
            ATyp::G2Affine => Operand::Value(Value::G2Affine(C::G2Ops::zero().into())),
        }
    }

    fn pad_zeroes(v: Operand<C>, n: usize) -> Operand<C> {
        let typ = v.typ();
        let (t, m) = typ.into_vec();
        if m < n {
            Operand::concat(v, Operand::vec(vec![Operand::zero(&t); n - m]), ATyp::vec(t, n))
        } else {
            v
        }
    }

    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a / b),
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l / r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l / CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(l, r, t.clone()))
                    .collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(l, r.into(), t.clone()))
                    .collect())
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::div(r.into(), l, t.clone()))
                    .collect())
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter()
                    .map(|l| Operand::div(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Operand::Coef(box l), Operand::Coef(box r)) => {
                let (_, n) = typ.clone().into_vec();
                Operand::coef(Operand::div(Operand::pad_zeroes(l, n), Operand::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => Operand::Bin(BinOp::Div, Box::new(v1), Box::new(v2), typ)
        }
    }

    pub fn rem(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a % b),
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l % r),
            (Operand::Range(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Range(l)) =>
                Operand::Range(l % CRange::singleton(r as usize)),
            (Operand::Vec(l), Operand::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::rem(l, r, t.clone()))
                    .collect())
            },
            (Operand::Vec(l), Operand::Range(r)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::rem(l, r.into(), t.clone()))
                    .collect())
            },
            (Operand::Range(r), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Operand::rem(r.into(), l, t.clone()))
                    .collect())
            },
           (Operand::Vec(l), Operand::Value(Value::Index(r)))
            | (Operand::Value(Value::Index(r)), Operand::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(l.into_iter()
                    .map(|l| Operand::rem(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Operand::Coef(box l), Operand::Coef(box r)) => {
                let (_, n) = typ.clone().into_vec();
                Operand::coef(Operand::rem(Operand::pad_zeroes(l, n), Operand::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => Operand::Bin(BinOp::Rem, Box::new(v1), Box::new(v2), typ)
        }
    }

    pub fn one(typ: &ATyp) -> Operand<C> {
        match typ {
            ATyp::Fin(_) => Operand::Value(Value::Index(1)),
            ATyp::Vec(box typ, n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(Operand::one(typ));
                }
                Operand::Vec(vs)
            },
            ATyp::Scalar => Operand::Value(Value::Scalar(C::FOps::one())),
            _ => unreachable!("UncaughtError: Operand::one() not implemented for type {}", typ),
        }
    }

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Self {
        match v2 {
            Operand::Value(Value::Index(r)) => {
                let mut exp: u64 = r;
                let mut base = Operand::one(&typ);
                while exp > 0 {
                    if exp % 2 == 1 {
                        base = Operand::mul(v1.clone(), base.clone(), typ.clone());
                    }
                    base = Operand::mul(base.clone(), base.clone(), typ.clone());
                    exp /= 2;
                };
                base
            },
            Operand::Range(r) => {
                let (t, _) = typ.into_vec();
                Operand::Vec(r.into_iter()
                    .map(|r| Operand::pow(v1.clone(), r.into(), t.clone()))
                    .collect())
            },
            v2 => Operand::Bin(BinOp::Pow, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn dot(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a.dot(b)),
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
            // Default case, constructor
            (v1, v2) => Operand::Bin(BinOp::Dot, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn not(v: Self) -> Operand<C> {
        match v {
            Operand::Not(box v) => v,
            _ => Operand::Not(Box::new(v)),
        }
    }

    pub fn equ(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Value(Value::Bool(l == r)),
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(Value::Bool(a == b)),
            (v1, v2) => Operand::Bin(BinOp::Equ, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn and(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Operand::Value(Value::Bool(false)), _)
            | (_, Operand::Value(Value::Bool(false))) => Operand::bfalse(),
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a & b),
            (v1, v2) => Operand::Bin(BinOp::And, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn btrue() -> Self {
        Operand::Value(Value::Bool(true))
    }
    pub fn bfalse() -> Self {
        Operand::Value(Value::Bool(false))
    }

    pub fn or(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Operand::Value(Value::Bool(true)), _)
            | (_, Operand::Value(Value::Bool(true))) => Operand::btrue(),
            (Operand::Value(a), Operand::Value(b)) => Operand::Value(a | b),
            (v1, v2) => Operand::Bin(BinOp::Or, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn contains(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Operand::Range(l), Operand::Value(Value::Index(r))) =>
                Operand::Value(Value::Bool(l.contains(r as usize))),
            (Operand::Vec(vs), v2) =>
                vs.iter().map(|v| Operand::equ(v.clone(), v2.clone()))
                    .reduce(|a, b| Operand::or(a, b))
                    .unwrap_or(Operand::Value(Value::Bool(false))),
            (v1, v2) => Operand::Bin(BinOp::Contains, Box::new(v1), Box::new(v2), ATyp::Bool),
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

    pub fn challenge(typ: ATyp) -> Operand<C> {
        Operand::Challenge(typ)
    }
    pub fn random(typ: ATyp) -> Operand<C> {
        Operand::Random(typ)
    }
    pub fn hash(op: Operand<C>) -> Operand<C> {
        Operand::Hash(Box::new(op))
    }

    pub fn check(op: Operand<C>) -> Operand<C> {
        Operand::Check(Box::new(op))
    }

    pub fn dependencies(&self) -> Vec<(NodeIndex, Option<Vid>)> {
        match self {
            Operand::Underscore(n, _) => vec![(*n, None)],
            Operand::Bin(_, box a, box b, _)
            | Operand::Ram(box a, box b) =>
                a.dependencies().into_iter()
                    .chain(b.dependencies().into_iter())
                    .collect(),
            Operand::Var(v, n, _) => vec![(*n, Some(v.clone()))],
            Operand::Vec(vs) =>
                vs.into_iter()
                    .flat_map(|v| v.dependencies())
                    .collect(),
            Operand::Not(box v)
            | Operand::Coef(box v)
            | Operand::Check(box v)
            | Operand::Hash(box v)
            | Operand::Eval(box v) => v.dependencies(),
            Operand::Value(_)
            | Operand::Gen(_)
            | Operand::Random(_)
            | Operand::Challenge(_)
            | Operand::Range(_) => vec![],
        }
    }
}

impl<C: ArkConfig> fmt::Display for Operand<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operand::Value(x) => write!(f, "{}", x),
            Operand::Bin(op, box a, box b, _) => write!(f, "({} {} {})", a, op, b),
            Operand::Eval(box v) => write!(f, "(eval {})", v),
            Operand::Coef(box v) => write!(f, "(coef {})", v),
            Operand::Hash(box v) => write!(f, "(hash {})", v),
            Operand::Check(box v) => write!(f, "(check {})", v),
            Operand::Challenge(t) => write!(f, "challenge<{}>", t),
            Operand::Random(t) => write!(f, "random<{}>", t),
            Operand::Ram(box v, r) => write!(f, "{}[{}]", v, r),
            Operand::Vec(vs) => {
                write!(f, "[{}", vs[0])?;
                for v in vs.iter().skip(1) {
                    write!(f, ", {}", v)?;
                }
                write!(f, "]")
            },
            Operand::Gen(t) => write!(f, "gen<{}>", t),
            Operand::Not(v) => write!(f, "!{}", v),
            Operand::Range(r) => write!(f, "{}", r),
            Operand::Underscore(_, _) => write!(f, "_"),
            Operand::Var(v, _, _) => write!(f, "{}", v),
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

