use lang::typ::range::CRange;
use lang::typ::{CTyp, TypeError, Nothing, Typeable, Kind};
use lang::ast::{CExp, BinOp, CSig, CBody};
use lang::id::{Tid, Vid};
use backend::{Value, ATyp, ArkConfig, ArkGroupOps, ArkScalarOps, ArkPairingOps};

use petgraph::graph::NodeIndex;
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use std::ops::{Add, Sub, Mul, Div, Rem, BitXor, BitAnd, BitOr};
use std::fmt;

/// Typed operations are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Op<C: ArkConfig> {
    /// Value
    Value(Value<C>),

    /// Binary operations
    Bin(BinOp, Box<Op<C>>, Box<Op<C>>, ATyp),

    /// Boolean not
    Not(Box<Op<C>>),

    /// Generator for a group
    Gen(ATyp),

    /// Node input
    Underscore(NodeIndex, ATyp),

    /// Variable input
    Var(Vid, NodeIndex, ATyp),

    /// Range of numbers
    Range(CRange),

    /// Random access into a value
    Ram(Box<Op<C>>, Box<Op<C>>),

    /// Vector of values
    Vec(Vec<Op<C>>),

    /// Random element
    Random(ATyp),

    /// Random oracle challenge
    Challenge(ATyp),

    /// Convert from evaluation domain to lagrange domain.
    Coef(Box<Op<C>>),

    /// Convert from lagrange domain to evaluation domain
    Eval(Box<Op<C>>),

    /// Assertion or verification check
    Check(Box<Op<C>>),
}

impl<C: ArkConfig> Op<C> {
    pub fn typ(&self) -> ATyp {
        match &self {
            Op::Value(v) => v.typ(),
            Op::Bin(_, _, _, typ) => typ.clone(),
            Op::Not(_) => ATyp::Bool,
            Op::Gen(t) => t.clone(),
            Op::Underscore(_, t) => t.clone(),
            Op::Var(_, _, t) => t.clone(),
            Op::Range(r) => ATyp::vec(ATyp::Fin(r.clone()), r.len()),
            Op::Ram(box l, box r) =>
                match (l.typ(), r.typ()) {
                    (ATyp::Vec(box typ, _), ATyp::Fin(_)) => typ,
                    (ATyp::Vec(box typ, _), ATyp::Vec(box ATyp::Fin(_), m)) =>
                        ATyp::vec(typ, m),
                    (a, b) =>
                        panic!("UncaughtError: Ram operand must be a vector, not {} [ {} ]", a, b),
                }
            Op::Vec(vs) => {
                let typ = vs[0].typ();
                for v in vs.iter().skip(1) {
                    if v.typ() != typ {
                        panic!("UncaughtError: Vector operands must be of the same type: {} != {}", typ, v.typ());
                    }
                }
                ATyp::vec(typ, vs.len())
            }
            Op::Random(t) => t.clone(),
            Op::Challenge(t) => t.clone(),
            Op::Coef(box op) => op.typ(),
            Op::Eval(box op) => op.typ(),
            Op::Check(box op) => op.typ(),
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
        Op::Value(Value::Index(i as u64))
    }

    /// Random access simplifications
    pub fn ram(v: Self, i: Self) -> Self {
        match (v, i) {
            (Op::Ram(box v, box Op::Range(l)), Op::Range(r)) =>
                Op::ram(v, Op::range(l.compose(&r))),
            (Op::Ram(box v, box Op::Range(r)), Op::Value(Value::Index(i))) =>
                Op::ram(v, r.compose_index(i as usize).into()),
            (Op::Vec(vs), Op::Value(Value::Index(i))) => vs[i as usize].clone(),
            (Op::Vec(vs), Op::Range(r)) =>
                Op::vec(r.into_iter().map(|i| vs[i].clone()).collect::<Vec<_>>()),
            (Op::Range(r), Op::Value(Value::Index(i))) => r.compose_index(i as usize).into(),
            (v, i) => Op::Ram(Box::new(v), Box::new(i)),
        }
    }

    /// Concatenation simplifications
    pub fn concat(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Vec(mut vs1), Op::Vec(vs2)) => {
                vs1.extend(vs2);
                Op::Vec(vs1)
            },
            (Op::Vec(mut vs), v) | (v, Op::Vec(mut vs)) => {
                let (t, _) = typ.clone().into_vec();
                if v.typ() == t {
                    vs.push(v);
                    Op::Vec(vs)
                } else {
                    Op::Bin(BinOp::Concat, Box::new(v), Box::new(Op::Vec(vs)), typ)
                }
            },
            (v1, v2) => Op::Bin(BinOp::Concat, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn add(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a + b),
            (Op::Range(l), Op::Range(r)) => Op::Range(l + r),
            (Op::Range(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Range(l)) =>
                Op::Range(l + CRange::singleton(r as usize)),
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::add(l, r, t.clone()))
                    .collect())
            },
            (Op::Vec(l), Op::Range(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::add(l, r.into(), t.clone()))
                    .collect())
            },
            (Op::Range(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::add(l.into(), r, t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Op::Eval(box l), Op::Eval(box r)) =>
                Op::Eval(Box::new(Op::add(l, r, typ))),
            (Op::Coef(box l), Op::Coef(box r)) =>
                Op::Coef(Box::new(Op::add(l, r, typ))),
            (v1, v2) => Op::Bin(BinOp::Add, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn sub(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a - b),
            (Op::Range(l), Op::Range(r)) => Op::Range(l - r),
            (Op::Range(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Range(l)) =>
                Op::Range(l - CRange::singleton(r as usize)),
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::sub(l, r, t.clone()))
                    .collect())
            },
            (Op::Vec(l), Op::Range(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::sub(l, r.into(), t.clone()))
                    .collect())
            },
            (Op::Range(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::sub(l.into(), r, t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Op::Eval(box l), Op::Eval(box r)) =>
                Op::Eval(Box::new(Op::sub(l, r, typ))),
            (Op::Coef(box l), Op::Coef(box r)) =>
                Op::Coef(Box::new(Op::sub(l, r, typ))),
            (v1, v2) => Op::Bin(BinOp::Sub, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a * b),
            (Op::Range(l), Op::Range(r)) => Op::Range(l * r),
            (Op::Range(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Range(l)) =>
                Op::Range(l * CRange::singleton(r as usize)),
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::mul(l, r, t.clone()))
                    .collect())
            },
            (Op::Vec(l), Op::Range(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::mul(l, r.into(), t.clone()))
                    .collect())
            },
            (Op::Range(r), Op::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::mul(r.into(), l, t.clone()))
                    .collect())
            },
           (Op::Vec(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter()
                    .map(|l| Op::mul(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Op::Coef(box l), Op::Coef(box r)) => {
                let (_, n) = typ.clone().into_vec();
                Op::coef(Op::mul(Op::pad_zeroes(l, n), Op::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => Op::Bin(BinOp::Mul, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn coef(op: Self) -> Op<C> {
        match op {
            Op::Eval(box op) => op,
            _ => Op::Coef(Box::new(op)),
        }
    }

    pub fn eval(op: Self) -> Op<C> {
        match op {
            Op::Coef(box op) => op,
            Op::Bin(op @ (BinOp::Mul | BinOp::Div | BinOp::Rem), box op1, box op2, typ) =>
                Op::bin(op, Op::eval(op1), Op::eval(op2), typ),
            op => Op::Eval(Box::new(op)),
        }
    }

    pub fn zero(typ: &ATyp) -> Op<C> {
        match typ {
            ATyp::Fin(_) => Op::Value(Value::Index(0)),
            ATyp::Vec(box typ, n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(Op::zero(typ));
                }
                Op::Vec(vs)
            },
            ATyp::Bool => Op::Value(Value::Bool(false)),
            ATyp::Scalar => Op::Value(Value::Scalar(C::FOps::zero())),
            ATyp::G1 => Op::Value(Value::G1(C::G1Ops::zero())),
            ATyp::G2 => Op::Value(Value::G2(C::G2Ops::zero())),
            ATyp::GT => Op::Value(Value::GT(C::POps::zero())),
            ATyp::G1Affine => Op::Value(Value::G1Affine(C::G1Ops::zero().into())),
            ATyp::G2Affine => Op::Value(Value::G2Affine(C::G2Ops::zero().into())),
        }
    }

    fn pad_zeroes(v: Op<C>, n: usize) -> Op<C> {
        let typ = v.typ();
        let (t, m) = typ.into_vec();
        if m < n {
            Op::concat(v, Op::vec(vec![Op::zero(&t); n - m]), ATyp::vec(t, n))
        } else {
            v
        }
    }

    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a / b),
            (Op::Range(l), Op::Range(r)) => Op::Range(l / r),
            (Op::Range(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Range(l)) =>
                Op::Range(l / CRange::singleton(r as usize)),
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::div(l, r, t.clone()))
                    .collect())
            },
            (Op::Vec(l), Op::Range(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::div(l, r.into(), t.clone()))
                    .collect())
            },
            (Op::Range(r), Op::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::div(r.into(), l, t.clone()))
                    .collect())
            },
           (Op::Vec(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter()
                    .map(|l| Op::div(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Op::Coef(box l), Op::Coef(box r)) => {
                let (_, n) = typ.clone().into_vec();
                Op::coef(Op::div(Op::pad_zeroes(l, n), Op::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => Op::Bin(BinOp::Div, Box::new(v1), Box::new(v2), typ)
        }
    }

    pub fn rem(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a % b),
            (Op::Range(l), Op::Range(r)) => Op::Range(l % r),
            (Op::Range(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Range(l)) =>
                Op::Range(l % CRange::singleton(r as usize)),
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::rem(l, r, t.clone()))
                    .collect())
            },
            (Op::Vec(l), Op::Range(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::rem(l, r.into(), t.clone()))
                    .collect())
            },
            (Op::Range(r), Op::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)| Op::rem(r.into(), l, t.clone()))
                    .collect())
            },
           (Op::Vec(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Vec(l)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter()
                    .map(|l| Op::rem(l, r.into(), t.clone()))
                    .collect())
            },
            // Commuting conversions
            (Op::Coef(box l), Op::Coef(box r)) => {
                let (_, n) = typ.clone().into_vec();
                Op::coef(Op::rem(Op::pad_zeroes(l, n), Op::pad_zeroes(r, n), typ))
            },
            // Default case, constructor
            (v1, v2) => Op::Bin(BinOp::Rem, Box::new(v1), Box::new(v2), typ)
        }
    }

    pub fn one(typ: &ATyp) -> Op<C> {
        match typ {
            ATyp::Fin(_) => Op::Value(Value::Index(1)),
            ATyp::Vec(box typ, n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(Op::one(typ));
                }
                Op::Vec(vs)
            },
            ATyp::Scalar => Op::Value(Value::Scalar(C::FOps::one())),
            _ => unreachable!("UncaughtError: Op::one() not implemented for type {}", typ),
        }
    }

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Self {
        match v2 {
            Op::Value(Value::Index(r)) => {
                let mut exp: u64 = r;
                let mut base = Op::one(&typ);
                while exp > 0 {
                    if exp % 2 == 1 {
                        base = Op::mul(v1.clone(), base.clone(), typ.clone());
                    }
                    base = Op::mul(base.clone(), base.clone(), typ.clone());
                    exp /= 2;
                };
                base
            },
            Op::Range(r) => {
                let (t, _) = typ.into_vec();
                Op::Vec(r.into_iter()
                    .map(|r| Op::pow(v1.clone(), r.into(), t.clone()))
                    .collect())
            },
            v2 => Op::Bin(BinOp::Pow, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn dot(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a.dot(b)),
            (Op::Range(l), Op::Range(r)) =>
                Op::Value(Value::Index(
                    l.into_iter()
                    .zip(r.into_iter())
                    .map(|(a, b)| (a * b) as u64)
                    .sum())),
            (Op::Range(l), Op::Value(Value::Index(r)))
            | (Op::Value(Value::Index(r)), Op::Range(l)) =>
                Op::Value(Value::Index(
                    l.into_iter()
                    .map(|a| (a * r as usize) as u64)
                    .sum())),
            // Default case, constructor
            (v1, v2) => Op::Bin(BinOp::Dot, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn not(v: Self) -> Op<C> {
        match v {
            Op::Not(box v) => v,
            _ => Op::Not(Box::new(v)),
        }
    }

    pub fn equ(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Range(l), Op::Range(r)) => Op::Value(Value::Bool(l == r)),
            (Op::Value(a), Op::Value(b)) => Op::Value(Value::Bool(a == b)),
            (v1, v2) => Op::Bin(BinOp::Equ, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn and(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Value(Value::Bool(false)), _)
            | (_, Op::Value(Value::Bool(false))) => Op::bfalse(),
            (Op::Value(a), Op::Value(b)) => Op::Value(a & b),
            (v1, v2) => Op::Bin(BinOp::And, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn btrue() -> Self {
        Op::Value(Value::Bool(true))
    }
    pub fn bfalse() -> Self {
        Op::Value(Value::Bool(false))
    }

    pub fn or(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Value(Value::Bool(true)), _)
            | (_, Op::Value(Value::Bool(true))) => Op::btrue(),
            (Op::Value(a), Op::Value(b)) => Op::Value(a | b),
            (v1, v2) => Op::Bin(BinOp::Or, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn contains(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Range(l), Op::Value(Value::Index(r))) =>
                Op::Value(Value::Bool(l.contains(r as usize))),
            (Op::Vec(vs), v2) =>
                vs.iter().map(|v| Op::equ(v.clone(), v2.clone()))
                    .reduce(|a, b| Op::or(a, b))
                    .unwrap_or(Op::Value(Value::Bool(false))),
            (v1, v2) => Op::Bin(BinOp::Contains, Box::new(v1), Box::new(v2), ATyp::Bool),
        }
    }

    pub fn vec(vs: Vec<Op<C>>) -> Op<C> {
        Op::Vec(vs)
    }
    pub fn underscore(n: &NodeIndex, typ: ATyp) -> Op<C> {
        Op::Underscore(*n, typ)
    }
    pub fn var(v: &Vid, n: &NodeIndex, typ: ATyp) -> Op<C> {
        Op::Var(v.clone(), *n, typ)
    }
    pub fn range(r: CRange) -> Op<C> {
        Op::Range(r)
    }

    pub fn challenge(typ: ATyp) -> Op<C> {
        Op::Challenge(typ)
    }
    pub fn random(typ: ATyp) -> Op<C> {
        Op::Random(typ)
    }

    pub fn check(op: Op<C>) -> Op<C> {
        Op::Check(Box::new(op))
    }

    pub fn dependencies(&self) -> Vec<(NodeIndex, Option<Vid>)> {
        match self {
            Op::Underscore(n, _) => vec![(*n, None)],
            Op::Bin(_, box a, box b, _)
            | Op::Ram(box a, box b) =>
                a.dependencies().into_iter()
                    .chain(b.dependencies().into_iter())
                    .collect(),
            Op::Var(v, n, _) => vec![(*n, Some(v.clone()))],
            Op::Vec(vs) =>
                vs.into_iter()
                    .flat_map(|v| v.dependencies())
                    .collect(),
            Op::Not(box v)
            | Op::Coef(box v)
            | Op::Check(box v)
            | Op::Eval(box v) => v.dependencies(),
            Op::Value(_)
            | Op::Gen(_)
            | Op::Random(_)
            | Op::Challenge(_)
            | Op::Range(_) => vec![],
        }
    }
}

/// Pretty-printer for Operations
impl<'a, D, C, A> Pretty<'a, D, A> for Op<C>
where
    D: DocAllocator<'a, A>,
    C: ArkConfig,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Op::Value(v) => allocator.text(format!("{}", v)),
            Op::Bin(op, box a, box b, _) => {
                allocator.concat(vec![
                    allocator.text("("),
                    a.pretty(allocator),
                    allocator.text(format!(" {} ", op)),
                    b.pretty(allocator),
                    allocator.text(")"),
                ])
            },
            Op::Eval(box v) => allocator.concat([
                allocator.text("(eval "),
                v.pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Coef(box v) => allocator.concat([
                allocator.text("(coef "),
                v.pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Check(box v) => allocator.concat([
                allocator.text("(check "),
                v.pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Challenge(t) => allocator.text(format!("challenge<{}>", t)),
            Op::Random(t) => allocator.text(format!("random<{}>", t)),
            Op::Ram(box v, box r) => allocator.concat([
                v.pretty(allocator),
                allocator.text("["),
                r.pretty(allocator),
                allocator.text("]"),
            ]),
            Op::Vec(vs) => allocator.concat([
                allocator.text("["),
                allocator.intersperse(
                vs.into_iter().map(|v| v.pretty(allocator)), ", "),
                allocator.text("]"),
            ]),
            Op::Gen(t) => allocator.text(format!("gen<{}>", t)),
            Op::Not(box v) => allocator.concat([
                allocator.text("!"),
                v.pretty(allocator),
            ]),
            Op::Range(r) => allocator.text(format!("{}", r)),
            Op::Underscore(_, _) => allocator.text(format!("_")),
            Op::Var(v, _, _) => allocator.text(format!("{}", v)),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, C: ArkConfig> fmt::Display for Op<C>{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Op<C> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<C: ArkConfig> From<Value<C>> for Op<C> {
    fn from(v: Value<C>) -> Self {
        Op::Value(v)
    }
}

impl<C: ArkConfig> From<u64> for Op<C> {
    fn from(v: u64) -> Self {
        Op::Value(Value::Index(v))
    }
}

impl<C: ArkConfig> From<usize> for Op<C> {
    fn from(v: usize) -> Self {
        Op::Value(Value::Index(v as u64))
    }
}

impl<C: ArkConfig> From<CRange> for Op<C> {
    fn from(r: CRange) -> Self {
        Op::Range(r)
    }
}

