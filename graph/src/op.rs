use lang::typ::range::CRange;
use lang::ast::BinOp;
use lang::typ::lub::Lub;
use lang::typ::{self, Nothing};
use lang::id::Vid;
use backend::{Value, ABase, ATyp, ArkConfig, ArkGroupOps, ArkScalarOps, ArkPairingOps};

use petgraph::graph::NodeIndex;
use share::{Ctx, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use std::fmt;
use std::ops::{AddAssign, SubAssign, MulAssign, DivAssign, RemAssign, BitXorAssign, BitAndAssign, Add, Sub, Mul, Div, Rem, BitXor, BitAnd};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Ref {
    /// Reference to a node in the graph
    Node(NodeIndex),
    /// Reference to a variable
    Var(Vid, NodeIndex),
}

/// Typed operations are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, Clone, Debug, Ord, PartialOrd)]
pub enum Op<C: ArkConfig, R> {
    /// Value
    Value(Value<C>),

    /// Reference to a node or variable
    Ref(R, ATyp),

    /// Binary operations
    Bin(BinOp, Box<Op<C, R>>, Box<Op<C, R>>, ATyp),

    /// Random access into a value
    Ram(Box<Op<C, R>>, Box<Op<C, R>>),

    /// Vector of values
    Vec(Vec<Op<C, R>>),

    /// Random element
    Random(ATyp, bool),

    /// Billinear pairing
    Pair(Box<Op<C, R>>, Box<Op<C, R>>, ATyp),

    /// Random oracle challenge
    Challenge(ATyp, bool),

    /// Convert from evaluation domain to lagrange domain.
    Coef(Box<Op<C, R>>),

    /// Convert from lagrange domain to evaluation domain
    Eval(Box<Op<C, R>>),

    /// Assertion or verification check
    Check(Box<Op<C, R>>),
}

/// Graph operation
pub type GOp<C> = Op<C, Ref>;

impl Ref {
    pub fn node(&self) -> NodeIndex {
        match self {
            Ref::Node(n) => *n,
            Ref::Var(_, n) => *n,
        }
    }

    pub fn var(&self) -> Option<Vid> {
        match self {
            Ref::Node(_) => None,
            Ref::Var(v, _) => Some(v.clone()),
        }
    }

    pub fn is_var(&self) -> bool {
        self.var().is_some()
    }
}

impl<C: ArkConfig, R> Op<C, R> {
    /// Assign a unique tag to each operation
    pub fn discriminant_order(&self) -> usize {
        match &self {
            Op::Value(_) => 1,
            Op::Ref(_, _) => 2,
            Op::Bin(BinOp::Add, _, _, _) => 3,
            Op::Bin(BinOp::Sub, _, _, _) => 4,
            Op::Bin(BinOp::Mul, _, _, _) => 5,
            Op::Bin(BinOp::Div, _, _, _) => 6,
            Op::Bin(BinOp::Rem, _, _, _) => 7,
            Op::Bin(BinOp::Dot, _, _, _) => 8,
            Op::Bin(BinOp::Concat, _, _, _) => 9,
            Op::Bin(BinOp::Equ, _, _, _) => 10,
            Op::Bin(BinOp::And, _, _, _) => 11,
            Op::Bin(BinOp::Pow, _, _, _) => 12,
            Op::Pair(_, _, _) => 13,
            Op::Ram(_, _) => 14,
            Op::Vec(_) => 15,
            Op::Random(_, _) => 16,
            Op::Challenge(_, _) => 17,
            Op::Coef(_) => 18,
            Op::Eval(_) => 19,
            Op::Check(_) => 20,
        }
    }

    /// Type inference for operations
    pub fn typ(&self) -> ATyp {
        match &self {
            Op::Value(v) => v.typ(),
            Op::Bin(_, _, _, typ) => typ.clone(),
            Op::Pair(_, _, typ) => typ.clone(),
            Op::Ref(_, t) => t.clone(),
            Op::Ram(box l, box r) =>
                match (l.typ(), r.typ()) {
                    (ATyp::Vec(box typ, _), ATyp::Base(_)) => typ,
                    (ATyp::Vec(box typ, _), ATyp::Vec(_, m)) =>
                        ATyp::vec(&typ, m),
                    (a, b) =>
                        panic!("UncaughtError: Ram operand must be a vector, not {} [ {} ]", a, b),
                }
            Op::Vec(vs) => {
                let mut typ = vs[0].typ();
                for v in vs.iter().skip(1) {
                    typ = ATyp::lub_equ(&typ, &v.typ(), &Nothing)
                        .expect(format!("UncaughtError: Vector operands must be of the same type: {} != {}", typ, v.typ()).as_str());
                }
                ATyp::vec(&typ, vs.len())
            }
            Op::Random(t, _) => t.clone(),
            Op::Challenge(t, _) => t.clone(),
            Op::Coef(box op) => op.typ(),
            Op::Eval(box op) => op.typ(),
            Op::Check(box op) => op.typ(),
        }
    }

    pub fn bin(op: BinOp, a: Self, b: Self, typ: ATyp) -> Self where R: Clone {
        match op {
            BinOp::Add => Self::add(a, b, typ),
            BinOp::Sub => Self::sub(a, b, typ),
            BinOp::Mul => Self::mul(a, b, typ),
            BinOp::Div => Self::div(a, b, typ),
            BinOp::Rem => Self::rem(a, b, typ),
            BinOp::Pow => Self::pow(a, b, typ),
            BinOp::Dot => Self::dot(a, b, typ),
            BinOp::Concat => Self::concat(a, b, typ),
            BinOp::Equ => Self::equ(a, b),
            BinOp::And => Self::and(a, b),
        }
    }

    pub fn index(i: usize) -> Self {
        Op::Value(Value::Index(i))
    }

    /// Random access simplifications
    pub fn ram(v: Self, i: Self) -> Self where R: Clone {
        match (v, i) {
            // a[r1][r2] = a[r1.compose(r2)]
            (Op::Ram(box v, box Op::Value(Value::Range(l))), Op::Value(Value::Range(r))) =>
                Op::ram(v, Op::range(l.compose(&r))),
            // a[vi][vi'] = a[vi.compose(vi')]
            (Op::Ram(box v, box Op::Value(Value::VecIndex(vl))), Op::Value(Value::VecIndex(vr))) =>
                Op::ram(v, Op::Value(Value::VecIndex(vr.into_iter()
                    .map(|i| vl[i as usize].clone())
                    .collect::<Vec<_>>()))),
            // a[vi][r] = a[vi.compose(r)]
            (Op::Ram(box v, box Op::Value(Value::VecIndex(vl))), Op::Value(Value::Range(r))) =>
                Op::ram(v, Op::Value(Value::VecIndex(r.into_iter()
                    .map(|i| vl[i as usize].clone())
                    .collect::<Vec<_>>()))),
            // a[r][vi] = a[r.compose(vi)]
            (Op::Ram(box v, box Op::Value(Value::Range(l))), Op::Value(Value::VecIndex(vr))) =>
                Op::ram(v, Op::Value(Value::VecIndex(vr.into_iter()
                    .map(|i| l.compose_index(i))
                    .collect::<Vec<_>>()))),
            // a[r1][i] = a[r1.compose_index(i)]
            (Op::Ram(box v, box Op::Value(Value::Range(r))), Op::Value(Value::Index(i))) =>
                Op::ram(v, r.compose_index(i as usize).into()),
            (Op::Ram(box v, box Op::Value(Value::VecIndex(vs))), Op::Value(Value::Index(i))) =>
                Op::ram(v, Op::Value(Value::Index(vs[i].clone()))),
            // [e0, e1, ..., en][i] = e_i
            (Op::Vec(vs), Op::Value(Value::Index(i))) => vs[i as usize].clone(),
            // [e0, e1, ..., en][r] = [e_i for i in r]
            (Op::Vec(vs), Op::Value(Value::Range(r))) =>
                Op::vec(r.into_iter().map(|i| vs[i].clone()).collect::<Vec<_>>()),
            (Op::Vec(vs), Op::Value(Value::VecIndex(vr))) =>
                Op::vec(vr.into_iter()
                    .map(|i| vs[i as usize].clone())
                    .collect::<Vec<_>>()),
            // v[v2]
            (Op::Value(a), Op::Value(b)) => Op::Value(Value::ram(a, b)),
            // Default constructor
            (v, i) => Op::Ram(Box::new(v), Box::new(i)),
        }
    }

    /// Concatenation simplifications
    pub fn concat(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // [e0, e1, ..., en] + [e_n+1, e_n+2, ..., e_m] = [e0, e1, ..., e_m]
            (Op::Vec(mut vs1), Op::Vec(vs2)) => {
                vs1.extend(vs2);
                Op::Vec(vs1)
            },
            // [e0, e1, ..., en] + e = [e0, e1, ..., e_n, e]
            (Op::Vec(mut vs), v) | (v, Op::Vec(mut vs)) => {
                let (t, _) = typ.clone().into_vec();
                if v.typ() == t {
                    vs.push(v);
                    Op::Vec(vs)
                } else {
                    Op::Bin(BinOp::Concat, Box::new(v), Box::new(Op::Vec(vs)), typ)
                }
            },
            // v1 + v2 = v1.concat(v2)
            (Op::Value(a), Op::Value(mut b)) => {
                Value::concat(a, &mut b);
                Op::Value(b)
            }
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Concat, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn add(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v + 0 = 0 + v = v
            (Op::Value(a), Op::Value(b)) if a.is_zero() => Op::Value(b),
            (Op::Value(a), Op::Value(b)) if b.is_zero() => Op::Value(a),
            // v1 + v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a + b),
            // e + v = v + e
            (Op::Vec(l), Op::Value(mut v))
            | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                Op::vec(v.into_vec_mut().into_iter()
                    .zip(l.into_iter())
                    .map(|(v, l)| Op::add(v.clone().into(), l.into(), t.clone()))
                    .collect())
            },

            // [e0, e1, ... en] + [e0', e1', ... em'] = [e0 + e0', e1 + e1', ... en + em']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)|
                        Op::add(l, r, t.clone()))
                    .collect())
            },
            // Commuting conversion (eval a + eval b) = eval (a + b)
            (Op::Eval(box l), Op::Eval(box r)) =>
                Op::Eval(Box::new(Op::add(l, r, typ))),
            // Commuting conversion (coef a + coef b) = coef (a + b)
            (Op::Coef(box l), Op::Coef(box r)) =>
                Op::Coef(Box::new(Op::add(l, r, typ))),
            (v1, v2) => Op::Bin(BinOp::Add, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn sub(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v - 0
            (Op::Value(a), Op::Value(b)) if b.is_zero() => Op::Value(a),
            // v1 - v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a - b),
            // e - v = v - e
            (Op::Vec(l), Op::Value(mut v))
            | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                Op::vec(v.into_vec_mut().into_iter()
                    .zip(l.into_iter())
                    .map(|(v, l)| Op::sub(v.clone().into(), l.into(), t.clone()))
                    .collect())
            },

            // [e0, e1, ... en] - [e0', e1', ... em'] = [e0 - e0', e1 - e1', ... en - em']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)|
                        Op::sub(l, r, t.clone()))
                    .collect())
            },
            // Commuting conversion (eval a - eval b) = eval (a - b)
            (Op::Eval(box l), Op::Eval(box r)) =>
                Op::Eval(Box::new(Op::sub(l, r, typ))),
            // Commuting conversion (coef a - coef b) = coef (a - b)
            (Op::Coef(box l), Op::Coef(box r)) =>
                Op::Coef(Box::new(Op::sub(l, r, typ))),
            (v1, v2) => Op::Bin(BinOp::Add, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn mul(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // 0 * v = v * 0 = 0
            (Op::Value(a), _) | (_, Op::Value(a)) if a.is_zero() => Op::zero(&typ),
            // 1 * v = v * 1 = v
            (Op::Value(a), b) | (b, Op::Value(a)) if a.is_one() => b,
            // v1 * v2 = v1.mul(v2)
            (Op::Value(a), Op::Value(b)) => Op::Value(a * b),
            // [e0, ..., en] * v = [e0 * v0, e1 * v1, ..., en * vn]
            (Op::Vec(l), Op::Value(mut v))
            | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    Op::vec(v.into_vec_mut().into_iter()
                        .zip(l.into_iter())
                        .map(|(v, l)| Op::mul(v.clone().into(), l.into(), t.clone()))
                        .collect())
                } else {
                    Op::vec(l.into_iter()
                        .map(|l| Op::mul(v.clone().into(), l.into(), t.clone())).collect())
                }
            },
            // [e0, e1, ... en] * [e0', e1', ... en'] = [e0 * e0', e1 * e1', ... en * en']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)|
                        Op::mul(l, r, t.clone()))
                    .collect())
            },
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Mul, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn div(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (_, Op::Value(b)) if b.is_zero() => panic!("UncaughtError: Division by zero"),
            (Op::Value(a), _) if a.is_zero() => Op::zero(&typ),
            (a, Op::Value(b)) if b.is_one() => a,
            // v1 / v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a / b),
            // [e0, ..., en] / v = [e0 / v0, e1 / v1, ..., en / vn]
            (Op::Vec(l), Op::Value(mut v))
            | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    Op::vec(v.into_vec_mut().into_iter()
                        .zip(l.into_iter())
                        .map(|(v, l)| Op::div(v.clone().into(), l.into(), t.clone()))
                        .collect())
                } else {
                    Op::vec(l.into_iter()
                        .map(|l| Op::div(v.clone().into(), l.into(), t.clone())).collect())
                }
            },
            // [e0, e1, ... en] / [e0', e1', ... en'] = [e0 / e0', e1 / e1', ... en / en']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)|
                        Op::div(l, r, t.clone()))
                    .collect())
            },
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Div, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn pair(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(mut b)) => {
                a.value_pair(&mut b);
                Op::Value(b)
            },
            (v1, v2) => Op::Pair(Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn rem(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v1 % v2
            (Op::Value(a), Op::Value(b)) => Op::Value(a % b),
            // [e0, ..., en] % v = [e0 % v0, e1 % v1, ..., en % vn]
            (Op::Vec(l), Op::Value(mut v))
            | (Op::Value(mut v), Op::Vec(l)) => {
                let (t, _) = typ.clone().into_vec();
                if v.is_vec() {
                    Op::vec(v.into_vec_mut().into_iter()
                        .zip(l.into_iter())
                        .map(|(v, l)| Op::rem(v.clone().into(), l.into(), t.clone()))
                        .collect())
                } else {
                    Op::vec(l.into_iter()
                        .map(|l| Op::rem(v.clone().into(), l.into(), t.clone())).collect())
                }
            },
            // [e0, e1, ... en] % [e0', e1', ... en'] = [e0 % e0', e1 % e1', ... en % en']
            (Op::Vec(l), Op::Vec(r)) => {
                let (t, _) = typ.into_vec();
                Op::Vec(l.into_iter().zip(r.into_iter())
                    .map(|(l, r)|
                        Op::rem(l, r, t.clone()))
                    .collect())
            },
            // Default constructor
            (v1, v2) => Op::Bin(BinOp::Rem, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn one(typ: &ATyp) -> Op<C, R> {
        match typ {
            ATyp::Base(ABase::Fin(r)) if r.contains(1) => Op::Value(Value::Index(1)),
            ATyp::Base(ABase::Scalar) => Op::Value(Value::Scalar(C::FOps::one())),
            ATyp::Vec(box ATyp::Base(ABase::Scalar), n) =>
                Op::Value(Value::VecScalar(vec![C::FOps::one(); *n])),
            ATyp::Vec(box ATyp::Base(ABase::Fin(r)), n) if r.contains(1) =>
                Op::Value(Value::VecIndex(vec![1; *n])),
            ATyp::Vec(box typ, n) => {
                let mut vs = vec![];
                for _ in 0..*n {
                    vs.push(Op::one(typ));
                }
                Op::Vec(vs)
            },
            ATyp::Uni(n) if *n > 0 => {
                let mut vs = vec![0; *n];
                vs[0] = 1;
                Op::Value(Value::VecIndex(vs))
            },
            _ => unreachable!("UncaughtError: Op::one() not implemented for type {}", typ),
        }
    }

    pub fn pow(v1: Self, v2: Self, typ: ATyp) -> Self where R: Clone {
        match v2 {
            Op::Value(Value::Index(i)) if i == 0 => Op::one(&typ),
            Op::Value(Value::Index(i)) if i == 1 => v1,
            v2 => Op::Bin(BinOp::Pow, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn dot(v1: Self, v2: Self, typ: ATyp) -> Self {
        match (v1, v2) {
            // v1 . v2 = v1.dot(v2)
            (Op::Value(a), Op::Value(b)) => {
                let mut b= b;
                Value::value_dot(&a, &mut b);
                Op::Value(b)
            },
            // Default case, constructor
            (v1, v2) => Op::Bin(BinOp::Dot, Box::new(v1), Box::new(v2), typ),
        }
    }

    pub fn coef(op: Self) -> Op<C, R> {
        match op {
            Op::Eval(box op) => op,
            _ => Op::Coef(Box::new(op)),
        }
    }

    pub fn eval(op: Self) -> Op<C, R> {
        match op {
            Op::Coef(box op) => op,
            op => Op::Eval(Box::new(op)),
        }
    }

    pub fn range(r: CRange) -> Op<C, R> {
        Op::Value(Value::VecIndex(r.into_iter().collect()));
    }
    pub fn zero(typ: &ATyp) -> Op<C, R> {
        Op::Value(Value::zero(typ))
    }

    pub fn pad_zeroes(v: Op<C, R>, n: usize) -> Op<C, R> where R: Clone {
        let typ = v.typ();
        let (t, m) = typ.into_vec();
        if m < n {
            Op::concat(v, Op::vec(vec![Op::zero(&t); n - m]), ATyp::vec(&t, n))
        } else {
            v
        }
    }

    pub fn equ(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Value(a), Op::Value(b)) => Op::Value(a.value_equ(&b)),
            (v1, v2) => Op::Bin(BinOp::Equ, Box::new(v1), Box::new(v2), ATyp::bool()),
        }
    }

    pub fn and(v1: Self, v2: Self) -> Self {
        match (v1, v2) {
            (Op::Value(Value::Bool(false)), _)
            | (_, Op::Value(Value::Bool(false))) => Op::bfalse(),
            (Op::Value(a), Op::Value(b)) => Op::Value(a & b),
            (v1, v2) => Op::Bin(BinOp::And, Box::new(v1), Box::new(v2), ATyp::bool()),
        }
    }

    pub fn btrue() -> Self {
        Op::Value(Value::Bool(true))
    }
    pub fn bfalse() -> Self {
        Op::Value(Value::Bool(false))
    }

    pub fn vec(vs: Vec<Op<C, R>>) -> Op<C, R> {
        Op::Vec(vs)
    }

    pub fn reference(r: R, typ: ATyp) -> Op<C, R> {
        Op::Ref(r, typ)
    }

    pub fn challenge(typ: ATyp) -> Op<C, R> {
        Op::Challenge(typ, false)
    }
    pub fn random(typ: ATyp) -> Op<C, R> {
        Op::Random(typ, false)
    }
    pub fn challenge_nz(typ: ATyp) -> Op<C, R> {
        Op::Challenge(typ, true)
    }
    pub fn random_nz(typ: ATyp) -> Op<C, R> {
        Op::Random(typ, true)
    }

    pub fn check(op: Op<C, R>) -> Op<C, R> {
        Op::Check(Box::new(op))
    }

    pub fn references(&self) -> Vec<R> where R: Clone {
        match self {
            Op::Ref(n, _) => vec![n.clone()],
            Op::Bin(_, box a, box b, _)
            | Op::Pair(box a, box b, _)
            | Op::Ram(box a, box b) =>
                a.references().into_iter()
                    .chain(b.references().into_iter())
                    .collect(),
            Op::Vec(vs) =>
                vs.into_iter()
                    .flat_map(|v| v.references())
                    .collect(),
            Op::Coef(box v)
            | Op::Check(box v)
            | Op::Eval(box v) => v.references(),
            Op::Value(_)
            | Op::Random(_, _)
            | Op::Challenge(_, _) => vec![],
        }
    }
}

impl<C: ArkConfig> GOp<C> {
    pub fn underscore(n: NodeIndex, typ: ATyp) -> Self {
        Op::Ref(Ref::Node(n), typ)
    }

    pub fn var(v: &Vid, n: NodeIndex, typ: ATyp) -> Self {
        Op::Ref(Ref::Var(v.clone(), n), typ)
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Op::Ref(Ref::Var(_, _), _))
    }

    pub fn is_underscore(&self) -> bool {
        matches!(self, Op::Ref(Ref::Node(_), _))
    }

    pub fn map_node_indices<F: Fn(NodeIndex) -> NodeIndex>(&self, f: &F) -> GOp<C> {
        match self {
            Op::Ref(Ref::Node(n), typ) => Op::Ref(Ref::Node(f(*n)), typ.clone()),
            Op::Ref(Ref::Var(v, n), typ) => Op::Ref(Ref::Var(v.clone(), f(*n)), typ.clone()),
            Op::Bin(op, box a, box b, typ) =>
                Op::Bin(*op, Box::new(a.map_node_indices(f)), Box::new(b.map_node_indices(f)), typ.clone()),
            Op::Ram(box a, box b) =>
                Op::Ram(Box::new(a.map_node_indices(f)), Box::new(b.map_node_indices(f))),
            Op::Vec(vs) => Op::Vec(vs.into_iter().map(|v| v.map_node_indices(f)).collect()),
            Op::Pair(box a, box b, typ) =>
                Op::Pair(Box::new(a.map_node_indices(f)), Box::new(b.map_node_indices(f)), typ.clone()),
            Op::Check(box op) => Op::Check(Box::new(op.map_node_indices(f))),
            Op::Coef(box op) => Op::Coef(Box::new(op.map_node_indices(f))),
            Op::Eval(box op) => Op::Eval(Box::new(op.map_node_indices(f))),
            _ => self.clone()
        }
    }

    pub fn map_refs<F: Fn(Ref) -> Ref>(&self, f: &F) -> GOp<C> {
        match self {
            Op::Ref(r, typ) => Op::Ref(f(r.clone()), typ.clone()),
            Op::Bin(op, box a, box b, typ) =>
                Op::Bin(*op, Box::new(a.map_refs(f)), Box::new(b.map_refs(f)), typ.clone()),
            Op::Ram(box a, box b) =>
                Op::Ram(Box::new(a.map_refs(f)), Box::new(b.map_refs(f))),
            Op::Vec(vs) => Op::Vec(vs.into_iter().map(|v| v.map_refs(f)).collect()),
            Op::Pair(box a, box b, typ) =>
                Op::Pair(Box::new(a.map_refs(f)), Box::new(b.map_refs(f)), typ.clone()),
            Op::Check(box op) => Op::Check(Box::new(op.map_refs(f))),
            Op::Coef(box op) => Op::Coef(Box::new(op.map_refs(f))),
            Op::Eval(box op) => Op::Eval(Box::new(op.map_refs(f))),
            Op::Value(_)
            | Op::Random(_, _)
            | Op::Challenge(_, _) => self.clone(),
        }
    }

    /// Inline an operation, except for the nodes specified
    /// which remain as node identifiers.
    pub fn inline<F: Fn(&Ref, &GOp<C>)->bool>(&self, vars: &Ctx<Ref, GOp<C>>, except: &F) -> GOp<C> {
        match self {
            Op::Ref(r, _) =>
                if let Some(next) = vars.get(&r) {
                    if except(r, next) {
                        return self.clone();
                    }
                    next.inline(vars, except)
                } else {
                    self.clone()
                },
            Op::Bin(op, box a, box b, typ) => {
                let oa = a.inline(vars, except);
                let ob = b.inline(vars, except);
                Op::bin(*op, oa, ob, typ.clone())
            },
            Op::Ram(box a, box b) => {
                let oa = a.inline(vars, except);
                let ob = b.inline(vars, except);
                Op::Ram(Box::new(oa), Box::new(ob))
            },
            Op::Vec(vs) =>
                Op::Vec(vs.into_iter().map(|v| v.inline(vars, except))
                    .collect::<Vec<_>>()),
            Op::Check(box op) => op.inline(vars, except),
            Op::Coef(box v) => Op::Coef(Box::new(v.inline(vars, except))),
            Op::Eval(box v) => Op::Eval(Box::new(v.inline(vars, except))),
            _ => self.clone()
        }
    }


}

/// Pretty-printer for Operations
impl<'a, D, A> Pretty<'a, D, A> for Ref
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Ref::Node(n) => allocator.text(format!("n{}", n.index())),
            Ref::Var(v, _) => allocator.text(format!("{}", v)),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Ref as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl From<NodeIndex> for Ref {
    fn from(n: NodeIndex) -> Self {
        Ref::Node(n)
    }
}

impl<'a> From<&'a Vid> for Ref {
    fn from(v: &'a Vid) -> Self {
        Ref::Var(v.clone(), NodeIndex::new(0))
    }
}

impl<'a> From<&'a str> for Ref {
    fn from(v: &'a str) -> Self {
        Ref::Var(Vid::from(v), NodeIndex::new(0))
    }
}

impl<C: ArkConfig, R: Clone> AddAssign<Op<C, R>> for Op<C, R> {
    fn add_assign(&mut self, other: Op<C, R>) {
        *self = Op::add(self.clone(), other, self.typ());
    }
}

impl<C: ArkConfig, R: Clone> SubAssign<Op<C, R>> for Op<C, R> {
    fn sub_assign(&mut self, other: Op<C, R>) {
        *self = Op::sub(self.clone(), other, self.typ());
    }
}

impl<C: ArkConfig, R: Clone> MulAssign<Op<C, R>> for Op<C, R> {
    fn mul_assign(&mut self, other: Op<C, R>) {
        *self = Op::mul(self.clone(), other, self.typ());
    }
}

impl<C: ArkConfig, R: Clone> DivAssign<Op<C, R>> for Op<C, R> {
    fn div_assign(&mut self, other: Op<C, R>) {
        *self = Op::div(self.clone(), other, self.typ());
    }
}

impl<C: ArkConfig, R: Clone> RemAssign<Op<C, R>> for Op<C, R> {
    fn rem_assign(&mut self, other: Op<C, R>) {
        *self = Op::rem(self.clone(), other, self.typ());
    }
}

impl<C: ArkConfig, R: Clone> BitXorAssign<Op<C, R>> for Op<C, R> {
    fn bitxor_assign(&mut self, other: Op<C, R>) {
        *self = Op::pow(self.clone(), other, self.typ());
    }
}

impl<C: ArkConfig, R: Clone> BitAndAssign<Op<C, R>> for Op<C, R> {
    fn bitand_assign(&mut self, other: Op<C, R>) {
        *self = Op::and(self.clone(),other);
    }
}

impl<C: ArkConfig, R: Clone> Add for Op<C, R> {
    type Output = Op<C, R>;

    fn add(self, other: Op<C, R>) -> Op<C, R> {
        let typ = self.typ().clone();
        Op::add(self, other, typ)
    }
}

impl<C: ArkConfig, R: Clone> Sub for Op<C, R> {
    type Output = Op<C, R>;

    fn sub(self, other: Op<C, R>) -> Op<C, R> {
        let typ = self.typ().clone();
        Op::sub(self, other, typ)
    }
}

impl<C: ArkConfig, R: Clone> Mul for Op<C, R> {
    type Output = Op<C, R>;

    fn mul(self, other: Op<C, R>) -> Op<C, R> {
        let typ = self.typ().clone();
        Op::mul(self, other, typ)
    }
}

impl<C: ArkConfig, R: Clone> Div for Op<C, R> {
    type Output = Op<C, R>;

    fn div(self, other: Op<C, R>) -> Op<C, R> {
        let typ = self.typ().clone();
        Op::div(self, other, typ)
    }
}

impl<C: ArkConfig, R: Clone> Rem for Op<C, R> {
    type Output = Op<C, R>;

    fn rem(self, other: Op<C, R>) -> Op<C, R> {
        let typ = self.typ().clone();
        Op::rem(self, other, typ)
    }
}

impl<C: ArkConfig, R: Clone> BitXor for Op<C, R> {
    type Output = Op<C, R>;

    fn bitxor(self, other: Op<C, R>) -> Op<C, R> {
        let typ = self.typ().clone();
        Op::pow(self, other, typ)
    }
}

impl<C: ArkConfig, R: Clone> BitAnd for Op<C, R> {
    type Output = Op<C, R>;

    fn bitand(self, other: Op<C, R>) -> Op<C, R> {
        Op::and(self, other)
    }
}

/// Pretty-printer for Operations
impl<'a, D, C, A, R> Pretty<'a, D, A> for Op<C, R>
where
    D: DocAllocator<'a, A>,
    C: ArkConfig,
    R: Pretty<'a, D, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Op::Value(v) => allocator.text(format!("{}", v)),
            Op::Bin(op, box a, box b, _) => {
                match (&a, &b) {
                    // If either operand is itself a binary op with lower precedence,
                    // we need parens around that operand
                    (Op::Bin(op1, _, _, _), _) if op1.precedence() < op.precedence() => {
                        allocator.concat(vec![
                            allocator.text("("),
                            a.pretty(allocator),
                            allocator.text(")"),
                            allocator.text(format!("{}", op)),
                            b.pretty(allocator),
                        ])
                    },
                    (_, Op::Bin(op2, _, _, _)) if op2.precedence() < op.precedence() => {
                        allocator.concat(vec![
                            a.pretty(allocator),
                            allocator.text(format!("{}", op)),
                            allocator.text("("),
                            b.pretty(allocator),
                            allocator.text(")"),
                        ])
                    },
                    // No parens needed
                    _ => allocator.concat(vec![
                        a.pretty(allocator),
                        allocator.text(format!("{}", op)),
                        b.pretty(allocator),
                    ])
                }
            },
            Op::Eval(box v) => allocator.concat([
                allocator.text("(eval "),
                v.pretty(allocator),
                allocator.text(")"),
            ]),
            Op::Pair(box a, box b, _) => allocator.concat([
                allocator.text("(pair "),
                a.pretty(allocator),
                allocator.text(", "),
                b.pretty(allocator),
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
            Op::Challenge(t, true) => allocator.text(format!("challenge<{}*>", t)),
            Op::Random(t, true) => allocator.text(format!("random<{}*>", t)),
            Op::Challenge(t, false) => allocator.text(format!("challenge<{}>", t)),
            Op::Random(t, false) => allocator.text(format!("random<{}>", t)),
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
            Op::Ref(n, _) => n.pretty(allocator),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, C: ArkConfig, R: Pretty<'a, BoxAllocator, ()> + Clone> fmt::Display for Op<C, R>{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Op<C, R> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<C: ArkConfig, R> From<Value<C>> for Op<C, R> {
    fn from(v: Value<C>) -> Self {
        Op::Value(v)
    }
}

impl<C: ArkConfig, R> From<usize> for Op<C, R> {
    fn from(v: usize) -> Self {
        Op::Value(Value::Index(v))
    }
}

impl<C: ArkConfig, R> From<CRange> for Op<C, R> {
    fn from(r: CRange) -> Self {
        Op::Value(Value::Range(r))
    }
}
