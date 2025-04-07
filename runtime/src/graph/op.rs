use lang::typ::range::CRange;
use std::fmt;
use petgraph::graph::NodeIndex;
use lang::ast::BinOp;

use crate::RTyp;

/// Operands are expressions which are not important
/// enough to be nodes in the graph.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Operand {
    /// Value
    Lit(usize),
    /// Binary operation
    Bin(BinOp, Box<Operand>, Box<Operand>),
    /// Boolean not
    Not(Box<Operand>),
    /// Generator for a group
    Gen,
    /// Random element
    Rand,
    /// Node input
    Underscore(NodeIndex),
    /// Range of numbers
    Range(CRange),
    /// Random access into a value
    Ram(Box<Operand>, Box<Operand>),
    /// Vector of values
    Vec(Vec<Operand>),
}

/// Typed operands
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct TOperand {
    typ: RTyp,
    operand: Operand,
}

/// An operation [Op] is loosely a node in the graph,
/// and it corresponds to one [lang::ast::Exp] in the AST.
/// It is parameterized by tye type of operands [V] and the type of types [T].
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Op<T> {
    /// Binary operation
    Bin(BinOp, T, T),

    /// Random oracle challenge
    Challenge(RTyp),

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

pub type TOp = Op<TOperand>;

impl TOperand {
    pub fn new(typ: RTyp, operand: Operand) -> TOperand {
        TOperand { typ, operand }
    }

    pub fn typ(&self) -> &RTyp {
        &self.typ
    }

    pub fn operand(&self) -> &Operand {
        &self.operand
    }
}

/// Smart constructors to simplify operands a bit
impl Operand {
    pub fn ram(v: Operand, i: Operand) -> Operand {
        match (v, i) {
            (Operand::Ram(box v, box Operand::Range(l)), Operand::Range(r)) =>
                Operand::ram(v, Operand::range(l.compose(&r))),
            (Operand::Ram(box v, box Operand::Range(r)), Operand::Lit(i)) =>
                Operand::ram(v, Operand::lit(r.compose_index(i))),
            (Operand::Vec(vs), Operand::Lit(i)) => vs[i].clone(),
            (Operand::Vec(vs), Operand::Range(r)) =>
                Operand::Vec(r.into_iter().map(|i| vs[i].clone()).collect::<Vec<_>>()),
            (Operand::Range(r), Operand::Lit(i)) => Operand::Lit(r.start + i* r.step),
            (v, i) => Operand::Ram(Box::new(v), Box::new(i)),
        }
    }

    pub fn concat(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Vec(mut vs1), Operand::Vec(vs2)) => {
                vs1.extend(vs2);
                Operand::Vec(vs1)
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.push(v);
                Operand::Vec(vs)
            },
            (l, r) => Operand::Bin(BinOp::Concat, Box::new(l), Box::new(r)),
        }
    }

    pub fn add(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l + r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l + CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::add(l, r)).collect()),
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Add, Box::new(l), Box::new(r)),
        }
    }

    pub fn sub(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l - r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l - CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::sub(l, r)).collect()),
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Add, Box::new(l), Box::new(r)),
        }
    }

    pub fn mul(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l * r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l * CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::mul(l, r)).collect()),
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Mul, Box::new(l), Box::new(r)),
        }
    }

    pub fn div(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l / r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l / CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::div(l, r)).collect()),
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Div, Box::new(l), Box::new(r)),
        }
    }

    pub fn pow(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l ^ r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l ^ CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::pow(l, r)).collect()),
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Pow, Box::new(l), Box::new(r)),
        }
    }

    pub fn dot(v1: Operand, v2: Operand) -> Operand {
        match (v1, v2) {
            (Operand::Range(l), Operand::Range(r)) => Operand::lit((l * r).into_iter().sum()),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l * CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::dot(l, r)).collect()),
            // Default case, constructor
            (l, r) =>
                Operand::Bin(BinOp::Dot, Box::new(l), Box::new(r)),
        }
    }

    pub fn not(v: Operand) -> Operand {
        match v {
            Operand::Not(box v) => v,
            _ => Operand::Not(Box::new(v)),
        }
    }
    pub fn vec(vs: Vec<Operand>) -> Operand {
        Operand::Vec(vs)
    }
    pub fn underscore(n: &NodeIndex) -> Operand {
        Operand::Underscore(*n)
    }
    pub fn lit(n: usize) -> Operand {
        Operand::Lit(n)
    }
    pub fn range(r: CRange) -> Operand {
        Operand::Range(r)
    }
    pub fn nodes(&self) -> Vec<NodeIndex> {
        match self {
            Operand::Underscore(n) => vec![*n],
            Operand::Ram(box v, _) => v.nodes(),
            Operand::Vec(vs) => {
                let mut res = Vec::new();
                for v in vs.iter() {
                    res.extend(v.nodes());
                }
                res
            },
            Operand::Bin(_, l, r) => {
                let mut res = l.nodes();
                res.extend(r.nodes());
                res
            },
            _ => vec![],
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operand::Lit(x) => write!(f, "{}", x),
            Operand::Ram(box v, r) => write!(f, "{}[{}]", v, r),
            Operand::Vec(vs) => {
                write!(f, "[")?;
                for v in vs.iter() {
                    write!(f, "{}, ", v)?;
                }
                write!(f, "]")
            },
            Operand::Gen => write!(f, "gen()"),
            Operand::Rand => write!(f, "rand()"),
            Operand::Not(v) => write!(f, "!{}", v),
            Operand::Bin(op, l, r) => write!(f, "({} {} {})", l, op, r),
            Operand::Range(r) => write!(f, "{}", r),
            Operand::Underscore(n) => write!(f, "_{}", n.index()),
        }
    }
}

impl fmt::Display for TOperand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} : {}", self.operand, self.typ)
    }
}

impl From<usize> for Operand {
    fn from(v: usize) -> Self {
        Operand::Lit(v)
    }
}

impl From<CRange> for Operand {
    fn from(r: CRange) -> Self {
        Operand::Range(r)
    }
}

impl From<NodeIndex> for Operand {
    fn from(n: NodeIndex) -> Self {
        Operand::Underscore(n)
    }
}

impl TOp {
    pub fn bin(op: BinOp, a: TOperand, b: TOperand) -> TOp {
        Op::Bin(op, a, b)
    }

    pub fn eval(a: TOperand) -> TOp {
        Op::Eval(a)
    }

    pub fn coef(a: TOperand) -> TOp {
        Op::Coef(a)
    }

    pub fn hash(a: TOperand) -> TOp {
        Op::Hash(a)
    }

    pub fn contains(a: TOperand, b: TOperand) -> TOp {
        Op::Contains(a, b)
    }

    pub fn challenge(t: RTyp) -> TOp {
        Op::Challenge(t)
    }

    pub fn check(a: TOperand) -> TOp {
        Op::Check(a)
    }
}

impl<T: fmt::Display> fmt::Display for Op<T> {
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
