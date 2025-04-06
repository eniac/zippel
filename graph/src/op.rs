use lang::typ::range::CRange;
use lang::id::Vid;
use lang::ast::FreeVars;
use lang::ast::BinOp;
use std::fmt;
use petgraph::graph::NodeIndex;
use lang::id::Tid;

use runtime::RTyp;
use share::Set;

/// Operands are expressions which are not important
/// enough to be nodes in the graph.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Operand<T> {
    /// Numeric literal
    Lit(usize),
    /// Binary operation
    Bin(BinOp, Box<Operand<T>>, Box<Operand<T>>),
    /// Boolean not
    Not(Box<Operand<T>>),
    /// Generator for a group
    Gen(T),
    /// Random element
    Rand(T),
    /// Vanishing polynomial
    Vanishing(Box<Operand<T>>),
    /// Node input
    Underscore(NodeIndex),
    /// Coefficients of a univariate vector
    Coef(Box<Operand<T>>),
    /// Multilinear extension of a 2^N vector of coefficients
    Mle(Box<Operand<T>>),
    /// Range of numbers
    Range(CRange),
    /// Random access into a value
    Ram(Box<Operand<T>>, Box<Operand<T>>),
    /// Vector of values
    Vec(Vec<Operand<T>>),
}

/// An operation [Op] is loosely a node in the graph,
/// and it corresponds to one [lang::ast::Exp] in the AST.
/// It is parameterized by tye type of operands [V] and the type of types [T].
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Op<T, V> {
    /// Binary operation
    Bin(BinOp, V, V),

    /// Random oracle challenge
    Challenge(T),

    /// Random oracle challenge as a hash
    Hash(T),

    /// Convert from evaluation domain to lagrange domain.
    Ifft(V),

    /// Convert from lagrange domain to evaluation domain
    Fft(V),

    /// Equality check
    Equ(V, V),

    /// Vector containment check
    Contains(V, V),

    /// Assertion or verification check
    Check(V)
}

/// A typed, operation is a computation on values
pub type Operation = Op<RTyp, (Operand<RTyp>, RTyp)>;

/// Smart constructors to simplify operands a bit
impl<T> Operand<T> {
    pub fn ram(v: Operand<T>, i: Operand<T>) -> Operand<T> {
        match (v, i) {
            (Operand::Ram(box v, box Operand::Range(l)), Operand::Range(r)) =>
                Operand::ram(v, Operand::range(l.compose(&r))),
            (Operand::Ram(box v, box Operand::Range(r)), Operand::Lit(i)) =>
                Operand::ram(v, Operand::lit(r.compose_index(i))),
            (Operand::Vec(vs), Operand::Lit(i)) => vs[i],
            (Operand::Vec(vs), Operand::Range(r)) =>
                Operand::Vec(r.iter().map(|i| vs[*i]).collect::<Vec<_>>()),
            (Operand::Range(r), Operand::Lit(i)) => Operand::Lit(r.start + i* r.step),
            (v, i) => Operand::Ram(Box::new(v), Box::new(i)),
        }
    }

    pub fn concat(v1: Operand<T>, v2: Operand<T>) -> Operand<T> {
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

    pub fn add(v1: Operand<T>, v2: Operand<T>) -> Operand<T> {
        match (v1, v2) {
            (Operand::Lit(l), Operand::Lit(r)) => Operand::Lit(l + r),
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l + r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l + CRange::singleton(r)),
            (Operand::Vec(l), Operand::Vec(r)) =>
                Operand::Vec(l.into_iter().zip(r.into_iter()).map(|(l, r)| Operand::add(l, r)).collect()),
            (Operand::Vec(vs), v) | (v, Operand::Vec(vs)) =>
                Operand::Vec(vs.into_iter().map(|l| Operand::add(l, v.clone())).collect()),
            (Operand::Coef(l), Operand::Coef(r)) => Operand::coef(Operand::add(*l, *r)),
            (Operand::Mle(l), Operand::Mle(r)) => Operand::mle(Operand::add(*l, *r)),

            (l, r) =>
                Operand::Bin(BinOp::Add, Box::new(l), Box::new(r)),
        }
    }

    pub fn sub(v1: Operand<T>, v2: Operand<T>) -> Operand<T> {
        match (v1, v2) {
            (Operand::Vec(l), Operand::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Operand::sub(l.clone(), r.clone()));
                }
                Operand::Vec(res)
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Operand::sub(l.clone(), v.clone()));
                Operand::Vec(vs)
            },
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l - r),
            (Operand::Range(l), Operand::Lit(r)) => Operand::Range(l - CRange::singleton(r)),
            (Operand::Lit(l), Operand::Range(r)) => Operand::Range(CRange::singleton(l) - r),
            (l, r) =>
                Operand::Bin(BinOp::Sub, Box::new(l), Box::new(r)),
        }
    }

    pub fn mul(v1: Operand, v2: Operand<T>) -> Operand<T> {
        match (v1, v2) {
            (Operand::Vec(l), Operand::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Operand::mul(l.clone(), r.clone()));
                }
                Operand::Vec(res)
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Operand::mul(l.clone(), v.clone()));
                Operand::Vec(vs)
            },
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l * r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l * CRange::singleton(r)),
            (l, r) =>
                Operand::Bin(BinOp::Mul, Box::new(l), Box::new(r)),
        }
    }

    pub fn div(v1: Operand<T>, v2: Operand<T>) -> Operand<T> {
        match (v1, v2) {
            (Operand::Vec(l), Operand::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Operand::div(l.clone(), r.clone()));
                }
                Operand::Vec(res)
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Operand::div(l.clone(), v.clone()));
                Operand::Vec(vs)
            },
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l / r),
            (Operand::Range(l), Operand::Lit(r)) => Operand::Range(l / CRange::singleton(r)),
            (Operand::Lit(l), Operand::Range(r)) => Operand::Range(CRange::singleton(l) / r),
            (l, r) =>
                Operand::Bin(BinOp::Div, Box::new(l), Box::new(r)),
        }
    }

    pub fn dot(v1: Operand<T>, v2: Operand<T>) -> Operand<T> {
        match (v1, v2) {
            (Operand::Vec(vs1), Operand::Vec(vs2)) => {
                let mut res = Vec::new();
                for (l, r) in vs1.iter().zip(vs2.iter()) {
                    res.push(Operand::mul(l.clone(), r.clone()));
                }
                match res.as_slice() {
                    [] => Operand::Vec(vec![]),
                    [v] => v.clone(),
                    [h, ts @ ..] =>
                        ts.into_iter().fold(h.clone(), |acc, v| Operand::add(acc, v.clone())),
                }
            },
            (Operand::Vec(mut vs), v) | (v, Operand::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Operand::mul(l.clone(), v.clone()));
                Operand::Vec(vs)
            },
            (Operand::Range(l), Operand::Range(r)) => Operand::Range(l * r),
            (Operand::Range(l), Operand::Lit(r)) | (Operand::Lit(r), Operand::Range(l)) =>
                Operand::Range(l * CRange::singleton(r)),
            (l, r) =>
                Operand::Bin(BinOp::Dot, Box::new(l), Box::new(r)),
        }
    }

    pub fn vec(vs: Vec<Operand<T>>) -> Operand<T> {
        Operand::Vec(vs)
    }
    pub fn underscore(n: NodeIndex) -> Operand {
        Operand::Underscore(n)
    }
    pub fn lit(n: usize) -> Operand {
        Operand::Lit(n)
    }
    pub fn range(r: CRange) -> Operand {
        Operand::Range(r)
    }
    pub fn coef(v: Operand) -> Operand {
        Operand::Coef(Box::new(v))
    }
    pub fn mle(v: Operand) -> Operand {
        Operand::Mle(Box::new(v))
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
            Operand::Coef(v) => v.nodes(),
            Operand::Mle(v) => v.nodes(),
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
            Operand::Bin(op, l, r) => write!(f, "({} {} {})", l, op, r),
            Operand::Coef(v) => write!(f, "coef {}", v),
            Operand::Mle(v) => write!(f, "mle {}", v),
            Operand::Range(r) => write!(f, "{}", r),
            Operand::Underscore(n) => write!(f, "_{}", n.index()),
        }
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

impl From<Vid> for Operand {
    fn from(v: Vid) -> Self {
        Operand::Var(v)
    }
}

impl From<NodeIndex> for Operand {
    fn from(n: NodeIndex) -> Self {
        Operand::Node(n)
    }
}

