use lang::range::CRange;
use lang::id::Vid;
use lang::ast::FreeVars;
use lang::ast::BinOp;
use std::fmt;
use petgraph::graph::NodeIndex;

/// Values are expressions which are (very close to) irreducible
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Value {
    /// Numeric literal
    Lit(usize),
    /// Binary operation
    Bin(BinOp, Box<Value>, Box<Value>),
    /// Node input
    Underscore(NodeIndex),
    /// Coefficients of a univariate vector
    Coef(Box<Value>),
    /// Multilinear extension of a 2^N vector of coefficients
    Mle(Box<Value>),
    /// Range of numbers
    Range(CRange),
    /// Random access into a value
    Ram(Box<Value>, Box<Value>),
    /// Vector of values
    Vec(Vec<Value>),
}

impl Value {
    pub fn ram(v: Value, i: Value) -> Value {
        match (v, i) {
            (Value::Ram(box v, r), Value::Lit(i)) =>
                Value::Ram(Box::new(v), r.compose_index(i).expect("InternalError: Invalid range")),
            (Value::Vec(vs), Value::Lit(i)) => vs[i].clone(),
            (Value::Vec(vs), Value::Range(r)) => {
                let mut res = Vec::new();
                for i in r {
                    res.push(vs[i].clone());
                }
                Value::Vec(res)
            },
            (Value::Range(r), Value::Lit(i)) => Value::Lit(r.start + i* r.step),
            (v, i) => Value::Ram(Box::new(v), Box::new(i)),
        }
    }

    pub fn concat(v1: Value, v2: Value) -> Value {
        match (v1, v2) {
            (Value::Vec(mut vs1), Value::Vec(vs2)) => {
                vs1.extend(vs2);
                Value::Vec(vs1)
            },
            (Value::Vec(mut vs), v) | (v, Value::Vec(mut vs)) => {
                vs.push(v);
                Value::Vec(vs)
            },
            (l, r) => Value::Bin(BinOp::Concat, Box::new(l), Box::new(r)),
        }
    }

    pub fn add(v1: Value, v2: Value) -> Value {
        match (v1, v2) {
            (Value::Vec(l), Value::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Value::add(l.clone(), r.clone()));
                }
                Value::Vec(res)
            },
            (Value::Vec(mut vs), v) | (v, Value::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Value::add(l.clone(), v.clone()));
                Value::Vec(vs)
            },
            (Value::Range(l), Value::Range(r)) => Value::Range(l + r),
            (Value::Range(l), Value::Lit(r)) | (Value::Lit(r), Value::Range(l)) =>
                Value::Range(l + CRange::singleton(r)),
            (l, r) =>
                Value::Bin(BinOp::Add, Box::new(l), Box::new(r)),
        }
    }

    pub fn sub(v1: Value, v2: Value) -> Value {
        match (v1, v2) {
            (Value::Vec(l), Value::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Value::sub(l.clone(), r.clone()));
                }
                Value::Vec(res)
            },
            (Value::Vec(mut vs), v) | (v, Value::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Value::sub(l.clone(), v.clone()));
                Value::Vec(vs)
            },
            (Value::Range(l), Value::Range(r)) => Value::Range(l - r),
            (Value::Range(l), Value::Lit(r)) => Value::Range(l - CRange::singleton(r)),
            (Value::Lit(l), Value::Range(r)) => Value::Range(CRange::singleton(l) - r),
            (l, r) =>
                Value::Bin(BinOp::Sub, Box::new(l), Box::new(r)),
        }
    }

    pub fn mul(v1: Value, v2: Value) -> Value {
        match (v1, v2) {
            (Value::Vec(l), Value::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Value::mul(l.clone(), r.clone()));
                }
                Value::Vec(res)
            },
            (Value::Vec(mut vs), v) | (v, Value::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Value::mul(l.clone(), v.clone()));
                Value::Vec(vs)
            },
            (Value::Range(l), Value::Range(r)) => Value::Range(l * r),
            (Value::Range(l), Value::Lit(r)) | (Value::Lit(r), Value::Range(l)) =>
                Value::Range(l * CRange::singleton(r)),
            (l, r) =>
                Value::Bin(BinOp::Mul, Box::new(l), Box::new(r)),
        }
    }

    pub fn div(v1: Value, v2: Value) -> Value {
        match (v1, v2) {
            (Value::Vec(l), Value::Vec(r)) => {
                let mut res = Vec::new();
                for (l, r) in l.iter().zip(r.iter()) {
                    res.push(Value::div(l.clone(), r.clone()));
                }
                Value::Vec(res)
            },
            (Value::Vec(mut vs), v) | (v, Value::Vec(mut vs)) => {
                vs.iter_mut().for_each(|l| *l = Value::div(l.clone(), v.clone()));
                Value::Vec(vs)
            },
            (Value::Range(l), Value::Range(r)) => Value::Range(l / r),
            (Value::Range(l), Value::Lit(r)) => Value::Range(l / CRange::singleton(r)),
            (Value::Lit(l), Value::Range(r)) => Value::Range(CRange::singleton(l) / r),
            (l, r) =>
                Value::Bin(BinOp::Div, Box::new(l), Box::new(r)),
        }
    }

    pub fn dot(v1: Value, v2: Value) -> Value {
        match (v1, v2) {
            (Value::Vec(vs1), Value::Vec(vs2)) => {
                let mut res = Vec::new();
                for (l, r) in vs1.iter().zip(vs2.iter()) {
                    res.push(Value::mul(l.clone(), r.clone()));
                }
                match res.as_slice() {
                    [] => Value::Vec(vec![]),
                    [v] => v.clone(),
                    [h, ts @ ..] =>
                        res.into_iter().fold(h, |acc, v| Value::add(acc, v))
                },
            },

            (l, r) =>
            (Value::Vec(vs),
            (l, r) =>
                Value::Bin(BinOp::Dot, Box::new(l), Box::new(r)),
        }
    }

    pub fn vec(vs: Vec<Value>) -> Value {
        Value::Vec(vs)
    }
    pub fn underscore() -> Value {
        Value::Underscore
    }
    pub fn lit(n: usize) -> Value {
        Value::Lit(n)
    }
    pub fn range(r: CRange) -> Value {
        Value::Range(r)
    }
    pub fn coef(v: Value) -> Value {
        Value::Coef(Box::new(v))
    }
    pub fn mle(v: Value) -> Value {
        Value::Mle(Box::new(v))
    }
    pub fn nodes(&self) -> Vec<NodeIndex> {
        match self {
            Value::Node(n) => vec![*n],
            Value::Ram(box v, _) => v.nodes(),
            Value::Slice(box v, _) => v.nodes(),
            Value::Vec(vs) => vs.iter().fold(Vec::new(), |acc, v| acc.extend(v.nodes())),
            _ => Vec::new(),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Lit(x) => write!(f, "{}", x),
            Value::Var(v) => write!(f, "{}", v),
            Value::Node(_) => write!(f, "_"),
            Value::Ram(box v, r) => write!(f, "{}[{}]", v, r),
            Value::Slice(box v, r) => write!(f, "{}[{}]", v, r),
            Value::Vec(vs) => {
                write!(f, "[")?;
                for v in vs.iter() {
                    write!(f, "{}, ", v)?;
                }
                write!(f, "]")
            },
            Value::Underscore(n) => write!(f, "_{}", n.index()),
        }
    }
}

impl FreeVars for Value {
    fn freevars(&self) -> Set<Vid> {
        match self {
            Value::Lit(_) => Set::new(),
            Value::Var(v) => Set::singleton(*v),
            Value::Node(_) => Set::new(),
            Value::Ram(box v, _) => v.freevars(),
            Value::Slice(box v, _) => v.freevars(),
            Value::Vec(vs) => vs.iter().fold(Set::new(), |acc, v| acc.union(&v.freevars())),
        }
    }
}

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Value::Lit(v)
    }
}

impl From<CRange> for Value {
    fn from(r: CRange) -> Self {
        Value::Range(r)
    }
}

impl From<Vid> for Value {
    fn from(v: Vid) -> Self {
        Value::Var(v)
    }
}

impl From<NodeIndex> for Value {
    fn from(n: NodeIndex) -> Self {
        Value::Node(n)
    }
}

