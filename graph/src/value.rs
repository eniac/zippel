use lang::typ::range::CRange;
use lang::id::Vid;
use lang::ast::FreeVars;
use std::fmt;
use petgraph::graph::NodeIndex;

/// Values are expressions which are (very close to) irreducible
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Value {
    Lit(usize),                      // Numeric literal
    Var(Vid),                        // Variable
    Range(CRange),                   // Range of numbers
    Node(NodeIndex),                 // Input from a node
    Slice(Box<Value>, Box<Value>),       // A slice of a value
    Ram(Box<Value>, Box<Value>),          // Random access memory into a value
    Vec(Vec<Value>),                 // A vector of values
}

impl Value {
    pub fn ram(v: Value, i: Value) -> Value {
        match (v, i) {
            (Value::Slice(box v, r), Value::Lit(i)) =>
                Value::Ram(Box::new(v), r.compose_index(i).expect("InternalError: Invalid range")),
            (Value::Vec(vs), Value::Lit(i)) => vs[i].clone(),
            (v, i) => Value::Ram(Box::new(v), Box::new(i)),
        }
    }
    pub fn slice(v: Value, r: Value) -> Value {
        match (v, r) {
            (Value::Slice(box v, r0), Value::Range(r)) =>
                Value::Slice(Box::new(v), r.compose(&r0)),
            (Value::Vec(vs), Value::Range(r)) => {
                let mut res = Vec::new();
                for i in r {
                    res.push(vs[i].clone());
                }
                Value::Vec(res)
            },
            (v, r) => Value::Slice(Box::new(v), Box::new(r)),
        }
    }
    pub fn vec(vs: Vec<Value>) -> Value {
        Value::Vec(vs)
    }
    pub fn underscore() -> Value {
        Value::Underscore
    }
    pub fn var(v: Vid, n: NodeIndex) -> Value {
        Value::Var(v)
    }
    pub fn lit(n: usize) -> Value {
        Value::Lit(n)
    }
    pub fn range(r: CRange) -> Value {
        Value::Range(r)
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
            Value::Underscore => write!(f, "_"),
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

