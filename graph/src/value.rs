use lang::ast::{CSig, CExp, BinOp};
use lang::typ::{CTyp, Nothing};
use lang::id::{Fid, Tid, Vid};
use lang::typ::range::CRange;
use lang::typ::lub::{Lub, LubError};
use std::ops::{Add, Sub, Mul, Div};
use share::traversal::ToTraversal1;

use crate::principal::Principal;
use std::fmt;

/// Values are expressions which are (very close to) irreducible
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Value {
    Lit(usize),                      // Numeric literal
    Bool(bool),                      // Boolean literal
    Range(CRange),                   // Range literal
    Vec(Vec<usize>),                 // Vector literal
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Lit(x) => write!(f, "{}", x),
            Value::Bool(x) => write!(f, "{}", x),
            Value::Range(r) => write!(f, "{}", r),
            Value::Vec(vs) => write!(f, "[{}]",
                vs.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "))
        }
    }
}

impl From<CRange> for Value {
    fn from(r: CRange) -> Self {
        Value::Range(r)
    }
}

impl<const N: usize> From<[Value; N]> for Value {
    fn from(vs: [Value; N]) -> Self {
        Value::Vec(vs.to_vec())
    }
}

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Value::Lit(v)
    }
}

impl From<bool> for Value {
    fn from(v: bool) -> Self {
        Value::Bool(v)
    }
}
