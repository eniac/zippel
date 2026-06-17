use crate::ast::BinOp;
use crate::id::Tid;
use crate::typ::range::{Range, RangeError};
use std::fmt;
use thiserror::Error;

#[derive(Error, PartialEq, Debug)]
pub enum LubError {
    #[error("{0}\n\n{1}")]
    Next(Box<LubError>, Box<LubError>),
    #[error("LubError: Cannot take equality of {0} == {1}")]
    Equ(String, String),
    #[error("LubError: Cannot take the least-upper bound: {1} {0} {2}")]
    Bin(BinOp, String, String),
    #[error("LubError: Cannot take dot-product of {0} . {1}")]
    Dot(String, String),
    #[error("LubError: Cannot take bilinear pairing of {0} and {1}")]
    Pair(String, String),
    #[error("LubError: Malformed range {0}\n\n{1}")]
    BadRange(Range<usize>, RangeError),
    #[error("LubError: Kind {0} not found")]
    KindNotFound(Tid),
    #[error("LubError: Cannot evaluate {0} at {1}")]
    Eval(String, String),
    #[error(
        "LubError: Degree overflow under reduce multiplication: degree {0} * vector length {1}"
    )]
    DegreeOverflow(usize, usize),
}

impl LubError {
    pub fn next(a: LubError, b: LubError) -> Self {
        LubError::Next(Box::new(a), Box::new(b))
    }
    pub fn kind_not_found(id: &Tid) -> Self {
        LubError::KindNotFound(id.clone())
    }
    pub fn bad_range(r: &Range<usize>, e: RangeError) -> Self {
        LubError::BadRange(*r, e)
    }
    pub fn equ<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Equ(a.to_string(), b.to_string())
    }
    pub fn add<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Add, a.to_string(), b.to_string())
    }
    pub fn sub<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Sub, a.to_string(), b.to_string())
    }
    pub fn mul<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Mul, a.to_string(), b.to_string())
    }
    pub fn div<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Div, a.to_string(), b.to_string())
    }
    pub fn pow<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Pow, a.to_string(), b.to_string())
    }
    pub fn eval<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Eval(a.to_string(), b.to_string())
    }
    pub fn rem<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Rem, a.to_string(), b.to_string())
    }
    pub fn dot<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Dot, a.to_string(), b.to_string())
    }
    pub fn pair<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Pair(a.to_string(), b.to_string())
    }
    pub fn and<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::And, a.to_string(), b.to_string())
    }
    pub fn concat<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Concat, a.to_string(), b.to_string())
    }
}
