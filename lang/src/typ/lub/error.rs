use crate::ast::range::{Range, RangeError};
use crate::ast::BinOp;
use crate::id::Tid;
use std::fmt;
use thiserror::Error;

/// Failure of a least-upper-bound computation between two source-level types (or kinds).
///
/// Produced by the [`Lub`](super::Lub) implementations while `lang`-level type inference joins the
/// operand types of a binary operation. Payloads are pre-rendered strings because the trait is
/// implemented for several different carriers (`CTyp`, `Tid`, `Range<usize>`, `CTypeVar`).
#[derive(Error, PartialEq, Debug)]
pub enum LubError {
    /// Chains a high-level failure with the more specific failure that caused it; rendered as two
    /// blank-line separated messages.
    #[error("{0}\n\n{1}")]
    Next(Box<LubError>, Box<LubError>),
    /// Two types have no common supertype under `==` / `lub_equ`.
    #[error("LubError: Cannot take equality of {0} == {1}")]
    Equ(String, String),
    /// No least-upper bound exists for the given [`BinOp`] applied to the two operand types.
    #[error("LubError: Cannot take the least-upper bound: {1} {0} {2}")]
    Bin(BinOp, String, String),
    /// Dot product between two incompatible operand types.
    #[error("LubError: Cannot take dot-product of {0} . {1}")]
    Dot(String, String),
    /// Bilinear pairing applied to operands that are not a `G1`/`G2` pair.
    #[error("LubError: Cannot take bilinear pairing of {0} and {1}")]
    Pair(String, String),
    /// A [`Range`] operand failed its own well-formedness check during the join.
    #[error("LubError: Malformed range {0}\n\n{1}")]
    BadRange(Range<usize>, RangeError),
    /// A [`Tid`] has no entry in the kind context, so its kind cannot be consulted.
    #[error("LubError: Kind {0} not found")]
    KindNotFound(Tid),
    /// A polynomial evaluation whose point shape is incompatible with the polynomial.
    #[error("LubError: Cannot evaluate {0} at {1}")]
    Eval(String, String),
    /// `reduce(*)` over a vector of polynomials overflowed `usize` when multiplying the element
    /// degree by the vector length.
    #[error(
        "LubError: Degree overflow under reduce multiplication: degree {0} * vector length {1}"
    )]
    DegreeOverflow(usize, usize),
}

/// Constructors; each mirrors one `Lub` method so call sites stay terse.
impl LubError {
    /// Wraps `b` as the cause of `a`, boxing both.
    pub fn next(a: LubError, b: LubError) -> Self {
        LubError::Next(Box::new(a), Box::new(b))
    }
    /// The kind context has no binding for `id`.
    pub fn kind_not_found(id: &Tid) -> Self {
        LubError::KindNotFound(id.clone())
    }
    /// The range `r` is malformed, with `e` describing how.
    pub fn bad_range(r: &Range<usize>, e: RangeError) -> Self {
        LubError::BadRange(r.clone(), e)
    }
    /// Equality (`lub_equ`) failed between `a` and `b`.
    pub fn equ<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Equ(a.to_string(), b.to_string())
    }
    /// Addition (`lub_add`) failed between `a` and `b`.
    pub fn add<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Add, a.to_string(), b.to_string())
    }
    /// Subtraction (`lub_sub`) failed between `a` and `b`.
    pub fn sub<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Sub, a.to_string(), b.to_string())
    }
    /// Multiplication (`lub_mul`) failed between `a` and `b`.
    pub fn mul<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Mul, a.to_string(), b.to_string())
    }
    /// Division (`lub_div`) failed between `a` and `b`.
    pub fn div<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Div, a.to_string(), b.to_string())
    }
    /// Exponentiation (`lub_pow`) failed between `a` and `b`.
    pub fn pow<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Pow, a.to_string(), b.to_string())
    }
    /// Evaluating the polynomial `a` at the point `b` is ill-typed.
    pub fn eval<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Eval(a.to_string(), b.to_string())
    }
    /// Remainder (`lub_rem`) failed between `a` and `b`.
    pub fn rem<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Rem, a.to_string(), b.to_string())
    }
    /// Dot product (`lub_dot`) failed between `a` and `b`.
    pub fn dot<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Dot, a.to_string(), b.to_string())
    }
    /// Bilinear pairing (`lub_pair`) failed between `a` and `b`.
    pub fn pair<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Pair(a.to_string(), b.to_string())
    }
    /// Concatenation (`lub_concat`) failed between `a` and `b`.
    pub fn concat<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::Concat, a.to_string(), b.to_string())
    }
    /// Boolean conjunction (`lub_and`) failed between `a` and `b`.
    pub fn and<K: fmt::Display>(a: &K, b: &K) -> Self {
        LubError::Bin(BinOp::And, a.to_string(), b.to_string())
    }
}
