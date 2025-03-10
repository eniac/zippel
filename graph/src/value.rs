use lang::typ::range::CRange;

use std::fmt;

/// Values are expressions which are (very close to) irreducible
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Value {
    Lit(usize),                      // Numeric literal
    Range(CRange),                   // A range of a vector variable
    Underscore,                      // An input edge with no variable name
}

impl Value {
    pub fn is_underscore(&self) -> bool {
        match self {
            Value::Underscore => true,
            _ => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Lit(x) => write!(f, "{}", x),
            Value::Range(r) => write!(f, "{}", r),
            Value::Underscore => write!(f, "_"),
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
