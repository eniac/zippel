use crate::id::Tid;
use crate::typ::kind::Kind;

use std::fmt;

/// A type variable with an associated kind
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVar { pub id: Tid, pub kind: Kind }
impl TypeVar {
    pub fn new(id: Tid, kind: Kind) -> Self {
        TypeVar { id, kind }
    }
}

impl<'a> fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} : {}", self.id, self.kind)
    }
}
