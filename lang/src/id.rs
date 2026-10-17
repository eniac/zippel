use std::fmt;

/// Type variable identifier
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Tid(pub String);

/// Rewrites the type identifiers in a structure.
pub trait TidSubst: Sized {
    /// Replaces every type identifier `t` with `f(t)` where that is `Some`, in one pass, so no
    /// replacement is itself rewritten again.
    fn map_tids(&mut self, f: &dyn Fn(&Tid) -> Option<Tid>);
}

impl fmt::Display for Tid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Tid {
    fn from(s: &str) -> Self {
        Tid(s.to_string())
    }
}

impl From<String> for Tid {
    fn from(s: String) -> Self {
        Tid(s)
    }
}

impl Default for Tid {
    fn default() -> Self {
        Tid("".to_string())
    }
}

/// Arbitrary instance for Tid
#[cfg(test)]
use arbitrary::{Arbitrary, Unstructured};
#[cfg(test)]
impl<'a> Arbitrary<'a> for Tid {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let c = u.int_in_range(0..=25)?;
        Ok(Tid(format!("{}", (b'A' + c) as char)))
    }
}

impl Tid {
    /// Wrap a string as a type identifier without freshening it.
    pub fn new(s: &str) -> Self {
        Tid(s.to_string())
    }
}

/// Expression variable identifier
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Vid(pub String);

impl fmt::Display for Vid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Vid {
    fn from(s: &str) -> Self {
        Vid(s.to_string())
    }
}

impl From<String> for Vid {
    fn from(s: String) -> Self {
        Vid(s)
    }
}

impl Default for Vid {
    fn default() -> Self {
        Vid("".to_string())
    }
}

/// Arbitrary instance for Vid
#[cfg(test)]
impl<'a> Arbitrary<'a> for Vid {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let c = u.int_in_range(0..=25)?;
        Ok(Vid(format!("{}", (b'a' + c) as char)))
    }
}

impl Vid {
    /// Wrap a string as an expression variable.
    pub fn new(s: &str) -> Self {
        Vid(s.to_string())
    }

    /// A variable named after `root` that no source program can write (`#` is not an
    /// identifier character), for bindings that lowering introduces. It neither captures nor
    /// is captured by a source variable.
    pub fn internal(root: &str) -> Self {
        Vid(format!("{root}#"))
    }
}
