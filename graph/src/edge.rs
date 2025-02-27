use lang::id::Vid;
use share::{Pretty, DocAllocator, BoxAllocator, DocBuilder};

use std::fmt;

/// Represents edges of graphs in the Zippel language
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Dependency {
    Data,       // Data dependency
    Transcript, // Transcript dependency
    Implicit    // Implicit dependency
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Edge {
    pub var: Option<Vid>,
    pub non_zero: Vec<Vid>,
    pub dep: Dependency,
}

impl fmt::Display for Dependency {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Dependency::Data => write!(f, "Data"),
            Dependency::Transcript => write!(f, "Transcript"),
            Dependency::Implicit => write!(f, "Implicit"),
        }
    }
}

/// Pretty printer instance for typed AExp
impl<'a, D, T> Pretty<'a, D, T> for Edge
where
    D: DocAllocator<'a, T>,
    D::Doc: Clone,
    T: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, T> {
        allocator.concat([
            allocator.text(format!("{}, ", self.dep)),
            self.var.map_or(allocator.nil(), |v| v.pretty(allocator)),
            allocator.text(", "),
            allocator.intersperse(
                self.non_zero.into_iter()
                    .map(|v| v.pretty(allocator).append(allocator.text(" != 0"))),
                ", ")
        ])
    }

    fn is_nil(&self) -> bool {
        self.var.is_none() && self.non_zero.is_empty() && self.dep == Dependency::Data
    }
}

impl fmt::Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_nil() {
            return write!(f, "")
        } else {
            <Edge as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
        }
    }
}
