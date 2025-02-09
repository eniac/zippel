use crate::id::Tid;
use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use std::fmt;

pub use crate::range::Range;

/// The kinds of type variables
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Kind {
    /// Unconstrained finite field type variable
    Field,
    /// Unconstrained group type variable
    Group,
    /// Scalar field of group [G: Tid]
    Scalar(Tid),
    /// Multiplicative subgroup of field [F: Tid]
    Multiplicative(Tid),
    /// Pairing-friendly groups
    Pairing(Tid, Tid),
    /// Finite size
    Fin(Range<usize>)
}

impl Kind {
    pub fn is_field(&self) -> bool {
        match self {
            Kind::Field | Kind::Scalar(_)  => true,
            _ => false,
        }
    }

    pub fn is_group(&self) -> bool {
        match self {
            Kind::Group | Kind::Pairing(_, _) => true,
            _  => false,
        }
    }

    pub fn in_pairing(&self, a: &Tid) -> bool {
        match self {
            Kind::Pairing(x, y) => x == a || y == a,
            _ => false
        }
    }
    pub fn is_pairing(&self, a: &Tid, b: &Tid) -> bool {
        match self {
            Kind::Pairing(x, y) =>
                (x == a && y == b) || (y == a && x == b),
            _ => false
        }
    }

    pub fn is_multiplicative(&self, t: &Tid) -> bool {
        match self {
            Kind::Multiplicative(x) => x == t,
            _ => false,
        }
    }

    pub fn is_scalar(&self, t: &Tid) -> bool {
        match self {
            Kind::Scalar(x) => x == t,
            _ => false,
        }
    }

    pub fn in_fin(&self, x: &usize) -> bool {
        match self {
            Kind::Fin(a, b) => a <= x && x <= b,
            _ => false,
        }
    }
}


impl<'a, D, A> Pretty<'a, D, A> for Kind
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Kind::Field => allocator.text("Field"),
            Kind::Group => allocator.text(format!("Group")),
            Kind::Scalar(g) => allocator.text(format!("Scalar({})", g)),
            Kind::Multiplicative(f) => allocator.text(format!("Multiplicative({})", f)),
            Kind::Group => allocator.text(format!("Group")),
            Kind::Pairing(g1, g2) => allocator.text(format!("Pairing({}, {})", g1, g2)),
            Kind::Fin(r) => allocator.concat([
                allocator.text("Fin("),
                r.pretty(allocator),
                allocator.text(")")
            ])
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Kind as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
