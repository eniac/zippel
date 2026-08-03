use crate::id::Tid;
use share::traversal::ToTraversal1;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty, Set};
use std::fmt;

use crate::ast::range::{Range, RangeTraversal};
use crate::ast::spanned::Spanned;
use crate::ast::Size;

/// The kinds of type variables, parameterized by size type N
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub enum Kind<N> {
    /// Unconstrained finite field type variable
    Field,
    /// Unconstrained group type variable
    Group,
    /// Scalar of groups
    Scalar(Set<Tid>),
    /// Pairing-friendly groups
    Pairing(Tid, Tid),
    /// Range of numbers
    Range(Range<N>),
    /// Externally-provided size parameter (value provided during concretize)
    SizeVar,
}

/// Symbolically-sized kind (used during parsing)
pub type UKind = Kind<Size>;

/// Concretely-sized kind (used after size resolution)
pub type CKind = Kind<usize>;

impl<N> Kind<N> {
    pub fn scalar1(a: &str) -> Self {
        Kind::Scalar(Set::singleton(Tid::new(a)))
    }
    pub fn scalar2<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Scalar(Set::from([Tid::new(a), Tid::new(b)]))
    }
    pub fn pairing<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Pairing(Tid::new(a), Tid::new(b))
    }
    pub fn range(start: N, step: N, end: N) -> Self {
        Kind::Range(Range {
            start: Spanned::dummy(start),
            step: Some(Spanned::dummy(step)),
            end: Some(Spanned::dummy(end)),
        })
    }
    pub fn is_scalar(&self) -> bool {
        matches!(self, Kind::Field | Kind::Scalar(_))
    }
    pub fn is_group(&self) -> bool {
        matches!(self, Kind::Group | Kind::Pairing(_, _))
    }
    pub fn is_pairing(&self, a: &Tid, b: &Tid) -> bool {
        match self {
            Kind::Pairing(x, y) => (x == a && y == b) || (y == a && x == b),
            _ => false,
        }
    }

    pub fn get_pairing_of(&self, a: &Tid) -> Option<(Tid, Tid)> {
        match self {
            Kind::Pairing(x, y) => {
                if x == a || y == a {
                    Some((x.clone(), y.clone()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// Traversal over the size parameter N
impl<N: Clone> ToTraversal1<N> for Kind<N> {
    type Output<Z> = Kind<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Kind<Z>, E> {
        match self {
            Kind::Field => Ok(Kind::Field),
            Kind::Group => Ok(Kind::Group),
            Kind::Scalar(s) => Ok(Kind::Scalar(s)),
            Kind::Pairing(a, b) => Ok(Kind::Pairing(a, b)),
            Kind::Range(r) => Ok(Kind::Range(r.traverse1(f)?)),
            Kind::SizeVar => Ok(Kind::SizeVar),
        }
    }
}

/// Range traversal for Kind
impl<N: Clone> RangeTraversal<N> for Kind<N> {
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E> {
        match self {
            Kind::Range(r) => Ok(Kind::Range(f(r)?)),
            _ => Ok(self),
        }
    }
}

impl<'a, D, A, N> Pretty<'a, D, A> for Kind<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Kind::Field => allocator.text("Field"),
            Kind::Group => allocator.text("Group".to_string()),
            Kind::Scalar(f) => allocator.concat([
                allocator.text("Scalar<"),
                allocator.intersperse(f.iter().map(|t| allocator.text(format!("{}", t))), ", "),
                allocator.text(">"),
            ]),
            Kind::Pairing(g1, g2) => allocator.text(format!("Pairing<{}, {}>", g1, g2)),
            Kind::Range(r) => r.pretty(allocator),
            Kind::SizeVar => allocator.text("Size"),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone + 'a> fmt::Display for Kind<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Kind<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kind_relations() {
        let f = Kind::<usize>::Field;
        let g = Kind::<usize>::Group;
        let s = Kind::<usize>::scalar2("A", "B");
        let p = Kind::<usize>::pairing("G1", "G2");
        let sv = Kind::<usize>::SizeVar;
        let r = Kind::<usize>::range(1, 1, 5);

        assert!(f.is_scalar());
        assert!(!f.is_group());

        assert!(!g.is_scalar());
        assert!(g.is_group());

        assert!(s.is_scalar());
        assert!(!s.is_group());

        assert!(!p.is_scalar());
        assert!(p.is_group());

        assert!(!sv.is_scalar());
        assert!(!sv.is_group());

        assert!(!r.is_scalar());
        assert!(!r.is_group());

        // pairing relations
        let t_g1 = Tid::new("G1");
        let t_g2 = Tid::new("G2");
        let t_g3 = Tid::new("G3");
        assert!(p.is_pairing(&t_g1, &t_g2));
        assert!(p.is_pairing(&t_g2, &t_g1));
        assert!(!p.is_pairing(&t_g1, &t_g3));
        assert!(!g.is_pairing(&t_g1, &t_g2));

        assert_eq!(p.get_pairing_of(&t_g1), Some((t_g1.clone(), t_g2.clone())));
        assert_eq!(p.get_pairing_of(&t_g2), Some((t_g1.clone(), t_g2.clone())));
        assert_eq!(p.get_pairing_of(&t_g3), None);
        assert_eq!(g.get_pairing_of(&t_g1), None);
    }
}
