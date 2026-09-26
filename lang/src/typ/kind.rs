use crate::id::Tid;
use share::traversal::ToTraversal1;
use share::Set;
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
    Scalar(Set<Spanned<Tid>>),
    /// Pairing-friendly groups
    Pairing(Spanned<Tid>, Spanned<Tid>),
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
    /// Returns `true` if a type variable of this kind resolves to a scalar-field element.
    ///
    /// Both an unconstrained `Field` and the scalar field `Scalar(groups)` of a set of groups
    /// collapse to `ABase::Scalar` during `ATyp::from_ctyp`.
    pub fn is_scalar(&self) -> bool {
        matches!(self, Kind::Field | Kind::Scalar(_))
    }
    /// Returns `true` if a type variable of this kind resolves to an elliptic-curve group
    /// element, whether it is an unconstrained `Group` or one half of a `Pairing`.
    pub fn is_group(&self) -> bool {
        matches!(self, Kind::Group | Kind::Pairing(_, _))
    }
    /// Returns `true` if this kind is a pairing over exactly the two given type identifiers,
    /// in either order.
    ///
    /// Pairings are unordered here: the source group roles are distinguished later, when
    /// `ATyp::from_ctyp` searches the `kctx` to route one `Tid` to `G1` and the other to `G2`.
    pub fn is_pairing(&self, a: &Tid, b: &Tid) -> bool {
        match self {
            Kind::Pairing(x, y) => (&x.node == a && &y.node == b) || (&y.node == a && &x.node == b),
            _ => false,
        }
    }

    /// If this kind is a pairing that mentions `a`, returns its two source-group identifiers
    /// in declaration order; otherwise returns `None`.
    ///
    /// Used to recover a group's pairing partner from the kind context.
    pub fn get_pairing_of(&self, a: &Tid) -> Option<(Tid, Tid)> {
        match self {
            Kind::Pairing(x, y) => {
                if &x.node == a || &y.node == a {
                    Some((x.node.clone(), y.node.clone()))
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

impl<N: fmt::Display> fmt::Display for Kind<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Field => f.write_str("Field"),
            Kind::Group => f.write_str("Group"),
            Kind::Scalar(groups) => {
                f.write_str("Scalar<")?;
                crate::display::sep(f, groups.iter().map(|t| &t.node), ", ")?;
                f.write_str(">")
            }
            Kind::Pairing(g1, g2) => write!(f, "Pairing<{}, {}>", g1.node, g2.node),
            Kind::Range(r) => write!(f, "{r}"),
            Kind::SizeVar => f.write_str("Size"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar2(a: &str, b: &str) -> Kind<usize> {
        Kind::Scalar(Set::from([
            Spanned::dummy(Tid::new(a)),
            Spanned::dummy(Tid::new(b)),
        ]))
    }
    fn pairing(a: &str, b: &str) -> Kind<usize> {
        Kind::Pairing(Spanned::dummy(Tid::new(a)), Spanned::dummy(Tid::new(b)))
    }
    fn range(start: usize, step: usize, end: usize) -> Kind<usize> {
        Kind::Range(Range {
            start: Spanned::dummy(start),
            step: Some(Spanned::dummy(step)),
            end: Some(Spanned::dummy(end)),
        })
    }

    #[test]
    fn test_kind_relations() {
        let f = Kind::<usize>::Field;
        let g = Kind::<usize>::Group;
        let s = scalar2("A", "B");
        let p = pairing("G1", "G2");
        let sv = Kind::<usize>::SizeVar;
        let r = range(1, 1, 5);

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
