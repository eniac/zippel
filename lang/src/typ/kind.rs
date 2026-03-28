use crate::id::Tid;
use share::{Pretty, DocAllocator, Set, DocBuilder, BoxAllocator};
use share::traversal::ToTraversal1;
use std::fmt;

use crate::typ::range::{Range, RangeTraversal};
use crate::typ::Size;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;

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
}

/// Symbolically-sized kind (used during parsing)
pub type UKind = Kind<Size>;

/// Concretely-sized kind (used after size resolution)
pub type CKind = Kind<usize>;

impl<N> Kind<N> {
    pub fn scalar1<'a>(a: &'a str) -> Self {
        Kind::Scalar(Set::singleton(Tid::new(a)))
    }
    pub fn scalar2<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Scalar(Set::from([Tid::new(a), Tid::new(b)]))
    }
    pub fn pairing<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Pairing(Tid::new(a), Tid::new(b))
    }
    pub fn range(start: N, step: N, end: N) -> Self {
        Kind::Range(Range { start, step, end })
    }
    pub fn is_scalar(&self) -> bool {
        match self {
            Kind::Field => true,
            Kind::Scalar(_) => true,
            _ => false,
        }
    }
    pub fn is_group(&self) -> bool {
        match self {
            Kind::Group | Kind::Pairing(_, _) => true,
            _  => false,
        }
    }
    pub fn is_pairing(&self, a: &Tid, b: &Tid) -> bool {
        match self {
            Kind::Pairing(x, y) =>
                (x == a && y == b) || (y == a && x == b),
            _ => false
        }
    }

    pub fn get_pairing_of(&self, a: &Tid) -> Option<(Tid, Tid)> {
        match self {
            Kind::Pairing(x, y) => if x == a || y == a { Some((x.clone(), y.clone())) } else { None }
            _ => None
        }
    }
}

/// Traversal over the size parameter N
impl<N> ToTraversal1<N> for Kind<N> {
    type Output<Z> = Kind<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Kind<Z>, E> {
        match self {
            Kind::Field => Ok(Kind::Field),
            Kind::Group => Ok(Kind::Group),
            Kind::Scalar(s) => Ok(Kind::Scalar(s)),
            Kind::Pairing(a, b) => Ok(Kind::Pairing(a, b)),
            Kind::Range(r) => Ok(Kind::Range(r.traverse1(f)?)),
        }
    }
}

/// Range traversal for Kind
impl<N: Clone> RangeTraversal<N> for Kind<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
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
            Kind::Group => allocator.text(format!("Group")),
            Kind::Scalar(f) =>
                allocator.concat([
                    allocator.text("Scalar<"),
                    allocator.intersperse(f.iter().map(|t| allocator.text(format!("{}", t))), ", "),
                    allocator.text(">"),
                ]),
            Kind::Pairing(g1, g2) => allocator.text(format!("Pairing<{}, {}>", g1, g2)),
            Kind::Range(r) => r.pretty(allocator),
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

impl<'pest> FromPest<'pest> for UKind {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::kind_ty => UKind::from_pest(&mut pair.into_inner()),
            Rule::field_ty => Ok(Kind::Field),
            Rule::group_ty => Ok(Kind::Group),
            Rule::scalar_ty => {
                let inner = pair.into_inner();
                let mut idents: Vec<Tid> = Vec::new();
                for inner in inner {
                    let t = Tid::from_pest(&mut Pairs::single(inner))?;
                    idents.push(t);
                }
                let len = idents.len();
                let set = Set::from(idents.clone());
                if len != set.len() {
                    return Err(ConversionError::Malformed(InputError::DuplicateIdents(
                        idents
                            .iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<String>>()
                            .join(", "),
                    )));
                }
                Ok(Kind::Scalar(set))
            },
            Rule::pairing_ty => {
                let mut inner = pair.into_inner();
                let g1 = Tid::from_pest(&mut inner)?;
                let g2 = Tid::from_pest(&mut inner)?;
                Ok(Kind::Pairing(g1, g2))
            },
            Rule::range_ty => Ok(Kind::Range(Range::from_pest(&mut pair.into_inner())?)),
            Rule::positive => {
                let n: u32 = pair.as_str().parse().unwrap();
                Ok(Kind::Range(Range {
                    start: Size::Lit(n),
                    step: Size::one(),
                    end: Size::Lit(n + 1),
                }))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}
