use crate::id::Tid;
use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use std::fmt;

pub use crate::range::Range;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;

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
    /// Range of numbers
    Range(Range<usize>)
}

impl Kind {
    pub fn scalar<'a>(a: &'a str) -> Self {
        Kind::Scalar(Tid::new(a))
    }
    pub fn multiplicative<'a>(a: &'a str) -> Self {
       Kind::Multiplicative(Tid::new(a))
    }
    pub fn pairing<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Pairing(Tid::new(a), Tid::new(b))
    }
    pub fn range(start: usize, step: usize, end: usize) -> Self {
        Kind::Range(Range { start, step, end })
    }
    pub fn is_multiplicative(&self) -> bool {
        match self {
            Kind::Field | Kind::Scalar(_) | Kind::Multiplicative(_) => true,
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
    pub fn get_range(&self) -> Option<&Range<usize>> {
        match self {
            Kind::Range(r) => Some(r),
            _ => None,
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
            Kind::Pairing(g1, g2) => allocator.text(format!("Pairing({}, {})", g1, g2)),
            Kind::Range(r) => allocator.concat([
                r.start.pretty(allocator),
                if r.step == 1 {
                    allocator.nil()
                } else {
                    allocator.text(", ").append(r.step.pretty(allocator))
                },
                allocator.text(".."),
                r.end.pretty(allocator),
            ]),
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

impl<'pest> FromPest<'pest> for Kind {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::kind_ty => Kind::from_pest(&mut pair.into_inner()),
            Rule::field_ty => Ok(Kind::Field),
            Rule::group_ty => Ok(Kind::Group),
            Rule::scalar_ty => Ok(Kind::Scalar(Tid::from_pest(&mut pair.into_inner())?)),
            Rule::multiplicative_ty => Ok(Kind::Multiplicative(Tid::from_pest(&mut pair.into_inner())?)),
            Rule::pairing_ty => {
                let mut inner = pair.into_inner();
                let g1 = Tid::from_pest(&mut inner)?;
                let g2 = Tid::from_pest(&mut inner)?;
                Ok(Kind::Pairing(g1, g2))
            }
            Rule::range_ty => Ok(Kind::Range(Range::from_pest(&mut pair.into_inner())?)),
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}
