use crate::id::Tid;
use share::{Pretty, DocAllocator, Set, DocBuilder, BoxAllocator};
use std::fmt;

use crate::typ::range::Range;
use crate::typ::size::Size;
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
    /// Scalar of groups
    Scalar(Set<Tid>),
    /// Pairing-friendly groups
    Pairing(Tid, Tid),
    /// Range of numbers
    Range(Range<usize>),

}

impl Kind {
    pub fn scalar1<'a>(a: &'a str) -> Self {
        Kind::Scalar(Set::singleton(Tid::new(a)))
    }
    pub fn scalar2<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Scalar(Set::from([Tid::new(a), Tid::new(b)]))
    }
    pub fn pairing<'a>(a: &'a str, b: &'a str) -> Self {
        Kind::Pairing(Tid::new(a), Tid::new(b))
    }
    pub fn range(start: usize, step: usize, end: usize) -> Self {
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
            Kind::Scalar(f) =>
                allocator.concat([
                    allocator.text("Scalar<"),
                    allocator.intersperse(f.iter().map(|t| allocator.text(format!("{}", t))), ", "),
                    allocator.text(">"),
                ]),
            Kind::Pairing(g1, g2) => allocator.text(format!("Pairing<{}, {}>", g1, g2)),
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
            Rule::positive => Ok(Kind::Range(Range::singleton(pair.as_str().parse().unwrap()))),
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}
