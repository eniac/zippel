use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::cmp::Ordering;
use std::fmt;

use crate::parser::*;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Qualifier {
    Witness,
    Local,
    Extra,
    Instance,
}

impl Qualifier {
    pub fn is_witness(&self) -> bool {
        matches!(self, Qualifier::Witness)
    }
    pub fn is_local(&self) -> bool {
        matches!(self, Qualifier::Local)
    }
    pub fn is_extra(&self) -> bool {
        matches!(self, Qualifier::Extra)
    }
    pub fn is_instance(&self) -> bool {
        matches!(self, Qualifier::Instance)
    }
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            // Witness ≤ Local ≤ Extra ≤ Instance (join = min in the lattice)
            (Qualifier::Witness, _) | (_, Qualifier::Witness) => Qualifier::Witness,
            (Qualifier::Local, _) | (_, Qualifier::Local) => Qualifier::Local,
            (Qualifier::Extra, _) | (_, Qualifier::Extra) => Qualifier::Extra,
            (Qualifier::Instance, Qualifier::Instance) => Qualifier::Instance,
        }
    }
}

/// Witness <= Local <= Extra <= Instance
impl PartialOrd for Qualifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Qualifier {
    fn cmp(&self, other: &Self) -> Ordering {
        let rank = |q: &Qualifier| -> u8 {
            match q {
                Qualifier::Witness => 0,
                Qualifier::Local => 1,
                Qualifier::Extra => 2,
                Qualifier::Instance => 3,
            }
        };
        rank(self).cmp(&rank(other))
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/* Pretty Formatting & Display */
////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Qualifier
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Qualifier::Witness => allocator.text("witness "),
            Qualifier::Local => allocator.text("local "),
            Qualifier::Extra => allocator.text("extra "),
            Qualifier::Instance => allocator.text("instance "),
        }
    }
    fn is_nil(&self) -> bool {
        false
    }
}

impl fmt::Display for Qualifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Qualifier as Pretty<'_, BoxAllocator, ()>>::pretty(*self, &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}

impl<'pest> FromPest<'pest> for Qualifier {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::qualifier => Qualifier::from_pest(&mut pair.into_inner()),
            Rule::witness => Ok(Qualifier::Witness),
            Rule::extra => Ok(Qualifier::Extra),
            Rule::instance => Ok(Qualifier::Instance),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
use pest::Parser;
#[test]
fn qualifier_parser() {
    let mut pairs = ZippelParser::parse(Rule::qualifier, "witness").unwrap();
    let qual = Qualifier::from_pest(&mut pairs).unwrap();
    assert_eq!(qual, Qualifier::Witness);

    let input = "instance";
    let mut pairs = ZippelParser::parse(Rule::qualifier, input).unwrap();
    let qual = Qualifier::from_pest(&mut pairs).unwrap();
    assert_eq!(qual, Qualifier::Instance);

    let input = "extra";
    let mut pairs = ZippelParser::parse(Rule::qualifier, input).unwrap();
    let qual = Qualifier::from_pest(&mut pairs).unwrap();
    assert_eq!(qual, Qualifier::Extra);
}

/// Regression: join must be a proper meet (min) on Witness ≤ Local ≤ Extra ≤ Instance.
#[test]
fn qualifier_join_lattice_consistency() {
    use Qualifier::*;
    let all = [Witness, Local, Extra, Instance];
    for &a in &all {
        for &b in &all {
            let j = a.join(&b);
            // join(a,b) == min(a,b) in the ordering
            assert_eq!(
                j,
                a.min(b),
                "join({:?}, {:?}) = {:?}, expected {:?}",
                a,
                b,
                j,
                a.min(b)
            );
            // Commutativity
            assert_eq!(
                a.join(&b),
                b.join(&a),
                "join is not commutative for {:?}, {:?}",
                a,
                b
            );
        }
    }
}
