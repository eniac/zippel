use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use pest::Parser;
use std::fmt;

use share::{Pretty, Traversable1, Ctx};
use share::{DocAllocator, DocBuilder, BoxAllocator};
use crate::typ::Size;
use crate::parser::*;

/// Represents a range of numbers (potentially open)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Range<N> {
    pub start : N,
    pub step : N,
    pub end : N
}

impl<N> Range<N> {
    pub fn new(start: N, step: N, end: N) -> Self {
        Range { start, step, end }
    }
}

impl<N> Traversable1<N> for Range<N> {
    type Output<Z> = Range<Z>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Range<Z>, E> {
        Ok(Range {
            start: f(self.start)?,
            end: f(self.end)?,
            step: f(self.step)?,
        })
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for Range<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A>,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            self.start.pretty(allocator),
            allocator.text(", "),
            self.step.pretty(allocator),
            allocator.text(".."),
            self.end.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Range<N> where N: Pretty<'a, BoxAllocator, ()> + Clone {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Range<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'pest> FromPest<'pest> for Range<usize> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let r: Range<Size> = Range::from_pest(pest)?;
        // Evaluate with empty context ~ cast to usize
        let start = r.start.eval(&Ctx::new()).ok_or(ConversionError::Malformed(InputError::ExpectedConstSize(r.start)))?;
        let step = r.step.eval(&Ctx::new()).ok_or(ConversionError::Malformed(InputError::ExpectedConstSize(r.step)))?;
        let end = r.end.eval(&Ctx::new()).ok_or(ConversionError::Malformed(InputError::ExpectedConstSize(r.end)))?;
        let rs = Range::new(start as usize, step as usize, end as usize);
        if (start <= end) && ((end - start) % step == 0) {
            Ok(rs)
        } else {
            Err(ConversionError::Malformed(InputError::MalformedRange(rs)))
        }
    }
}

impl<'pest> FromPest<'pest> for Range<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::range => {
                let mut inner = pair.into_inner();
                if inner.len() == 3 {
                    let start = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    let step = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    let end = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    Ok(Range::new(start, step, end))
                } else {
                    dbg!(&inner);
                    let start = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    let end = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    Ok(Range::new(start, Size::one(), end))
                }
            },
            _ => unreachable!()
        }
    }
}

#[test]
fn range_parser() {
    let mut pairs = ZippelParser::parse(Rule::range, "0..10").unwrap();
    assert_eq!(Range::from_pest(&mut pairs).unwrap(), Range::new(Size::from(0), Size::one(), Size::from(10)));

    pairs = ZippelParser::parse(Rule::range, "0, 2..2^N").unwrap();
    assert_eq!(Range::from_pest(&mut pairs).unwrap(), Range::new(Size::from(0), Size::from(2), Size::from(2) ^ Size::from("N")));
}
