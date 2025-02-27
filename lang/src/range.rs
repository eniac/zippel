use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;
use thiserror::Error;

use share::{Pretty, Traversal, DocAllocator, DocBuilder, BoxAllocator, Ctx};
use share::traversal::ToTraversal1;
use crate::typ::Size;
use crate::parser::*;


#[derive(Error, PartialEq, Debug)]
pub enum RangeError {
    #[error("Instantiated an invalid range [{0},{1}..{2}]")]
    RangeOrder(usize, usize, usize),
}

/// Represents a range of numbers
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Range<N> {
    pub start : N,
    pub step : N,
    pub end : N
}

/// Implementations of this trait can modify ranges
pub trait RangeTraversal<N> : Sized {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E>;
}

impl<N> ToTraversal1<N> for Range<N> {
    type Output<Z> = Range<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Range<Z>, E> {
        Ok(Range {
            start: f(self.start)?,
            step: f(self.step)?,
            end: f(self.end)?
        })
    }
}

/// Concrete sized range of numbers
pub type CRange = Range<usize>;
impl Copy for CRange {}

impl CRange {
    /// Create a range from a start, step and end numbers, checking their order
    pub fn from_num(start: usize, step: usize, end: usize) -> Result<Self, RangeError> {
        // Check if the range is well formed
        let rs = Range { start, step, end };
        if (start <= end) &&  (step > 0) && ((end - start) % step == 0) {
            Ok(rs)
        } else {
            Err(RangeError::RangeOrder(start, step, end))
        }
    }

    pub fn check(&self) -> Result<(), RangeError> {
        Range::from_num(self.start, self.step, self.end).map(|_| ())
    }

    /// Create a singleton range
    pub fn singleton(start: usize) -> Self {
        Range { start, step: 1, end: start + 1 }
    }

    /// Function to check if a value is contained in the range
    pub fn contains(&self, value: usize) -> bool {
        // Check if the value is within the bounds of the range
        if value < self.start || value >= self.end {
            return false;
        }

        // Check if the value aligns with the step
        (value - self.start) % self.step == 0
    }

    pub fn get_size(&self) -> usize {
        (self.end - self.start) / self.step
    }

}

pub struct RangeTraversal1<N>(std::marker::PhantomData<N>);
impl<A, B> Traversal<A, B> for RangeTraversal1<A> {
    type Domain = Range<A>;
    type Codomain = Range<B>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E> {
        Ok(Range {
            start: f(on.start)?,
            step: f(on.step)?,
            end: f(on.end)?,
        })
    }
}

impl Iterator for CRange {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start >= self.end {
            None
        } else {
            let current = self.start;
            self.start = self.start.saturating_add(self.step);
            Some(current)
        }
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

impl<'pest> FromPest<'pest> for CRange {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let r: Range<Size> = Range::from_pest(pest)?;
        // Evaluate Size with empty context ~ cast to usize
        let start = r.start.eval(&Ctx::new())?;
        let step = r.step.eval(&Ctx::new())?;
        let end = r.end.eval(&Ctx::new())?;

        // Check if the range is well formed
        Ok(Range::from_num(start, step, end)?)
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
                    Ok(Range { start, step, end })
                } else {
                    let start = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    let end = Size::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                    Ok(Range { start, step: Size::one(), end })
                }
            },
            _ => unreachable!()
        }
    }
}

#[cfg(test)] use pest::Parser;
#[test]
fn range_parser() {
    let mut pairs = ZippelParser::parse(Rule::range, "0..10").unwrap();
    assert_eq!(Range::from_pest(&mut pairs).unwrap(), Range { start: Size::from(0), step: Size::one(), end: Size::from(10) });

    pairs = ZippelParser::parse(Rule::range, "0, 2..2^N").unwrap();
    assert_eq!(Range::from_pest(&mut pairs).unwrap(), Range { start: Size::from(0), step: Size::from(2), end: Size::from(2) ^ Size::from("N") });
}

#[test]
fn range_traversal() {
    let r = Range { start: Size::varstr("N"), step: Size::from(2), end: Size::from(10) };
    assert_eq!(
        r.traverse1(&mut |x| x.eval(&Ctx::singleton("N".into(), 0))).unwrap(),
        Range { start: 0, step: 2, end: 10 }
    );
}
