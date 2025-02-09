use share::{Pretty, Traversable1};
use share::{DocAllocator, DocBuilder, BoxAllocator};
use crate::parser::*;

use from_pest::{ConversionError, FromPest, Void};
use pest::Parser;
use pest_derive::Parser;
use pest::error::Error;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};

use thiserror::Error;
use std::fmt;

/// Represents a range of numbers (potentially open)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Range<N> {
    pub start : N,
    pub step : N,
    pub end : N
}

impl<N> Traversable1<N> for Range<N> {
    type Output<Z> = Range<Z>;

    fn traverse1<Z, E>(self, mut f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Range<Z>, E> {
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

impl<'pest> FromPest<'pest> for Range<Size> {
    type Rule = Rule;
    type FatalError = LogError;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::range => {
                let mut inner = pair.into_inner();
                if inner.len() == 3 {
                    let start = Size::from_pest(&mut inner)?;
                    let step = Bin::from_pest(&mut inner)?;
                    let end = Size::from_pest(&mut inner)?;
                    Ok(Range { start, step: step.soft_log2().ok_or(LogError::NotLog(step)), end })
                } else {
                    let a = Size::from_pest(&mut inner)?;
                    let b = Size::from_pest(&mut inner)?;
                    Ok(Range::new(a, Bin::default(), b))
                }
            },
            _ => unreachable!()
        }
    }
}
