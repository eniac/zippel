use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;

use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use crate::parser::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Distribution {
    Uniform,
    UniformNonZero,
    Nonuniform
}

impl Distribution {
    pub fn is_uniform(&self) -> bool {
        matches!(self, Distribution::Uniform)
    }
    pub fn is_uniform_nz(&self) -> bool {
        matches!(self, Distribution::UniformNonZero)
    }
    pub fn is_nonuniform(&self) -> bool {
        matches!(self, Distribution::Nonuniform)
    }

    // Assumes independence, adding two distributions
    pub fn add(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            (Distribution::Uniform, Distribution::UniformNonZero) 
            | (Distribution::UniformNonZero, Distribution::Uniform) => Distribution::UniformNonZero,
            (Distribution::Uniform, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::Uniform) => Distribution::Uniform,
            (a, b) if a == b => *a,
            (_, _) => Distribution::Nonuniform,
        }
    }

    pub fn sub(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            (Distribution::Uniform, Distribution::UniformNonZero) 
            | (Distribution::UniformNonZero, Distribution::Uniform) => Distribution::UniformNonZero,
            (Distribution::Uniform, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::Uniform) => Distribution::Uniform,
            (a, b) if a == b => *a,
            (_, _) => Distribution::Nonuniform,
        }
    }

    // Assumes independence, multiplying two distributions
    pub fn mul(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            (Distribution::Uniform, Distribution::UniformNonZero) 
            | (Distribution::UniformNonZero, Distribution::Uniform) => Distribution::Uniform,
            (Distribution::Uniform, Distribution::Uniform) => Distribution::Nonuniform,
            (Distribution::UniformNonZero, Distribution::UniformNonZero) => Distribution::UniformNonZero,
            (_, Distribution::Nonuniform)
            | (Distribution::Nonuniform, _) => Distribution::Nonuniform,
        }
    }

    pub fn inv(&self) -> Distribution {
        match self {
            Distribution::UniformNonZero => Distribution::Uniform,
            _ => Distribution::Nonuniform,
        }
    }
}

impl Default for Distribution {
    fn default() -> Self {
        Distribution::Nonuniform
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/* Pretty Formatting & Display */
////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Distribution
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Distribution::Uniform => allocator.text("uniform "),
            Distribution::UniformNonZero => allocator.text("uniform*"),
            Distribution::Nonuniform => allocator.text(""),
        }
    }
    fn is_nil(&self) -> bool {
        self.is_nonuniform()
    }
}

impl<'a> fmt::Display for Distribution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Distribution as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}


impl<'pest> FromPest<'pest> for Distribution {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::distribution => {
                let inner = pair.into_inner();
                if let Some(star_pair) = inner.peek() {
                    if star_pair.as_rule() == Rule::star {
                        return Ok(Distribution::UniformNonZero);
                    }
                }
                Ok(Distribution::Uniform)
            },
            _ => Err(ConversionError::NoMatch),
        }
    }
}


