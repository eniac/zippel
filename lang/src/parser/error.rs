use from_pest::ConversionError;
use thiserror::Error;
use pest::iterators::Pair;

use crate::id::Fid;
use crate::range::Range;
use crate::parser::Rule;
use crate::typ::{Size, EvalError};

#[derive(Error, PartialEq, Debug)]
pub enum InputError<'pest> {
    #[error("Duplicate declaration found {0}")]
    DuplicateDecl(Fid),
    #[error("Unexpected expression {0}")]
    UnexpectedExp(Pair<'pest, Rule>),
    #[error("Unsupported operation {0}")]
    UnsupportedOp(Pair<'pest, Rule>),
    #[error("Expected constant arithmetic size expression,found {0}")]
    ExpectedConstSize(Size),
    #[error("Malformed range expression {0}")]
    MalformedRange(Range<usize>),
    #[error("Type variables should start with a capital letter and contain alphanumerics or '_', '-', '\'' {0}")]
    TidCapitalize(Pair<'pest, Rule>),
    #[error("Functions should start with a lowercase letter and contain alphanumerics or '_', '-', '\'' {0}")]
    FidCapitalize(Pair<'pest, Rule>),
    #[error("Variables should start with a lowercase letter and contain alphanumerics or '_', '-', '\'' {0}")]
    VidCapitalize(Pair<'pest, Rule>),
    #[error("Error statically evaluating range expression {0}")]
    RangeError(#[from] EvalError),
}

impl From<EvalError> for ConversionError<InputError<'_>> {
    fn from(e: EvalError) -> Self {
        ConversionError::Malformed(InputError::RangeError(e))
    }
}
