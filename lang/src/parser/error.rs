use from_pest::ConversionError;
use thiserror::Error;
use pest::iterators::Pair;

use crate::id::Tid;
use crate::module::sig::USig;
use crate::parser::Rule;
use crate::typ::{Size, Kind, EvalError};
use crate::typ::range::RangeError;

#[derive(Error, PartialEq, Debug)]
pub enum InputError<'pest> {
    #[error("Duplicate declaration found: {0}")]
    DuplicateDecl(USig),
    #[error("Unexpected expression {0}")]
    UnexpectedExp(Pair<'pest, Rule>),
    #[error("Unsupported operation {0}")]
    UnsupportedOp(Pair<'pest, Rule>),
    #[error("Expected constant arithmetic size expression,found {0}")]
    ExpectedConstSize(Size),
    #[error(transparent)]
    MalformedRange(RangeError),
    #[error("Type variables should start with a capital letter and contain alphanumerics or '_', '-', '\'' {0}")]
    TidCapitalize(Pair<'pest, Rule>),
    #[error("Functions should start with a lowercase letter and contain alphanumerics or '_', '-', '\'' {0}")]
    FidCapitalize(Pair<'pest, Rule>),
    #[error("Variables should start with a lowercase letter and contain alphanumerics or '_', '-', '\'' {0}")]
    VidCapitalize(Pair<'pest, Rule>),
    #[error("Error statically evaluating range expression {0}")]
    RangeError(#[from] EvalError),
    #[error("KindError: Duplicate type variable {0}")]
    DuplicateTid(Tid),
    #[error("KindError: Type variable not found {0}")]
    KindNotFound(Tid),
    #[error("KindError: Pairing<{0},{1}> requires {2}: {3} to be a Group")]
    PairingGroup(Tid, Tid, Tid, Kind),
    #[error("KindError: Multiplicative<{0}> requires {0}: {1} to be a Field")]
    MultiplicativeField(Tid, Kind),
    #[error("KindError: Scalar<{0}> requires {0}: {1} to be a Group")]
    ScalarGroup(Tid, Kind),
}

impl From<EvalError> for ConversionError<InputError<'_>> {
    fn from(e: EvalError) -> Self {
        ConversionError::Malformed(InputError::RangeError(e))
    }
}

impl From<RangeError> for ConversionError<InputError<'_>> {
    fn from(e: RangeError) -> Self {
        ConversionError::Malformed(InputError::MalformedRange(e))
    }
}
