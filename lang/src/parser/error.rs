use from_pest::ConversionError;
use pest::iterators::Pair;
use thiserror::Error;

use crate::ast::arg::UArgs;
use crate::ast::sig::USig;
use crate::id::{Tid, Vid};
use crate::parser::Rule;
use crate::typ::range::RangeError;
use crate::typ::{EvalError, Size, UKind, UTypeVars};
use share::Set;

#[derive(Error, PartialEq, Debug)]
pub enum InputError<'pest> {
    #[error("Duplicate declaration found: {0}")]
    DuplicateDecl(USig),
    #[error("KindError: Duplicate identifiers {0}")]
    DuplicateIdents(String),
    #[error("Unexpected expression {0}")]
    UnexpectedExp(Pair<'pest, Rule>),
    #[error("Unsupported operation {0}")]
    UnsupportedOp(Pair<'pest, Rule>),
    #[error("Eval selector requires explicit evaluation points: {0}")]
    EvaluateSelectorWithoutPoints(Pair<'pest, Rule>),
    #[error("Expected constant arithmetic size expression,found {0}")]
    ExpectedConstSize(Size),
    #[error(transparent)]
    MalformedRange(RangeError),
    #[error("Error statically evaluating range expression {0}")]
    RangeError(#[from] EvalError),
    #[error("KindError: Duplicate type variable {0}")]
    DuplicateTid(Tid),
    #[error("KindError: Type variable not found {0}")]
    KindNotFound(Tid),
    #[error("KindError: Pairing<{0},{1}> requires {2}: {3} to be a Group")]
    PairingGroup(Tid, Tid, Tid, UKind),
    #[error("KindError: Scalar<{0}> requires {0}: {1} to be a Group")]
    ScalarGroup(Set<Tid>, UKind),
    #[error("EmptyDeclaration: Empty declaration body found: {0}{1}{2}")]
    EmptyDecl(Vid, UTypeVars, UArgs),
    #[error("Cyclic type alias dependency: {0}")]
    CyclicTypeAlias(Tid),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_eval_error() {
        let eval_err = EvalError::DivisionByZero(Size::Lit(1), Size::Lit(0));
        let conv_err: ConversionError<InputError> = eval_err.into();
        match conv_err {
            ConversionError::Malformed(InputError::RangeError(_)) => {}
            _ => panic!("Expected RangeError conversion"),
        }
    }

    #[test]
    fn test_from_range_error() {
        let range_err = RangeError::RangeOrder(0, 1, 0);
        let conv_err: ConversionError<InputError> = range_err.into();
        match conv_err {
            ConversionError::Malformed(InputError::MalformedRange(_)) => {}
            _ => panic!("Expected MalformedRange conversion"),
        }
    }
}
