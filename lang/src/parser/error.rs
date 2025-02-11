use thiserror::Error;
use pest::iterators::Pair;

use crate::id::Fid;
use crate::parser::Rule;

#[derive(Error, PartialEq, Debug)]
pub enum InputError<'pest> {
    #[error("Duplicate declaration found {0}")]
    DuplicateDecl(Fid),
    #[error("Unexpected expression {0}")]
    UnexpectedExp(Pair<'pest, Rule>),
    #[error("Unsupported operation {0}")]
    UnsupportedOp(Pair<'pest, Rule>),
}
