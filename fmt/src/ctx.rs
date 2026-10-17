//! Shared formatter context: allocator, doc type, and common helpers.

use pretty::{DocAllocator, DocBuilder};

pub(crate) use pretty::Arena;

use crate::style::Style;
use crate::trivia::TokenCursor;

/// State for one formatting call. Documents borrow `alloc`, independently of the mutable
/// borrow used to advance the cursor, so earlier documents can be kept while formatting more.
pub(crate) struct Formatter<'doc, 'style> {
    pub(crate) alloc: &'doc Arena<'doc>,
    pub(crate) cursor: TokenCursor,
    pub(crate) style: &'style Style,
}

/// Documents borrow the arena owned by one formatting call. Their edges are references, so
/// cloning and dropping a document never recursively copies or frees its children.
pub(crate) type Doc<'a> = DocBuilder<'a, Arena<'a>, ()>;

/// Wrap a doc in parentheses if needed.
pub(crate) fn parenthesize<'doc>(
    alloc: &'doc Arena<'doc>,
    doc: Doc<'doc>,
    needed: bool,
) -> Doc<'doc> {
    if needed {
        alloc.concat([alloc.text("("), doc, alloc.text(")")])
    } else {
        doc
    }
}

/// Emit `count` hardlines.
pub(crate) fn hardlines<'doc>(alloc: &'doc Arena<'doc>, count: usize) -> Doc<'doc> {
    alloc.concat((0..count).map(|_| alloc.hardline()))
}
