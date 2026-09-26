//! Shared formatter context: allocator, doc type, and common helpers.

use pretty::{BoxAllocator, DocAllocator, DocBuilder};

pub(crate) const ALLOC: BoxAllocator = BoxAllocator;
pub(crate) type Doc<'a> = DocBuilder<'a, BoxAllocator, ()>;

/// Wrap a doc in parentheses if needed.
pub(crate) fn parenthesize(doc: Doc<'static>, needed: bool) -> Doc<'static> {
    if needed {
        ALLOC.concat([ALLOC.text("("), doc, ALLOC.text(")")])
    } else {
        doc
    }
}

/// Emit `count` hardlines.
pub(crate) fn hardlines(count: usize) -> Doc<'static> {
    ALLOC.concat((0..count).map(|_| ALLOC.hardline()))
}
