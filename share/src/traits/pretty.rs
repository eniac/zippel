#![allow(refining_impl_trait)]
pub use pretty::{BoxAllocator, DocAllocator, DocBuilder};

/// Pretty printing instance
pub trait Pretty <'a, D, A> where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A>;
    fn is_nil(&self) -> bool;
}

impl Pretty<'_, BoxAllocator, ()> for String {
    fn pretty(self, allocator: &BoxAllocator) -> DocBuilder<'_, BoxAllocator, ()> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        self.is_empty()
    }
}

impl<'a> Pretty<'_, BoxAllocator, ()> for &'a str {
    fn pretty(self, allocator: &BoxAllocator) -> DocBuilder<'_, BoxAllocator, ()> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        self.is_empty()
    }
}
