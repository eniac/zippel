#![allow(refining_impl_trait)]
pub use pretty::{DocAllocator, DocBuilder, BoxAllocator};

/// Pretty printing instance
pub trait Pretty <'a, D, A> where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A>;
    fn is_nil(&self) -> bool;
}

impl<'a, D, A> Pretty<'a, D, A> for String where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        self.is_empty()
    }
}

impl<'a, D, A> Pretty<'a, D, A> for &'a str where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        self.is_empty()
    }
}

impl<'a, D, A> Pretty<'a, D, A> for u64 where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A> Pretty<'a, D, A> for usize where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A> Pretty<'a, D, A> for i32 where A: 'a, D: DocAllocator<'a, A> {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A, X, Y> Pretty<'a, D, A> for (X, Y)
    where
        X: Pretty<'a, D, A>,
        Y: Pretty<'a, D, A>,
        A: 'a,
        D: DocAllocator<'a, A> {

    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let (x, y) = self;
        x.pretty(allocator).append(allocator.text(", ")).append(y.pretty(allocator))
    }

    fn is_nil(&self) -> bool {
        self.0.is_nil() && self.1.is_nil()
    }
}
