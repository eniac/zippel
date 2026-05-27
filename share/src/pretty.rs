#![allow(refining_impl_trait)]
pub use pretty::{BoxAllocator, DocAllocator, DocBuilder};

/// Pretty printing instance
pub trait Pretty<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A>;
    fn is_nil(&self) -> bool;
}

impl<'a, D, A> Pretty<'a, D, A> for String
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(self.to_string())
    }

    fn is_nil(&self) -> bool {
        self.is_empty()
    }
}

impl<'a, D, A> Pretty<'a, D, A> for &'a str
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(self.to_string())
    }

    fn is_nil(&self) -> bool {
        self.is_empty()
    }
}

impl<'a, D, A> Pretty<'a, D, A> for u64
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A> Pretty<'a, D, A> for usize
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, D, A> Pretty<'a, D, A> for i32
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
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
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        let (x, y) = self;
        x.pretty(allocator)
            .append(allocator.text(", "))
            .append(y.pretty(allocator))
    }

    fn is_nil(&self) -> bool {
        self.0.is_nil() && self.1.is_nil()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pretty_string() {
        let allocator = BoxAllocator;
        let s = "hello".to_string();
        let doc: DocBuilder<'_, BoxAllocator, ()> = s.pretty(&allocator);
        let rendered = format!("{}", doc.1.pretty(80));
        assert!(rendered.contains("hello"));
    }

    #[test]
    fn test_pretty_str() {
        let allocator = BoxAllocator;
        let s = "world";
        let doc: DocBuilder<'_, BoxAllocator, ()> = s.pretty(&allocator);
        let rendered = format!("{}", doc.1.pretty(80));
        assert!(rendered.contains("world"));
    }

    #[test]
    fn test_pretty_u64() {
        let allocator = BoxAllocator;
        let n = 42u64;
        let doc: DocBuilder<'_, BoxAllocator, ()> = n.pretty(&allocator);
        let rendered = format!("{}", doc.1.pretty(80));
        assert!(rendered.contains("42"));
    }

    #[test]
    fn test_pretty_usize() {
        let allocator = BoxAllocator;
        let n = 123usize;
        let doc: DocBuilder<'_, BoxAllocator, ()> = n.pretty(&allocator);
        let rendered = format!("{}", doc.1.pretty(80));
        assert!(rendered.contains("123"));
    }

    #[test]
    fn test_pretty_i32() {
        let allocator = BoxAllocator;
        let n = -456i32;
        let doc: DocBuilder<'_, BoxAllocator, ()> = n.pretty(&allocator);
        let rendered = format!("{}", doc.1.pretty(80));
        assert!(rendered.contains("-456"));
    }

    #[test]
    fn test_pretty_tuple() {
        let allocator = BoxAllocator;
        let t = (42usize, 17usize);
        let doc: DocBuilder<'_, BoxAllocator, ()> = t.pretty(&allocator);
        let rendered = format!("{}", doc.1.pretty(80));
        assert!(rendered.contains("42"));
        assert!(rendered.contains("17"));
    }

    #[test]
    fn test_is_nil_string_empty() {
        let s = String::new();
        assert!(<String as Pretty<BoxAllocator, ()>>::is_nil(&s));
    }

    #[test]
    fn test_is_nil_string_nonempty() {
        let s = "hello".to_string();
        assert!(!<String as Pretty<BoxAllocator, ()>>::is_nil(&s));
    }

    #[test]
    fn test_is_nil_str_empty() {
        let s = "";
        assert!(<&str as Pretty<BoxAllocator, ()>>::is_nil(&s));
    }

    #[test]
    fn test_is_nil_str_nonempty() {
        let s = "world";
        assert!(!<&str as Pretty<BoxAllocator, ()>>::is_nil(&s));
    }

    #[test]
    fn test_is_nil_u64() {
        let n = 0u64;
        assert!(!<u64 as Pretty<BoxAllocator, ()>>::is_nil(&n));
        let n = 42u64;
        assert!(!<u64 as Pretty<BoxAllocator, ()>>::is_nil(&n));
    }

    #[test]
    fn test_is_nil_usize() {
        let n = 0usize;
        assert!(!<usize as Pretty<BoxAllocator, ()>>::is_nil(&n));
        let n = 123usize;
        assert!(!<usize as Pretty<BoxAllocator, ()>>::is_nil(&n));
    }

    #[test]
    fn test_is_nil_i32() {
        let n = 0i32;
        assert!(!<i32 as Pretty<BoxAllocator, ()>>::is_nil(&n));
        let n = -456i32;
        assert!(!<i32 as Pretty<BoxAllocator, ()>>::is_nil(&n));
    }

    #[test]
    fn test_is_nil_tuple_both_empty() {
        let t = ("".to_string(), "".to_string());
        assert!(<(String, String) as Pretty<BoxAllocator, ()>>::is_nil(&t));
    }

    #[test]
    fn test_is_nil_tuple_one_empty() {
        let t = ("hello".to_string(), "".to_string());
        assert!(!<(String, String) as Pretty<BoxAllocator, ()>>::is_nil(&t));
    }

    #[test]
    fn test_is_nil_tuple_none_empty() {
        let t = ("hello".to_string(), "world".to_string());
        assert!(!<(String, String) as Pretty<BoxAllocator, ()>>::is_nil(&t));
    }
}
