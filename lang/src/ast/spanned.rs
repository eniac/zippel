/// A value paired with its source span.
///
/// Used by the parser to attach byte-offset spans to AST nodes for
/// comment-preserving formatting and source-location error reporting.
///
/// Does NOT derive `PartialEq` — spans are source positions that differ
/// between formatted and original text. Compare `.node` for structural
/// equality.
#[derive(Debug, Clone)]
pub struct Spanned<T> {
    pub node: T,
    pub span: std::ops::Range<usize>,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: std::ops::Range<usize>) -> Self {
        Self { node, span }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            span: self.span,
        }
    }
}
