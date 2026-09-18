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
    /// The wrapped AST node.
    pub node: T,
    /// Byte offsets of the node in the source text, as produced by `pest`.
    pub span: std::ops::Range<usize>,
}

impl<T> Spanned<T> {
    /// Attach an explicit source span to a node.
    pub fn new(node: T, span: std::ops::Range<usize>) -> Self {
        Self { node, span }
    }

    /// Wrap a value with a dummy span (0..0). For tests and code that
    /// doesn't care about span information.
    pub fn dummy(node: T) -> Self {
        Self { node, span: 0..0 }
    }

    /// Rewrite the wrapped node while keeping the original span, so a
    /// desugaring step stays attributable to the syntax it came from.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            span: self.span,
        }
    }
}

/// Display delegates to inner T — spans are not part of the textual
/// representation.
impl<T: std::fmt::Display> std::fmt::Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.node.fmt(f)
    }
}

/// Deref to inner T — lets method calls and field accesses on `Spanned<T>`
/// delegate to `T` automatically.
impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.node
    }
}

// ── Equality / ordering / hashing ─────────────────────────────────────
//
// The span is treated as metadata: it is NOT considered for equality,
// hashing, or ordering — only the inner value is. This lets `Spanned<T>`
// be used as a map key that behaves like `T`.
//
// This follows the universal Rust convention for span-attaching wrappers:
//   - rustc_span::Spanned (rustc compiler)
//   - toml::Spanned (serde_spanned)
//   - logosky::utils::Spanned
//   - nightjar_lang::Spanned
//   - aranya_policy_ast::WithSpan
//
// All of these implement PartialEq/Eq/Ord/Hash comparing only the inner
// value, ignoring the span. This is the same pattern Arc<T>, Rc<T>, and
// Cell<T> follow — wrapper types compare inner values, not metadata.

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl<T: Eq> Eq for Spanned<T> {}

impl<T: PartialOrd> PartialOrd for Spanned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.node.partial_cmp(&other.node)
    }
}

impl<T: Ord> Ord for Spanned<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.node.cmp(&other.node)
    }
}

impl<T: std::hash::Hash> std::hash::Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.node.hash(state);
    }
}

// ── Blanket trait impls for Spanned<T> ───────────────────────────────
// These delegate to the inner T's impl, preserving the span. This avoids
// needing per-type impls for every AST node that gets wrapped in Spanned.

impl<T: Clone, N: Clone> share::traversal::ToTraversal1<N> for Spanned<T>
where
    T: share::traversal::ToTraversal1<N>,
{
    type Output<Z> = Spanned<T::Output<Z>>;
    fn traverse1<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        Ok(Spanned::new(self.node.traverse1(f)?, self.span))
    }
}

impl<T: Clone, N: Clone> share::traversal::ToTraversal2<N> for Spanned<T>
where
    T: share::traversal::ToTraversal2<N>,
{
    type Output<Z> = Spanned<T::Output<Z>>;
    fn traverse2<Z: Clone, E>(
        self,
        f: &mut dyn FnMut(N) -> Result<Z, E>,
    ) -> Result<Self::Output<Z>, E> {
        Ok(Spanned::new(self.node.traverse2(f)?, self.span))
    }
}

impl<T: crate::id::TidSubst> crate::id::TidSubst for Spanned<T> {
    fn tid_subst(&mut self, from: &crate::id::Tid, to: &crate::id::Tid) {
        self.node.tid_subst(from, to);
    }
}

impl<T: crate::ast::FreeVars> crate::ast::FreeVars for Spanned<T> {
    fn freevars(&self) -> share::Set<crate::id::Vid> {
        self.node.freevars()
    }
}

impl<T: Clone, N: Clone> crate::typ::RangeTraversal<N> for Spanned<T>
where
    T: crate::typ::RangeTraversal<N>,
{
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(crate::typ::Range<N>) -> Result<crate::typ::Range<N>, E>,
    ) -> Result<Self, E> {
        Ok(Spanned::new(self.node.range_traverse(f)?, self.span))
    }
}

impl<T: Clone, N: Clone> crate::typ::TypeInline<N> for Spanned<T>
where
    T: crate::typ::TypeInline<N>,
{
    fn type_inline(self, ctx: &share::Ctx<crate::id::Tid, crate::typ::GTyp<N>>) -> Self {
        Spanned::new(self.node.type_inline(ctx), self.span)
    }
}
