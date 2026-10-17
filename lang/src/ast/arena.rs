//! The arena expression trees live in: nodes stored flat, children by [`ExpId`].

use std::ops::Index;

use super::exp::{Exp, ExpLiteral};

// ── The arena ───────────────────────────────────────────────────────────

/// Index of an expression in its [`Exprs`] arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpId(u32);

impl ExpId {
    /// The node's position in its arena.
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// The nodes of expression trees, stored flat with their spans. Children are [`ExpId`]s into
/// the same arena, so cloning, dropping and comparing an arena are loops over its nodes, at
/// any depth of the trees in it (issue #252). Equality and ordering ignore spans, as
/// [`Spanned`](super::Spanned)'s do.
///
/// Statements ([`Exp::Let`], [`Exp::Log`], [`Exp::Discard`]) occur exactly in blocks'
/// statement lists. Outside this module nodes are only added, never changed, and each comes
/// after its children: the arena is acyclic by construction, and a node's id names the same tree for
/// the arena's lifetime, which is what per-node side tables such as inferred types rely on.
#[derive(Debug, Clone)]
pub struct Exprs<N: ExpLiteral> {
    // Visible to `ast` for the whole-tree rewrites of leaf data (sizes, type variables) in
    // `exp.rs`, which keep every node's children.
    pub(super) nodes: Vec<Exp<N>>,
    pub(super) spans: Vec<std::ops::Range<usize>>,
}

impl<N: ExpLiteral> Default for Exprs<N> {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            spans: Vec::new(),
        }
    }
}

impl<N: ExpLiteral> Exprs<N> {
    /// An empty arena.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds `node`, whose children must already be in this arena, and returns its id.
    ///
    /// # Panics
    /// If the arena already holds `u32::MAX` nodes.
    pub fn push(&mut self, node: Exp<N>, span: std::ops::Range<usize>) -> ExpId {
        let id = ExpId(u32::try_from(self.nodes.len()).expect("fewer than 2^32 expressions"));
        debug_assert!(node.children().all(|c| c < id), "a child after its parent");
        debug_assert!(
            match &node {
                Exp::Block(stmts, value) => {
                    stmts.iter().all(|s| self[s].is_stmt())
                        && value.is_none_or(|v| !self[v].is_stmt())
                }
                node => node.children().all(|c| !self[c].is_stmt()),
            },
            "statements occur exactly in blocks' statement lists"
        );
        self.nodes.push(node);
        self.spans.push(span);
        id
    }

    /// Number of nodes in the arena.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the arena holds no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// The source span of node `id`.
    pub fn span(&self, id: ExpId) -> &std::ops::Range<usize> {
        &self.spans[id.index()]
    }

    /// Node `id`, for reading the tree under it.
    pub const fn at(&self, id: ExpId) -> ExpRef<'_, N> {
        ExpRef { exprs: self, id }
    }

    /// Moves the nodes of `tree` into this arena and returns the id of its root here.
    pub fn append(&mut self, tree: Expr<N>) -> ExpId {
        let offset = u32::try_from(self.nodes.len()).expect("fewer than 2^32 expressions");
        let shift = |id: ExpId| ExpId(id.0 + offset);
        for (node, span) in tree.exprs.nodes.into_iter().zip(tree.exprs.spans) {
            self.push(node.map_ids(shift), span);
        }
        shift(tree.root)
    }

    /// The tree under `root`, copied into an arena of its own in post-order (children in
    /// source order, before their parent), so equal trees copy to equal arenas.
    pub fn extract(&self, root: ExpId) -> Expr<N> {
        let mut out = Exprs::new();
        let mut copied: Vec<Option<ExpId>> = vec![None; self.nodes.len()];
        // (node, whether its children are copied)
        let mut stack = vec![(root, false)];
        while let Some((id, ready)) = stack.pop() {
            if copied[id.index()].is_some() {
                continue;
            }
            if ready {
                let node = self[id]
                    .clone()
                    .map_ids(|c| copied[c.index()].expect("child first"));
                copied[id.index()] = Some(out.push(node, self.span(id).clone()));
            } else {
                stack.push((id, true));
                let first = stack.len();
                stack.extend(self[id].children().map(|c| (c, false)));
                stack[first..].reverse();
            }
        }
        Expr {
            exprs: out,
            root: copied[root.index()].expect("root copied"),
        }
    }
}

impl<N: ExpLiteral> Index<ExpId> for Exprs<N> {
    type Output = Exp<N>;
    fn index(&self, id: ExpId) -> &Exp<N> {
        &self.nodes[id.index()]
    }
}

impl<N: ExpLiteral + PartialEq> PartialEq for Exprs<N> {
    fn eq(&self, other: &Self) -> bool {
        self.nodes == other.nodes
    }
}

impl<N: ExpLiteral + Eq> Eq for Exprs<N> {}

impl<N: ExpLiteral + PartialOrd> PartialOrd for Exprs<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.nodes.partial_cmp(&other.nodes)
    }
}

impl<N: ExpLiteral + Ord> Ord for Exprs<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.nodes.cmp(&other.nodes)
    }
}

/// One expression tree, owned: an arena holding exactly the tree, and its root.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expr<N: ExpLiteral> {
    /// The tree's nodes.
    pub exprs: Exprs<N>,
    /// The tree's root.
    pub root: ExpId,
}

impl<N: ExpLiteral> Expr<N> {
    /// A one-node tree.
    pub fn leaf(node: Exp<N>, span: std::ops::Range<usize>) -> Self {
        Self::compose([], span, |_| node)
    }

    /// The tree whose root `make` builds from the roots of `children`, which are merged
    /// into one arena in order. Composing children in source order keeps the arena in
    /// post-order, as [`Exprs::extract`] would lay it out.
    pub fn compose(
        children: impl IntoIterator<Item = Expr<N>>,
        span: std::ops::Range<usize>,
        make: impl FnOnce(&[ExpId]) -> Exp<N>,
    ) -> Self {
        let mut exprs = Exprs::new();
        let roots: Vec<ExpId> = children.into_iter().map(|c| exprs.append(c)).collect();
        let root = exprs.push(make(&roots), span);
        Expr { exprs, root }
    }

    /// The root, for reading the tree.
    pub const fn root(&self) -> ExpRef<'_, N> {
        self.exprs.at(self.root)
    }

    /// The root's node.
    pub fn node(&self) -> &Exp<N> {
        &self.exprs[self.root]
    }

    /// The root's source span.
    pub fn span(&self) -> &std::ops::Range<usize> {
        self.exprs.span(self.root)
    }
}

/// A node of an arena, with the arena: what recursive passes walk.
#[derive(Debug)]
pub struct ExpRef<'a, N: ExpLiteral> {
    exprs: &'a Exprs<N>,
    id: ExpId,
}

impl<N: ExpLiteral> Clone for ExpRef<'_, N> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<N: ExpLiteral> Copy for ExpRef<'_, N> {}

impl<'a, N: ExpLiteral> ExpRef<'a, N> {
    /// The node.
    pub fn node(self) -> &'a Exp<N> {
        &self.exprs[self.id]
    }

    /// The node's source span.
    pub fn span(self) -> &'a std::ops::Range<usize> {
        self.exprs.span(self.id)
    }

    /// The node's id in its arena.
    pub const fn id(self) -> ExpId {
        self.id
    }

    /// The arena the node is in.
    pub const fn exprs(self) -> &'a Exprs<N> {
        self.exprs
    }

    /// Node `id` of the same arena, typically a child of this one.
    pub const fn at(self, id: ExpId) -> Self {
        ExpRef {
            exprs: self.exprs,
            id,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::spanned::Spanned;
    use crate::ast::{BinOp, Size};
    use crate::id::Vid;

    #[test]
    fn extract_lays_out_in_post_order() {
        // Composition and extraction agree, so trees compare by structure.
        let var = |x: &str| Expr::leaf(Exp::Var(Spanned::dummy(Vid::from(x))), 0..0);
        let bin = |op, l, r| Expr::compose([l, r], 0..0, |c| Exp::Bin(op, c[0], c[1]));
        let built: Expr<Size> = bin(BinOp::Add, bin(BinOp::Mul, var("a"), var("b")), var("c"));
        let mut arena = Exprs::new();
        let c = arena.push(Exp::Var(Spanned::dummy(Vid::from("c"))), 0..0);
        let a = arena.push(Exp::Var(Spanned::dummy(Vid::from("a"))), 0..0);
        let b = arena.push(Exp::Var(Spanned::dummy(Vid::from("b"))), 0..0);
        let ab = arena.push(Exp::Bin(BinOp::Mul, a, b), 0..0);
        let root = arena.push(Exp::Bin(BinOp::Add, ab, c), 0..0);
        assert_eq!(arena.extract(root), built);
    }
}
