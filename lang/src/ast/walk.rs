//! The shape of expression nodes, described once: which children a node has
//! ([`Exp::children`], [`Exp::for_each_child_mut`]), and which variables each child sees bound
//! ([`ExpRef::walk`]). Passes that don't depend on a node's meaning use these rather than
//! matching every [`Exp`] variant, so a new variant, or a new binder, is a change here only.
//! Walks keep their work on the heap, so they take bounded stack at any depth (issue #252).

use std::collections::HashMap;

use super::exp::{Exp, ExpLiteral, Exps};
use super::spanned::Spanned;
use super::{ExpId, ExpRef};
use crate::id::Vid;

/// The children of a node, in source order (see [`Exp::children`]).
pub struct Children<'a>(Inner<'a>);

enum Inner<'a> {
    Fixed(std::iter::Flatten<std::array::IntoIter<Option<ExpId>, 2>>),
    /// A list, then possibly one more: a block's statements and value.
    List(
        std::iter::Chain<
            std::iter::Copied<std::slice::Iter<'a, ExpId>>,
            std::option::IntoIter<ExpId>,
        >,
    ),
    Record(Box<dyn Iterator<Item = ExpId> + 'a>),
}

impl Iterator for Children<'_> {
    type Item = ExpId;

    fn next(&mut self) -> Option<ExpId> {
        match &mut self.0 {
            Inner::Fixed(ids) => ids.next(),
            Inner::List(ids) => ids.next(),
            Inner::Record(ids) => ids.next(),
        }
    }
}

impl<N: ExpLiteral> Exp<N> {
    /// The direct subexpressions of this node, in source order; a record's fields in field
    /// order.
    pub fn children<'a>(&'a self) -> Children<'a> {
        let fixed = |a, b| Children(Inner::Fixed([a, b].into_iter().flatten()));
        let list = |ids: &'a Exps, last: Option<ExpId>| {
            Children(Inner::List(ids.0.iter().copied().chain(last)))
        };
        match self {
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => fixed(None, None),
            Exp::Random(_, x) | Exp::Challenge(_, x) => {
                fixed(x.as_ref().and_then(|x| x.values()).copied(), None)
            }
            Exp::App(_, args) | Exp::Vec(args) => list(args, None),
            Exp::Block(stmts, tail) => list(stmts, *tail),
            Exp::Map(a, _, b)
            | Exp::Bin(_, a, b)
            | Exp::Pair(a, b)
            | Exp::Ram(a, b)
            | Exp::SetRecord(a, _, b) => fixed(Some(*a), Some(*b)),
            Exp::Interpolate(a, b) => fixed(*a, Some(*b)),
            Exp::Evaluate(a, _, b) => fixed(Some(*a), *b),
            Exp::Neg(a)
            | Exp::Coef(a)
            | Exp::Poly(a)
            | Exp::Mle(a)
            | Exp::Reduce(_, a)
            | Exp::Verify(a)
            | Exp::Fun(_, a)
            | Exp::Proj(a, _)
            | Exp::Let(_, a)
            | Exp::Log(_, a)
            | Exp::Discard(a) => fixed(Some(*a), None),
            Exp::Record(fields) => {
                Children(Inner::Record(Box::new(fields.iter().map(|(_, e)| *e))))
            }
        }
    }

    /// Calls `f` on each child id, in [`Exp::children`] order, to read or replace it.
    pub fn for_each_child_mut(&mut self, mut f: impl FnMut(&mut ExpId)) {
        match self {
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => {}
            Exp::Random(_, x) | Exp::Challenge(_, x) => {
                if let Some(Spanned {
                    node: super::Exclusion::Values(v),
                    ..
                }) = x
                {
                    f(v);
                }
            }
            Exp::App(_, args) | Exp::Vec(args) => args.0.iter_mut().for_each(f),
            Exp::Block(stmts, tail) => {
                stmts.0.iter_mut().for_each(&mut f);
                tail.iter_mut().for_each(f);
            }
            Exp::Map(a, _, b)
            | Exp::Bin(_, a, b)
            | Exp::Pair(a, b)
            | Exp::Ram(a, b)
            | Exp::SetRecord(a, _, b) => {
                f(a);
                f(b);
            }
            Exp::Interpolate(a, b) => {
                a.iter_mut().for_each(&mut f);
                f(b);
            }
            Exp::Evaluate(a, _, b) => {
                f(a);
                b.iter_mut().for_each(f);
            }
            Exp::Neg(a)
            | Exp::Coef(a)
            | Exp::Poly(a)
            | Exp::Mle(a)
            | Exp::Reduce(_, a)
            | Exp::Verify(a)
            | Exp::Fun(_, a)
            | Exp::Proj(a, _)
            | Exp::Let(_, a)
            | Exp::Log(_, a)
            | Exp::Discard(a) => f(a),
            Exp::Record(fields) => fields.modify(|_, e| f(e)),
        }
    }

    /// The same node with each child id replaced by `f` of it, in [`Exp::children`] order.
    #[must_use]
    pub fn map_ids(mut self, mut f: impl FnMut(ExpId) -> ExpId) -> Self {
        self.for_each_child_mut(|id| *id = f(*id));
        self
    }
}

/// One step of an [`ExpRef::walk`].
pub enum Visit<'a, N: ExpLiteral> {
    /// A node, before its children.
    Enter(ExpRef<'a, N>),
    /// A variable comes into scope. It stays bound until the [`Visit::Leave`] of the node that
    /// binds it: the rest of a block for a statement, the body for a comprehension or `fun`.
    Bind(&'a Spanned<Vid>),
    /// A node, after its children.
    Leave(ExpRef<'a, N>),
}

/// The walk of a tree: each node entered and left, its children in between in evaluation
/// order, with the variables bound at each point (see [`ExpRef::walk`]).
pub struct Walk<'a, N: ExpLiteral> {
    root: ExpRef<'a, N>,
    todo: Vec<Step<'a>>,
    bound: Vec<&'a Spanned<Vid>>,
    /// For each bound name, its positions in `bound`, innermost last.
    by_name: HashMap<&'a Vid, Vec<usize>>,
}

enum Step<'a> {
    Enter(ExpId),
    /// The children of a node just entered, still to be scheduled.
    Expand(ExpId),
    Bind(&'a Spanned<Vid>),
    /// Leave a node, unbinding back to `bound.len() == .1`.
    Leave(ExpId, usize),
}

impl<'a, N: ExpLiteral> ExpRef<'a, N> {
    /// Walks the tree under this node: each node is entered, then its children are walked in
    /// evaluation order, then it is left. A comprehension's domain comes before its binder
    /// and body; a block's statements come in order, each binding after its value and only
    /// when something follows it. [`Walk::resolve`] answers which binding a name refers to.
    pub fn walk(self) -> Walk<'a, N> {
        Walk {
            root: self,
            todo: vec![Step::Enter(self.id())],
            bound: Vec::new(),
            by_name: HashMap::new(),
        }
    }

    /// This node and all its descendants, in pre-order.
    pub fn subexps(self) -> impl Iterator<Item = ExpRef<'a, N>> {
        let mut todo = vec![self.id()];
        std::iter::from_fn(move || {
            let e = self.at(todo.pop()?);
            let first = todo.len();
            todo.extend(e.node().children());
            todo[first..].reverse();
            Some(e)
        })
    }
}

impl<'a, N: ExpLiteral> Walk<'a, N> {
    /// Variables bound by the nodes the walk is inside, outermost first.
    pub fn bound(&self) -> &[&'a Spanned<Vid>] {
        &self.bound
    }

    /// The innermost binding of `name` the walk is inside, as a position in [`Self::bound`].
    pub fn resolve(&self, name: &Vid) -> Option<usize> {
        self.by_name.get(name).and_then(|at| at.last().copied())
    }

    /// Whether the walk is inside a binding of `name`.
    pub fn is_bound(&self, name: &Vid) -> bool {
        self.resolve(name).is_some()
    }

    /// Called right after a [`Visit::Enter`]: skips that node's children, so its
    /// [`Visit::Leave`] comes next.
    pub fn skip_children(&mut self) {
        if let Some(Step::Expand(id)) = self.todo.last() {
            let id = *id;
            *self.todo.last_mut().expect("just checked") = Step::Leave(id, self.bound.len());
        }
    }

    /// Schedules the children of `id`, in evaluation order, before leaving it.
    fn expand(&mut self, id: ExpId) {
        let first = self.todo.len();
        self.todo.push(Step::Leave(id, self.bound.len()));
        let todo = &mut self.todo;
        match self.root.at(id).node() {
            Exp::Map(body, var, domain) => {
                todo.extend([Step::Enter(*domain), Step::Bind(var), Step::Enter(*body)]);
            }
            Exp::Fun(params, body) => {
                todo.extend(params.iter().map(Step::Bind));
                todo.push(Step::Enter(*body));
            }
            Exp::Block(stmts, tail) => {
                for (i, &stmt) in stmts.0.iter().enumerate() {
                    todo.push(Step::Enter(stmt));
                    if let Some(x) = self.root.at(stmt).node().binder()
                        && (i + 1 < stmts.len() || tail.is_some())
                    {
                        todo.push(Step::Bind(x));
                    }
                }
                todo.extend(tail.map(Step::Enter));
            }
            node => todo.extend(node.children().map(Step::Enter)),
        }
        // The `Leave` stays first, so it comes last.
        self.todo[first + 1..].reverse();
    }

    fn unbind_to(&mut self, len: usize) {
        while self.bound.len() > len {
            let x = self.bound.pop().expect("longer than len");
            let at = self.by_name.get_mut(&x.node).expect("bound");
            at.pop();
            if at.is_empty() {
                self.by_name.remove(&x.node);
            }
        }
    }
}

impl<'a, N: ExpLiteral> Iterator for Walk<'a, N> {
    type Item = Visit<'a, N>;

    fn next(&mut self) -> Option<Visit<'a, N>> {
        loop {
            match self.todo.pop()? {
                Step::Enter(id) => {
                    self.todo.push(Step::Expand(id));
                    return Some(Visit::Enter(self.root.at(id)));
                }
                Step::Expand(id) => self.expand(id),
                Step::Bind(x) => {
                    self.by_name
                        .entry(&x.node)
                        .or_default()
                        .push(self.bound.len());
                    self.bound.push(x);
                    return Some(Visit::Bind(x));
                }
                Step::Leave(id, len) => {
                    self.unbind_to(len);
                    return Some(Visit::Leave(self.root.at(id)));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp, Exclusion, Exprs, Exps, Size, UExp, UExpr};
    use crate::id::Tid;
    use share::Ctx;

    /// One node of every variant with children, over distinct leaves.
    fn every_parent() -> (Exprs<Size>, Vec<ExpId>) {
        let mut exprs = Exprs::new();
        let leaf = |exprs: &mut Exprs<Size>| exprs.push(UExp::Unit, 0..0);
        let [a, b, c] = [leaf(&mut exprs), leaf(&mut exprs), leaf(&mut exprs)];
        let x = || Spanned::new(Vid::new("x"), 0..0);
        let t = || Spanned::new(Tid::new("F"), 0..0);
        let field = |f: &str| Spanned::new(f.to_string(), 0..0);
        let mut record = Ctx::new();
        record.insert(&field("q"), &b);
        record.insert(&field("p"), &a);
        let nodes = [
            UExp::App(x(), Exps(vec![a, b, c])),
            UExp::Interpolate(Some(a), b),
            UExp::Interpolate(None, b),
            UExp::Poly(a),
            UExp::Evaluate(a, None, Some(b)),
            UExp::Evaluate(a, None, None),
            UExp::Coef(a),
            UExp::Mle(a),
            UExp::Vec(Exps(vec![c, a])),
            UExp::Bin(BinOp::Add, a, b),
            UExp::Neg(a),
            UExp::Map(a, x(), b),
            UExp::Reduce(BinOp::Mul, a),
            UExp::Ram(a, b),
            UExp::Pair(a, b),
            UExp::Random(t(), Some(Spanned::new(Exclusion::Values(c), 0..0))),
            UExp::Challenge(t(), None),
            UExp::Let(x(), a),
            UExp::Log(x(), b),
            UExp::Discard(c),
            UExp::Verify(a),
            UExp::Fun(vec![x()], a),
            UExp::Record(record),
            UExp::Proj(a, field("p")),
            UExp::SetRecord(a, field("p"), b),
        ];
        let mut ids: Vec<ExpId> = nodes.into_iter().map(|n| exprs.push(n, 0..0)).collect();
        // A block of the statements above, then `a`.
        let stmts = ids
            .iter()
            .copied()
            .filter(|&id| exprs[id].is_stmt())
            .collect();
        ids.push(exprs.push(UExp::Block(Exps(stmts), Some(a)), 0..0));
        (exprs, ids)
    }

    #[test]
    fn children_and_mutable_children_agree() {
        let (exprs, ids) = every_parent();
        for id in ids {
            let node = &exprs[id];
            let children: Vec<ExpId> = node.children().collect();
            assert!(
                !children.is_empty() || matches!(node, Exp::Challenge(..)),
                "{node:?}"
            );
            let mut seen = Vec::new();
            node.clone().for_each_child_mut(|c| seen.push(*c));
            assert_eq!(children, seen, "{node:?}");
            // Replacing every child by itself rebuilds the node.
            assert_eq!(&node.clone().map_ids(|c| c), node);
            // The walk enters exactly the children, one level down (a map's domain before its body).
            let mut depth = 0;
            let mut entered = Vec::new();
            for visit in exprs.at(id).walk() {
                match visit {
                    Visit::Enter(e) => {
                        if depth == 1 {
                            entered.push(e.id());
                        }
                        depth += 1;
                    }
                    Visit::Leave(_) => depth -= 1,
                    Visit::Bind(_) => {}
                }
            }
            let mut expected = children;
            if matches!(node, Exp::Map(..)) {
                expected.reverse();
            }
            assert_eq!(entered, expected, "{node:?}");
        }
    }

    fn tree(body: &str) -> UExpr {
        let src = format!("fn f<F: Field>(instance a: F) -> F {{ {body} }}");
        let (mut decls, errors) = crate::parser::parse_decls(&src);
        assert!(errors.is_empty(), "{errors:?}");
        decls.remove(0).node.body.body().expect("a body")
    }

    /// Each variable read, in walk order, with the binding it resolves to.
    fn reads(tree: &UExpr) -> Vec<(String, Option<usize>)> {
        let mut walk = tree.root().walk();
        let mut out = Vec::new();
        while let Some(visit) = walk.next() {
            if let Visit::Enter(e) = visit
                && let Exp::Var(x) = e.node()
            {
                out.push((x.node.0.to_string(), walk.resolve(&x.node)));
            }
        }
        out
    }

    #[test]
    fn walk_resolves_names_in_evaluation_order() {
        let t = tree("let x = a; let y = [x * z for z in [x, a]]; let x = y; x");
        let expected = [
            ("a", None),
            // The comprehension's domain, then its body with `z` bound.
            ("x", Some(0)),
            ("a", None),
            ("x", Some(0)),
            ("z", Some(1)),
            // `z` is out of scope after the comprehension; `y` takes its place.
            ("y", Some(1)),
            // The second `x` shadows the first.
            ("x", Some(2)),
        ];
        let expected: Vec<_> = expected.iter().map(|(n, i)| (n.to_string(), *i)).collect();
        assert_eq!(reads(&t), expected);
        let t = tree("let p = a; fun(p, q) => p * q * a");
        assert_eq!(
            reads(&t),
            [("a", None), ("p", Some(1)), ("q", Some(2)), ("a", None)]
                .map(|(n, i)| (n.to_string(), i))
        );
    }

    #[test]
    fn a_binding_with_nothing_after_it_binds_nothing() {
        let t = tree("let u = a; u <- a;");
        let binds: Vec<_> = t
            .root()
            .walk()
            .filter_map(|v| match v {
                Visit::Bind(x) => Some(x.node.0.to_string()),
                _ => None,
            })
            .collect();
        assert_eq!(binds, ["u"]);
    }

    #[test]
    fn skip_children_goes_to_leave() {
        let t = tree("[a for z in [a]]");
        let mut walk = t.root().walk();
        assert!(matches!(walk.next(), Some(Visit::Enter(e)) if matches!(e.node(), Exp::Map(..))));
        walk.skip_children();
        assert!(matches!(walk.next(), Some(Visit::Leave(e)) if matches!(e.node(), Exp::Map(..))));
        assert!(walk.next().is_none());
    }

    #[test]
    fn walks_take_no_stack_per_level() {
        // Deeper than any stack would hold recursion over.
        let mut exprs: Exprs<Size> = Exprs::new();
        let mut e = exprs.push(UExp::Unit, 0..0);
        for _ in 0..1_000_000 {
            e = exprs.push(UExp::Neg(e), 0..0);
        }
        assert_eq!(exprs.at(e).walk().count(), 2_000_002);
        assert_eq!(exprs.at(e).subexps().count(), 1_000_001);
    }
}
