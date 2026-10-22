//! The shape of expression nodes, described once: which children a node has
//! ([`Exp::for_each_child`], [`Exp::for_each_child_mut`]), and where each variable's scope starts
//! and ends ([`ExpRef::walk`]; [`InScope`] resolves names from those events). Passes that don't depend on a node's meaning use these rather than
//! matching every [`Exp`] variant, so a new variant, or a new binder, is a change here only.
//! Walks keep their work on the heap, so they take bounded stack at any depth (issue #252).

use std::collections::HashMap;

use super::exp::{Exp, ExpLiteral};
use super::spanned::Spanned;
use super::{ExpId, ExpRef, Stmt};
use crate::id::Vid;

/// Calls `$f` on a reference to each child id of `$node`, in source order; a record's fields
/// in field order. With `mut`, the references are mutable. The one description of which
/// fields of a node are children.
macro_rules! each_child {
    ($node:expr, $f:ident $(, $m:tt)?) => {
        match $node {
            Exp::Lit(_) | Exp::Unit | Exp::Var(_) | Exp::Range(_) => {}
            Exp::Random(_, x) | Exp::Challenge(_, x) => {
                if let Some(Spanned {
                    node: super::Exclusion::Values(v),
                    ..
                }) = x
                {
                    $f(v);
                }
            }
            Exp::App(_, args) | Exp::Vec(args) => {
                for a in &$($m)? args.0 {
                    $f(a);
                }
            }
            Exp::Block(block) => {
                for stmt in &$($m)? block.stmts {
                    match &$($m)? stmt.node {
                        Stmt::Let(_, v) | Stmt::Log(_, v) | Stmt::Discard(v) => $f(v),
                    }
                }
                if let Some(tail) = &$($m)? block.tail {
                    $f(tail);
                }
            }
            Exp::Map(a, _, b)
            | Exp::Bin(_, a, b)
            | Exp::Pair(a, b)
            | Exp::Ram(a, b)
            | Exp::SetRecord(a, _, b) => {
                $f(a);
                $f(b);
            }
            Exp::Interpolate(a, b) => {
                if let Some(a) = a {
                    $f(a);
                }
                $f(b);
            }
            Exp::Evaluate(a, _, b) => {
                $f(a);
                if let Some(b) = b {
                    $f(b);
                }
            }
            Exp::Neg(a)
            | Exp::Coef(a)
            | Exp::Poly(a)
            | Exp::Mle(a)
            | Exp::Reduce(_, a)
            | Exp::Verify(a)
            | Exp::Fun(_, a)
            | Exp::Proj(a, _) => $f(a),
            Exp::Record(fields) => each_child!(@record fields, $f $(, $m)?),
        }
    };
    (@record $fields:ident, $f:ident) => {
        for (_, e) in $fields.iter() {
            $f(e);
        }
    };
    (@record $fields:ident, $f:ident, mut) => {
        $fields.modify(|_, e| $f(e))
    };
}

impl<N: ExpLiteral> Exp<N> {
    /// Calls `f` on each direct subexpression of this node, in source order; a record's fields
    /// in field order.
    pub fn for_each_child(&self, mut f: impl FnMut(ExpId)) {
        let mut f = |id: &ExpId| f(*id);
        each_child!(self, f);
    }

    /// Calls `f` on each child id, in [`Exp::for_each_child`] order, to read or replace it.
    pub fn for_each_child_mut(&mut self, mut f: impl FnMut(&mut ExpId)) {
        each_child!(self, f, mut);
    }

    /// The same node with each child id replaced by `f` of it, in [`Exp::for_each_child`] order.
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
    /// A statement, before its value is evaluated.
    EnterStmt(&'a Spanned<Stmt>),
    /// A statement, after its value is evaluated, before its binder comes into scope.
    LeaveStmt(&'a Spanned<Stmt>),
    /// A variable comes into scope, bound as [`Bound`] says. A matching [`Visit::Unbind`]
    /// ends it.
    Bind(&'a Spanned<Vid>, Bound<'a, N>),
    /// A variable goes out of scope: its block, comprehension or `fun` is being left.
    /// Bindings end innermost first, before that node's [`Visit::Leave`].
    Unbind(&'a Spanned<Vid>),
    /// A node, after its children.
    Leave(ExpRef<'a, N>),
}

/// What a [`Visit::Bind`]'s variable is bound to.
pub enum Bound<'a, N: ExpLiteral> {
    /// A statement's value: `let x = e;` or `x <- e;` binds `x` to `e`.
    Value(ExpRef<'a, N>),
    /// Each element of a comprehension's domain: `[body for x in domain]`.
    Element {
        /// The comprehension.
        map: ExpRef<'a, N>,
        /// Its domain.
        domain: ExpRef<'a, N>,
    },
    /// A variable of the polynomial a `fun` builds: `fun(x, y) => body`.
    Param(ExpRef<'a, N>),
}

/// The walk of a tree: each node entered and left, its children in between in evaluation
/// order, with variables bound and unbound where their scopes start and end (see
/// [`ExpRef::walk`]).
pub struct Walk<'a, N: ExpLiteral> {
    root: ExpRef<'a, N>,
    todo: Vec<Step<'a>>,
}

enum Step<'a> {
    Enter(ExpId),
    EnterStmt(&'a Spanned<Stmt>),
    LeaveStmt(&'a Spanned<Stmt>),
    /// The children of a node just entered, still to be scheduled.
    Expand(ExpId),
    Bind(&'a Spanned<Vid>, BoundStep),
    Unbind(&'a Spanned<Vid>),
    Leave(ExpId),
}

/// A [`Bound`] by node ids, while it waits in the walk's work stack.
#[derive(Clone, Copy)]
enum BoundStep {
    Value(ExpId),
    Element { map: ExpId, domain: ExpId },
    Param(ExpId),
}

impl<'a, N: ExpLiteral> ExpRef<'a, N> {
    /// Walks the tree under this node: each node is entered, then its children are walked in
    /// evaluation order, then it is left. A comprehension's domain comes before its binder
    /// and body; a block's statements come in order, each with statement enter/leave events
    /// around its value, binding afterward only when something follows it. Each binding ends
    /// when the node that made it is left. [`InScope`] resolves names from these events.
    pub fn walk(self) -> Walk<'a, N> {
        Walk {
            root: self,
            todo: vec![Step::Enter(self.id())],
        }
    }

    /// This expression and all its subexpressions, in pre-order. Use [`Self::walk`] to also
    /// visit the statements a block owns.
    pub fn subexps(self) -> impl Iterator<Item = ExpRef<'a, N>> {
        let mut todo = vec![self.id()];
        std::iter::from_fn(move || {
            let e = self.at(todo.pop()?);
            let first = todo.len();
            e.node().for_each_child(|c| todo.push(c));
            todo[first..].reverse();
            Some(e)
        })
    }
}

impl<N: ExpLiteral> Walk<'_, N> {
    /// Called right after a [`Visit::Enter`]: skips that node's children, so its
    /// [`Visit::Leave`] comes next.
    pub fn skip_children(&mut self) {
        if let Some(Step::Expand(id)) = self.todo.last() {
            let id = *id;
            *self.todo.last_mut().expect("just checked") = Step::Leave(id);
        }
    }

    /// Schedules the children of `id`, in evaluation order, before leaving it. The variables
    /// it binds are unbound, innermost first, just before it is left.
    fn expand(&mut self, id: ExpId) {
        let first = self.todo.len();
        self.todo.push(Step::Leave(id));
        let todo = &mut self.todo;
        match self.root.at(id).node() {
            Exp::Map(body, var, domain) => {
                let bound = BoundStep::Element {
                    map: id,
                    domain: *domain,
                };
                todo.extend([
                    Step::Enter(*domain),
                    Step::Bind(var, bound),
                    Step::Enter(*body),
                    Step::Unbind(var),
                ]);
            }
            Exp::Fun(params, body) => {
                todo.extend(params.iter().map(|x| Step::Bind(x, BoundStep::Param(id))));
                todo.push(Step::Enter(*body));
                todo.extend(params.iter().rev().map(Step::Unbind));
            }
            Exp::Block(block) => {
                let mut bound = Vec::new();
                for (i, stmt) in block.stmts.iter().enumerate() {
                    todo.extend([
                        Step::EnterStmt(stmt),
                        Step::Enter(stmt.node.value()),
                        Step::LeaveStmt(stmt),
                    ]);
                    if let Some(x) = stmt.node.binder()
                        && block.is_followed(i)
                    {
                        todo.push(Step::Bind(x, BoundStep::Value(stmt.node.value())));
                        bound.push(x);
                    }
                }
                todo.extend(block.tail.map(Step::Enter));
                todo.extend(bound.into_iter().rev().map(Step::Unbind));
            }
            node => node.for_each_child(|c| todo.push(Step::Enter(c))),
        }
        // The `Leave` stays first, so it comes last.
        self.todo[first + 1..].reverse();
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
                Step::EnterStmt(stmt) => return Some(Visit::EnterStmt(stmt)),
                Step::LeaveStmt(stmt) => return Some(Visit::LeaveStmt(stmt)),
                Step::Bind(x, bound) => {
                    let at = |id| self.root.at(id);
                    let bound = match bound {
                        BoundStep::Value(value) => Bound::Value(at(value)),
                        BoundStep::Element { map, domain } => Bound::Element {
                            map: at(map),
                            domain: at(domain),
                        },
                        BoundStep::Param(fun) => Bound::Param(at(fun)),
                    };
                    return Some(Visit::Bind(x, bound));
                }
                Step::Unbind(x) => return Some(Visit::Unbind(x)),
                Step::Leave(id) => return Some(Visit::Leave(self.root.at(id))),
            }
        }
    }
}

/// The variables in scope at a point of a walk, each with what a pass records about it. A pass
/// feeds it the walk's [`Visit::Bind`] and [`Visit::Unbind`]; a name resolves to its innermost
/// binding.
pub struct InScope<'a, T> {
    /// The bindings in scope with their records, outermost first.
    bindings: Vec<(&'a Spanned<Vid>, T)>,
    /// For each bound name, its positions in `bindings`, innermost last.
    by_name: HashMap<&'a Vid, Vec<usize>>,
}

impl<T> Default for InScope<'_, T> {
    fn default() -> Self {
        InScope {
            bindings: Vec::new(),
            by_name: HashMap::new(),
        }
    }
}

impl<'a, T> InScope<'a, T> {
    /// No variables in scope.
    pub fn new() -> Self {
        Self::default()
    }

    /// Brings `x` into scope with `record`, shadowing any outer binding of its name.
    pub fn bind(&mut self, x: &'a Spanned<Vid>, record: T) {
        self.by_name
            .entry(&x.node)
            .or_default()
            .push(self.bindings.len());
        self.bindings.push((x, record));
    }

    /// Ends the innermost binding, which is `x`, and returns its record.
    ///
    /// # Panics
    /// If nothing is in scope.
    pub fn unbind(&mut self, x: &Spanned<Vid>) -> T {
        let (y, record) = self.bindings.pop().expect("a binding to end");
        debug_assert!(std::ptr::eq(x, y), "bindings end innermost first");
        let at = self.by_name.get_mut(&y.node).expect("bound");
        at.pop();
        if at.is_empty() {
            self.by_name.remove(&y.node);
        }
        record
    }

    /// The record of the binding `name` refers to.
    pub fn get(&self, name: &Vid) -> Option<&T> {
        let at = *self.by_name.get(name)?.last()?;
        Some(&self.bindings[at].1)
    }

    /// The record of the binding `name` refers to, to update it.
    pub fn get_mut(&mut self, name: &Vid) -> Option<&mut T> {
        let at = *self.by_name.get(name)?.last()?;
        Some(&mut self.bindings[at].1)
    }

    /// The bindings in scope, outermost first.
    pub fn iter(&self) -> impl Iterator<Item = (&'a Spanned<Vid>, &T)> {
        self.bindings.iter().map(|(x, record)| (*x, record))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp, Block, Exclusion, Exprs, Exps, Size, UExp, UExpr};
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
            UExp::Verify(a),
            UExp::Fun(vec![x()], a),
            UExp::Record(record),
            UExp::Proj(a, field("p")),
            UExp::SetRecord(a, field("p"), b),
        ];
        let mut ids: Vec<ExpId> = nodes.into_iter().map(|n| exprs.push(n, 0..0)).collect();
        let stmts = vec![Stmt::Let(x(), a), Stmt::Log(x(), b), Stmt::Discard(c)]
            .into_iter()
            .map(Spanned::dummy)
            .collect();
        ids.push(exprs.push(
            UExp::Block(Block {
                stmts,
                tail: Some(a),
            }),
            0..0,
        ));
        (exprs, ids)
    }

    #[test]
    fn children_and_mutable_children_agree() {
        let (exprs, ids) = every_parent();
        for id in ids {
            let node = &exprs[id];
            let mut children = Vec::new();
            node.for_each_child(|c| children.push(c));
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
                    Visit::Bind(..)
                    | Visit::Unbind(_)
                    | Visit::EnterStmt(_)
                    | Visit::LeaveStmt(_) => {}
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

    /// Each variable read, in walk order, with the binding it resolves to, as that binding's
    /// position among the bindings in scope when it was made.
    fn reads(tree: &UExpr) -> Vec<(String, Option<usize>)> {
        let mut in_scope = InScope::new();
        let mut out = Vec::new();
        for visit in tree.root().walk() {
            match visit {
                Visit::Bind(x, _) => {
                    let depth = in_scope.iter().count();
                    in_scope.bind(x, depth);
                }
                Visit::Unbind(x) => {
                    in_scope.unbind(x);
                }
                Visit::Enter(e) => {
                    if let Exp::Var(x) = e.node() {
                        out.push((x.node.0.to_string(), in_scope.get(&x.node).copied()));
                    }
                }
                _ => {}
            }
        }
        out
    }

    #[test]
    fn each_binding_says_what_it_binds_to() {
        let t = tree("let x = a; let y = [x for z in [a]]; fun(p, q) => p * q * y");
        let kind = |e: ExpRef<'_, Size>| match e.node() {
            Exp::Var(v) => format!("var {}", v.node.0),
            Exp::Vec(_) => "vector".into(),
            Exp::Map(..) => "map".into(),
            Exp::Fun(..) => "fun".into(),
            _ => "other".into(),
        };
        let binds: Vec<_> = t
            .root()
            .walk()
            .filter_map(|visit| match visit {
                Visit::Bind(x, bound) => Some(format!(
                    "{}: {}",
                    x.node.0,
                    match bound {
                        Bound::Value(value) => format!("value {}", kind(value)),
                        Bound::Element { map, domain } => {
                            format!("element of {} in {}", kind(domain), kind(map))
                        }
                        Bound::Param(fun) => format!("param of {}", kind(fun)),
                    }
                )),
                _ => None,
            })
            .collect();
        assert_eq!(
            binds,
            [
                "x: value var a",
                "z: element of vector in map",
                "y: value map",
                "p: param of fun",
                "q: param of fun",
            ]
        );
    }

    #[test]
    fn bindings_end_innermost_first_before_their_node_is_left() {
        let t = tree("let x = a; let y = [x for z in [a]]; fun(p, q) => p * q * y");
        let events: Vec<_> = t
            .root()
            .walk()
            .filter_map(|visit| match visit {
                Visit::Bind(x, _) => Some(format!("bind {}", x.node.0)),
                Visit::Unbind(x) => Some(format!("unbind {}", x.node.0)),
                Visit::Leave(e) => match e.node() {
                    Exp::Map(..) => Some("leave map".into()),
                    Exp::Fun(..) => Some("leave fun".into()),
                    Exp::Block(..) => Some("leave block".into()),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        assert_eq!(
            events,
            [
                "bind x",
                "bind z",
                "unbind z",
                "leave map",
                "bind y",
                "bind p",
                "bind q",
                "unbind q",
                "unbind p",
                "leave fun",
                "unbind y",
                "unbind x",
                "leave block",
            ]
        );
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
    fn nested_statement_bindings_end_with_their_block() {
        let t = tree("let x = a; let y = (let x = x; x); x + y");
        assert_eq!(
            reads(&t),
            [
                ("a", None),
                ("x", Some(0)),
                ("x", Some(1)),
                ("x", Some(0)),
                ("y", Some(1))
            ]
            .map(|(name, binding)| (name.to_string(), binding))
        );
    }

    #[test]
    fn statement_events_wrap_values_before_binding() {
        let t = tree("let x = a; x <- x; x; x");
        let events: Vec<_> = t
            .root()
            .walk()
            .filter_map(|visit| match visit {
                Visit::EnterStmt(stmt) => Some(match stmt.node {
                    Stmt::Let(..) => "enter let",
                    Stmt::Log(..) => "enter log",
                    Stmt::Discard(_) => "enter discard",
                }),
                Visit::LeaveStmt(_) => Some("leave statement"),
                Visit::Enter(e) if matches!(e.node(), Exp::Var(..)) => Some("enter value"),
                Visit::Leave(e) if matches!(e.node(), Exp::Var(..)) => Some("leave value"),
                Visit::Bind(..) => Some("bind"),
                _ => None,
            })
            .collect();
        assert_eq!(
            events,
            [
                "enter let",
                "enter value",
                "leave value",
                "leave statement",
                "bind",
                "enter log",
                "enter value",
                "leave value",
                "leave statement",
                "bind",
                "enter discard",
                "enter value",
                "leave value",
                "leave statement",
                "enter value",
                "leave value",
            ]
        );
    }

    #[test]
    fn a_binding_with_nothing_after_it_binds_nothing() {
        let t = tree("let u = a; u <- a;");
        let binds: Vec<_> = t
            .root()
            .walk()
            .filter_map(|v| match v {
                Visit::Bind(x, _) => Some(x.node.0.to_string()),
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
