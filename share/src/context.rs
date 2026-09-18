use im::OrdMap;
use std::collections::BTreeSet;
use std::fmt;
use std::hash::Hash;
use std::ops::Index;

use crate::pretty::{BoxAllocator, DocAllocator, DocBuilder, Pretty};
use crate::traversal::Traversal;

/// General ordered map context backed by im::OrdMap for O(1) structural-sharing clones
pub struct Ctx<K, V>(OrdMap<K, V>);

impl<K: Clone, V: Clone> Clone for Ctx<K, V> {
    fn clone(&self) -> Self {
        Ctx(self.0.clone())
    }
}

impl<K: Ord + PartialEq, V: PartialEq> PartialEq for Ctx<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K: Ord + Eq, V: Eq> Eq for Ctx<K, V> {}

impl<K: Ord + PartialOrd, V: PartialOrd> PartialOrd for Ctx<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<K: Ord, V: Ord> Ord for Ctx<K, V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<K: Ord + Hash, V: Hash> Hash for Ctx<K, V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for Ctx<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Pretty printer instance for Ctx
impl<'a, D, A, K, V> Pretty<'a, D, A> for Ctx<K, V>
where
    K: Ord + Clone + Pretty<'a, D, A>,
    V: Clone + Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("{"),
            allocator.hardline(),
            allocator
                .intersperse(
                    self.0.iter().map(|(k, v)| {
                        k.clone()
                            .pretty(allocator)
                            .append(allocator.text(": "))
                            .append(v.clone().pretty(allocator))
                    }),
                    allocator.hardline(),
                )
                .group()
                .indent(2),
            allocator.hardline(),
            allocator.text("}"),
        ])
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Traversal instance for Ctx values
pub struct CtxValueTraversal<K, V>(std::marker::PhantomData<(K, V)>);
impl<K: Ord + Clone, V1: Clone, V2: Clone> Traversal<V1, V2> for CtxValueTraversal<K, V1> {
    type Domain = Ctx<K, V1>;
    type Codomain = Ctx<K, V2>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(V1) -> Result<V2, E>,
    ) -> Result<Self::Codomain, E> {
        on.into_iter().map(|(k, v)| Ok((k, f(v)?))).collect()
    }
}

/// IntoIterator instance for Ctx
impl<K: Ord + Clone, V: Clone> IntoIterator for Ctx<K, V> {
    type Item = (K, V);
    type IntoIter = im::ordmap::ConsumingIter<(K, V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<K, V> FromIterator<(K, V)> for Ctx<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Ctx(OrdMap::from_iter(iter))
    }
}

/// Display instance for Ctx calls the pretty printer
impl<'a, K, V> fmt::Display for Ctx<K, V>
where
    K: Ord + Pretty<'a, BoxAllocator, ()> + Clone,
    V: Pretty<'a, BoxAllocator, ()> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Ctx<_, _> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(80, f)
    }
}

impl<K: Ord, V> Index<&K> for Ctx<K, V> {
    type Output = V;
    fn index(&self, index: &K) -> &Self::Output {
        &self.0[index]
    }
}

impl<K: Ord, V> Index<K> for Ctx<K, V> {
    type Output = V;
    fn index(&self, index: K) -> &Self::Output {
        &self.0[&index]
    }
}

/// Special and wrapper methods for Ctx
impl<K, V> Ctx<K, V> {
    /// Creates an empty context.
    pub fn new() -> Self
    where
        K: Ord,
    {
        Ctx(OrdMap::new())
    }

    /// Creates a context holding the single binding `k` to `v`.
    pub fn singleton(k: K, v: V) -> Self
    where
        K: Ord + Clone,
        V: Clone,
    {
        let mut m = OrdMap::new();
        m.insert(k, v);
        Ctx(m)
    }

    /// Returns the first binding, in key order, satisfying `f`.
    pub fn find<FF>(&self, f: FF) -> Option<(&K, &V)>
    where
        FF: Fn(&K, &V) -> bool,
        K: Ord,
    {
        self.0.iter().find(|(k, v)| f(k, v))
    }

    /// Returns the first non-`None` result of applying `f` to a binding, in key order.
    pub fn find_map<FF, Y>(&self, f: FF) -> Option<Y>
    where
        FF: Fn(&K, &V) -> Option<Y>,
        K: Ord,
    {
        self.0.iter().find_map(|(k, v)| f(k, v))
    }

    /// Returns the binding with the smallest key.
    pub fn first(&self) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        self.0.iter().next()
    }

    /// Returns the binding with the largest key.
    pub fn last(&self) -> Option<(&K, &V)>
    where
        K: Ord,
    {
        self.0.iter().next_back()
    }

    /// Removes and returns the binding with the smallest key.
    ///
    /// Used to drain a context as a work queue in deterministic key order.
    pub fn pop_first(&mut self) -> Option<(K, V)>
    where
        K: Ord + Clone,
        V: Clone,
    {
        let (result, new_map) = self.0.without_min_with_key();
        self.0 = new_map;
        result
    }

    /// Reports whether any binding satisfies `f`.
    pub fn any<FF>(&self, f: FF) -> bool
    where
        FF: Fn(&K, &V) -> bool,
        K: Ord,
    {
        self.find(f).is_some()
    }
    /// Returns the number of bindings.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Removes every binding, leaving an empty context.
    pub fn clear(&mut self) {
        self.0.clear();
    }
    /// Binds `k` to `v`, cloning both, and returns the value previously bound to `k`.
    pub fn insert(&mut self, k: &K, v: &V) -> Option<V>
    where
        K: Ord + Clone,
        V: Clone,
    {
        self.0.insert(k.clone(), v.clone())
    }

    /// Inserts `k` with value `v`, resolving a key collision by renaming rather than
    /// overwriting.
    ///
    /// If `k` is already bound, `f` is called with the key, the incoming value and the
    /// existing value and must yield a replacement key; insertion is then retried with
    /// that key. This is how gensym-style shadowing avoidance is expressed for `Vid` and
    /// `Tid` environments.
    ///
    /// # Errors
    /// Returns the `E` produced by `f` when it refuses to rename a colliding key, e.g.
    /// because the collision is a genuine redeclaration rather than shadowing.
    pub fn insert_with<E, FF>(&mut self, k: K, v: V, f: &FF) -> Result<(), E>
    where
        K: Ord + Clone,
        V: Clone + Eq,
        FF: Fn(&K, &V, &V) -> Result<K, E>,
    {
        match self.0.get(&k) {
            Some(v1) => {
                let k = f(&k, &v, v1)?;
                self.insert_with(k, v, f)
            }
            None => {
                self.0.insert(k, v);
                Ok(())
            }
        }
    }

    /// Inserts every binding of `other` into `self`; on a shared key `other` wins.
    pub fn append(&mut self, other: &Ctx<K, V>)
    where
        K: Ord + Clone,
        V: Clone,
    {
        for (k, v) in other.0.iter() {
            self.0.insert(k.clone(), v.clone());
        }
    }
    /// Returns the union of `self` and `other`; on a shared key `other`'s value wins.
    ///
    /// Neither operand is modified: `Ctx` clones are `O(1)` thanks to structural sharing.
    pub fn union(&self, other: &Ctx<K, V>) -> Ctx<K, V>
    where
        K: Ord + Clone,
        V: Clone,
    {
        Ctx(other.0.clone().union(self.0.clone()))
    }

    /// Reports whether the context has no bindings.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Looks up the value bound to `k`.
    pub fn get(&self, k: &K) -> Option<&V>
    where
        K: Ord,
    {
        self.0.get(k)
    }

    /// Looks up the value bound to `k` for in-place mutation, cloning the affected path
    /// out of any shared structure first.
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V>
    where
        K: Ord + Clone,
        V: Clone,
    {
        self.0.get_mut(k)
    }

    /// Removes the binding for `k` and returns its value.
    pub fn remove(&mut self, k: &K) -> Option<V>
    where
        K: Ord + Clone,
        V: Clone,
    {
        self.0.remove(k)
    }

    /// Returns the bound keys as a [`Set`], in key order.
    pub fn keys(&self) -> Set<K>
    where
        K: Ord + Clone,
    {
        Set(self.0.keys().cloned().collect::<BTreeSet<_>>())
    }
    /// Returns the bound values, in key order.
    pub fn values(&self) -> Vec<V>
    where
        V: Clone,
        K: Ord,
    {
        self.0.values().cloned().collect()
    }
    /// Reports whether `k` is bound.
    pub fn contains(&self, k: &K) -> bool
    where
        K: Ord,
    {
        self.0.contains_key(k)
    }
    /// Iterates over the bindings in ascending key order.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)>
    where
        K: Ord,
    {
        self.0.iter()
    }
    /// Rewrites every value in place, preserving the key set and ordering.
    pub fn modify<F>(&mut self, mut f: F)
    where
        K: Ord + Clone,
        V: Clone,
        F: FnMut(&K, &mut V),
    {
        let old = std::mem::replace(&mut self.0, OrdMap::new());
        let mut new_map = OrdMap::new();
        for (k, v) in old {
            let mut v = v;
            f(&k, &mut v);
            new_map.insert(k, v);
        }
        self.0 = new_map;
    }
    /// Drops every binding for which `f` returns `false`.
    pub fn retain(&mut self, f: impl Fn(&K, &V) -> bool)
    where
        K: Ord + Clone,
        V: Clone,
    {
        let old = std::mem::replace(&mut self.0, OrdMap::new());
        let mut new_map = OrdMap::new();
        for (k, v) in old {
            if f(&k, &v) {
                new_map.insert(k, v);
            }
        }
        self.0 = new_map;
    }

    /// Returns the underlying map entry for `k`, for insert-or-update in one lookup.
    pub fn entry(&mut self, k: K) -> im::ordmap::Entry<'_, K, V>
    where
        K: Ord + Clone,
        V: Clone,
    {
        self.0.entry(k)
    }

    /// Returns the unique binding satisfying `f`, or `None` if zero or several match.
    ///
    /// The "several match" case deliberately collapses to `None` so callers can treat
    /// ambiguity and absence uniformly (e.g. overload resolution that must be unique).
    pub fn find_one(&self, f: impl Fn(&K, &V) -> bool) -> Option<(K, V)>
    where
        K: Ord + Clone,
        V: Clone,
    {
        let res: Vec<(K, V)> = self
            .0
            .iter()
            .filter(|(k, v)| f(k, v))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        if res.len() == 1 {
            Some(res[0].clone())
        } else {
            None
        }
    }

    /// Removes every binding satisfying `f` from `self` and returns them as a new context.
    pub fn extract_if(&mut self, f: impl Fn(&K, &V) -> bool) -> Ctx<K, V>
    where
        K: Ord + Clone,
        V: Clone,
    {
        let mut c = Ctx::new();
        for (k, v) in self.0.clone().into_iter() {
            if f(&k, &v) {
                c.insert(&k, &v);
            }
        }
        self.retain(|k, _| !c.contains(k));
        c
    }
}

impl<K: Ord, V> Default for Ctx<K, V> {
    fn default() -> Self {
        Ctx(OrdMap::new())
    }
}

/// From instance
impl<X, Y, K: From<X> + Ord + Clone, V: From<Y> + Clone, const N: usize> From<[(X, Y); N]>
    for Ctx<K, V>
{
    fn from(v: [(X, Y); N]) -> Self {
        Ctx(OrdMap::from_iter(
            v.into_iter().map(|(k, v)| (K::from(k), V::from(v))),
        ))
    }
}

impl<X, Y, K: From<X> + Ord + Clone, V: From<Y> + Clone> From<Vec<(X, Y)>> for Ctx<K, V> {
    fn from(v: Vec<(X, Y)>) -> Self {
        Ctx(OrdMap::from_iter(
            v.into_iter().map(|(k, v)| (K::from(k), V::from(v))),
        ))
    }
}

///////////////////////////////////////////////////////////////////////////////////
// A set of values with Pretty and Display traits and other useful methods
///////////////////////////////////////////////////////////////////////////////////
/// Ordered set of values with `Pretty`/`Display` instances, used for key sets, free-variable
/// sets and signature sets throughout the compiler.
///
/// Backed by a `BTreeSet`, so iteration order is the `Ord` order of `V`; this is what keeps
/// analysis output and pretty-printed diagnostics deterministic.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Set<V>(BTreeSet<V>);

/// Pretty printer instance
impl<'a, D, A, V> Pretty<'a, D, A> for Set<V>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
    V: Pretty<'a, D, A> + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("{"),
            allocator.intersperse(self.0.into_iter().map(|k| k.pretty(allocator)), ", "),
            allocator.text("}"),
        ])
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl<V> IntoIterator for Set<V> {
    type Item = V;
    type IntoIter = std::collections::btree_set::IntoIter<V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

// Iterator for borrowing key-value pairs
/// Borrowing iterator over the elements of a [`Set`], in ascending order.
#[derive(Debug, Clone)]
pub struct SetIterator<'a, V> {
    iter: std::collections::btree_set::Iter<'a, V>,
}

impl<'a, V> Iterator for SetIterator<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<V> FromIterator<V> for Set<V>
where
    V: Ord,
{
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        Set(BTreeSet::from_iter(iter))
    }
}

impl<V> Default for Set<V> {
    fn default() -> Self {
        Set(BTreeSet::new())
    }
}

impl<'a, V> fmt::Display for Set<V>
where
    V: Pretty<'a, BoxAllocator, ()> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Set<_> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(80, f)
    }
}

impl<V: Ord, const N: usize> From<[V; N]> for Set<V> {
    fn from(v: [V; N]) -> Self {
        Set(BTreeSet::from_iter(v))
    }
}

impl<V: Ord> From<Vec<V>> for Set<V> {
    fn from(v: Vec<V>) -> Self {
        Set(BTreeSet::from_iter(v))
    }
}

impl<V: Ord> From<Set<V>> for Vec<V> {
    fn from(val: Set<V>) -> Self {
        val.0.into_iter().collect()
    }
}

impl<V: Ord> Set<V> {
    /// Creates an empty set.
    pub fn new() -> Self
    where
        V: Ord,
    {
        Set(BTreeSet::new())
    }
    /// Creates a set holding exactly `v`.
    pub fn singleton(v: V) -> Self {
        Set(BTreeSet::from([v]))
    }

    /// Returns the number of elements.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Inserts `k`, returning `true` if it was not already present.
    pub fn insert(&mut self, k: V) -> bool {
        self.0.insert(k)
    }

    /// Removes and returns the smallest element.
    pub fn pop_first(&mut self) -> Option<V> {
        self.0.pop_first()
    }

    /// Inserts every element of `it`, returning `true` if at least one was new.
    ///
    /// The boolean is the fixed-point signal used by the dataflow analyses: they keep
    /// iterating while some `append` still changes a set.
    pub fn append<It>(&mut self, it: It) -> bool
    where
        It: Iterator<Item = V>,
    {
        let mut ins = false;
        for k in it {
            ins |= self.0.insert(k)
        }
        ins
    }
    /// Returns the smallest element.
    pub fn first(&self) -> Option<&V> {
        self.0.first()
    }

    /// Reports whether `self` and `other` share no element.
    pub fn is_disjoint(&self, other: &Set<V>) -> bool {
        self.0.is_disjoint(&other.0)
    }

    /// Returns the largest element.
    pub fn last(&self) -> Option<&V> {
        self.0.last()
    }
    /// Reports whether `k` is a member.
    pub fn contains(&self, k: &V) -> bool {
        self.0.contains(k)
    }

    /// Returns the smallest element satisfying `f`.
    pub fn find<FF>(&self, f: FF) -> Option<&V>
    where
        FF: Fn(&V) -> bool,
    {
        self.0.iter().find(|v| f(v))
    }

    /// Reports whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Union of two sets
    pub fn union(&self, other: Set<V>) -> Self
    where
        V: Clone,
    {
        let mut c = self.clone();
        c.append(other.into_iter());
        c
    }
    /// Intersection of two sets
    pub fn intersection(&self, other: Set<V>) -> Self
    where
        V: Clone,
    {
        Set(self.0.intersection(&other.0).cloned().collect())
    }

    /// Iterates over the elements in ascending order, borrowing them.
    pub fn iter<'a>(&'a self) -> SetIterator<'a, V> {
        SetIterator {
            iter: self.0.iter(),
        }
    }

    /// Method to iterate over a mutable Vec, modify elements, and return a new `Set<T>`
    pub fn modify<F>(&mut self, mut f: F)
    where
        V: Clone,
        F: FnMut(&mut V),
    {
        // Convert BTreeSet<V> to Vec<V>
        let mut vec: Vec<V> = self.0.iter().cloned().collect();

        // Apply modification function to each element
        for elem in vec.iter_mut() {
            f(elem);
        }
        // Collect back into Set<V>
        self.0 = vec.into_iter().collect();
    }

    /// Extract elements from the map that satisfy a predicate
    pub fn extract_if(&mut self, f: impl Fn(&V) -> bool) -> Set<V>
    where
        V: Clone,
    {
        let mut s = Set::new();
        let mut to_remove = Vec::new();
        for v in self.0.iter() {
            if f(v) {
                s.insert(v.clone());
                to_remove.push(v.clone());
            }
        }
        for v in to_remove {
            self.0.remove(&v);
        }
        s
    }

    /// Drops every element for which `f` returns `false`.
    pub fn retain(&mut self, f: impl Fn(&V) -> bool) {
        self.0.retain(f);
    }
}

impl<V: Ord + Clone> Set<&V> {
    /// Clones every borrowed element, turning a set of references into an owning set.
    pub fn cloned(self) -> Set<V> {
        Set(self.0.into_iter().cloned().collect())
    }
}

#[test]
fn set_modify() {
    let mut s = Set::from([1, 2, 3]);
    s.modify(|v| *v += 1);
    assert_eq!(s.into_iter().collect::<Vec<_>>(), vec![2, 3, 4]);
}

#[test]
fn set_extract_if() {
    let mut s = Set::from([1, 2, 3, 4, 5]);
    let s2 = s.extract_if(|v| *v % 2 == 0);
    assert_eq!(s.into_iter().collect::<Vec<_>>(), vec![1, 3, 5]);
    assert_eq!(s2.into_iter().collect::<Vec<_>>(), vec![2, 4]);
}

#[cfg(test)]
mod additional_tests {
    use super::*;

    // Ctx tests
    #[test]
    fn test_ctx_singleton() {
        let ctx = Ctx::singleton("key", 42);
        assert_eq!(ctx.len(), 1);
        assert_eq!(ctx.get(&"key"), Some(&42));
    }

    #[test]
    fn test_ctx_find_map() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        ctx.insert(&3, &"three");

        let result = ctx.find_map(|k, v| {
            if *k == 2 {
                Some(v.to_uppercase())
            } else {
                None
            }
        });
        assert_eq!(result, Some("TWO".to_string()));
    }

    #[test]
    fn test_ctx_find_map_not_found() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");

        let result = ctx.find_map(|k, _v| if *k == 99 { Some(true) } else { None });
        assert_eq!(result, None);
    }

    #[test]
    fn test_ctx_last() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        ctx.insert(&3, &"three");

        let last = ctx.last();
        assert_eq!(last, Some((&3, &"three")));
    }

    #[test]
    fn test_ctx_last_empty() {
        let ctx: Ctx<i32, &str> = Ctx::new();
        assert_eq!(ctx.last(), None);
    }

    #[test]
    fn test_ctx_pop_first() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        ctx.insert(&3, &"three");

        let first = ctx.pop_first();
        assert_eq!(first, Some((1, "one")));
        assert_eq!(ctx.len(), 2);
    }

    #[test]
    fn test_ctx_pop_first_empty() {
        let mut ctx: Ctx<i32, &str> = Ctx::new();
        assert_eq!(ctx.pop_first(), None);
    }

    #[test]
    fn test_ctx_any_true() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        ctx.insert(&3, &30);

        assert!(ctx.any(|_k, v| *v == 20));
    }

    #[test]
    fn test_ctx_any_false() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);

        assert!(!ctx.any(|_k, v| *v == 99));
    }

    #[test]
    fn test_ctx_clear() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        assert_eq!(ctx.len(), 2);

        ctx.clear();
        assert_eq!(ctx.len(), 0);
        assert!(ctx.is_empty());
    }

    #[test]
    fn test_ctx_insert_with_no_conflict() {
        let mut ctx = Ctx::new();
        let result = ctx.insert_with(1, "one", &|_k, _v1, _v2| Ok::<_, ()>(1));
        assert!(result.is_ok());
        assert_eq!(ctx.get(&1), Some(&"one"));
    }

    #[test]
    fn test_ctx_insert_with_conflict() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"original");

        // Use a different key to avoid infinite recursion
        let result = ctx.insert_with(1, "new", &|_k, _v1, _v2| Ok::<i32, ()>(2));
        assert!(result.is_ok());
        assert_eq!(ctx.get(&2), Some(&"new"));
    }

    #[test]
    fn test_ctx_insert_with_error() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"original");

        let result = ctx.insert_with(1, "new", &|_k, _v1, _v2| Err::<i32, _>("conflict"));
        assert!(result.is_err());
    }

    #[test]
    fn test_ctx_append() {
        let mut ctx1 = Ctx::new();
        ctx1.insert(&1, &"one");
        ctx1.insert(&2, &"two");

        let mut ctx2 = Ctx::new();
        ctx2.insert(&3, &"three");
        ctx2.insert(&4, &"four");

        ctx1.append(&ctx2);
        assert_eq!(ctx1.len(), 4);
        assert_eq!(ctx1.get(&3), Some(&"three"));
    }

    #[test]
    fn test_ctx_union() {
        let mut ctx1 = Ctx::new();
        ctx1.insert(&1, &"one");
        ctx1.insert(&2, &"two");

        let mut ctx2 = Ctx::new();
        ctx2.insert(&3, &"three");

        let ctx3 = ctx1.union(&ctx2);
        assert_eq!(ctx3.len(), 3);
        assert_eq!(ctx3.get(&1), Some(&"one"));
        assert_eq!(ctx3.get(&3), Some(&"three"));
    }

    #[test]
    fn test_ctx_get_mut() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &42);

        if let Some(v) = ctx.get_mut(&1) {
            *v = 100;
        }
        assert_eq!(ctx.get(&1), Some(&100));
    }

    #[test]
    fn test_ctx_get_mut_not_found() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &42);

        assert_eq!(ctx.get_mut(&99), None);
    }

    #[test]
    fn test_ctx_remove() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");

        let removed = ctx.remove(&1);
        assert_eq!(removed, Some("one"));
        assert_eq!(ctx.len(), 1);
        assert_eq!(ctx.get(&1), None);
    }

    #[test]
    fn test_ctx_remove_not_found() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");

        let removed = ctx.remove(&99);
        assert_eq!(removed, None);
    }

    #[test]
    fn test_ctx_find_one_single_match() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        ctx.insert(&3, &30);

        let result = ctx.find_one(|_k, v| *v == 20);
        assert_eq!(result, Some((2, 20)));
    }

    #[test]
    fn test_ctx_find_one_no_match() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);

        let result = ctx.find_one(|_k, v| *v == 99);
        assert_eq!(result, None);
    }

    #[test]
    fn test_ctx_find_one_multiple_matches() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &10);
        ctx.insert(&3, &30);

        let result = ctx.find_one(|_k, v| *v == 10);
        assert_eq!(result, None); // Multiple matches return None
    }

    // Set tests
    #[test]
    fn test_set_singleton() {
        let s = Set::singleton(42);
        assert_eq!(s.len(), 1);
        assert!(s.contains(&42));
    }

    #[test]
    fn test_set_pop_first() {
        let mut s = Set::from([1, 2, 3]);
        let first = s.pop_first();
        assert_eq!(first, Some(1));
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn test_set_pop_first_empty() {
        let mut s: Set<i32> = Set::new();
        assert_eq!(s.pop_first(), None);
    }

    #[test]
    fn test_set_append_iterator() {
        let mut s = Set::from([1, 2]);
        let inserted = s.append(vec![3, 4, 5].into_iter());
        assert!(inserted);
        assert_eq!(s.len(), 5);
    }

    #[test]
    fn test_set_append_duplicates() {
        let mut s = Set::from([1, 2, 3]);
        let inserted = s.append(vec![2, 3].into_iter());
        assert!(!inserted); // No new elements inserted
        assert_eq!(s.len(), 3);
    }

    #[test]
    fn test_set_first() {
        let s = Set::from([3, 1, 2]);
        assert_eq!(s.first(), Some(&1)); // BTreeSet is sorted
    }

    #[test]
    fn test_set_first_empty() {
        let s: Set<i32> = Set::new();
        assert_eq!(s.first(), None);
    }

    #[test]
    fn test_set_last() {
        let s = Set::from([1, 3, 2]);
        assert_eq!(s.last(), Some(&3));
    }

    #[test]
    fn test_set_last_empty() {
        let s: Set<i32> = Set::new();
        assert_eq!(s.last(), None);
    }

    #[test]
    fn test_set_is_disjoint_true() {
        let s1 = Set::from([1, 2, 3]);
        let s2 = Set::from([4, 5, 6]);
        assert!(s1.is_disjoint(&s2));
    }

    #[test]
    fn test_set_is_disjoint_false() {
        let s1 = Set::from([1, 2, 3]);
        let s2 = Set::from([3, 4, 5]);
        assert!(!s1.is_disjoint(&s2));
    }

    #[test]
    fn test_set_find() {
        let s = Set::from([1, 2, 3, 4, 5]);
        let result = s.find(|v| *v == 3);
        assert_eq!(result, Some(&3));
    }

    #[test]
    fn test_set_find_not_found() {
        let s = Set::from([1, 2, 3]);
        let result = s.find(|v| *v == 99);
        assert_eq!(result, None);
    }

    #[test]
    fn test_set_union() {
        let s1 = Set::from([1, 2, 3]);
        let s2 = Set::from([3, 4, 5]);
        let s3 = s1.union(s2);
        assert_eq!(s3.len(), 5);
        assert!(s3.contains(&1));
        assert!(s3.contains(&5));
    }

    #[test]
    fn test_set_intersection() {
        let s1 = Set::from([1, 2, 3, 4]);
        let s2 = Set::from([3, 4, 5, 6]);
        let s3 = s1.intersection(s2);
        assert_eq!(s3.len(), 2);
        assert!(s3.contains(&3));
        assert!(s3.contains(&4));
    }

    #[test]
    fn test_set_intersection_empty() {
        let s1 = Set::from([1, 2, 3]);
        let s2 = Set::from([4, 5, 6]);
        let s3 = s1.intersection(s2);
        assert_eq!(s3.len(), 0);
    }

    #[test]
    fn test_set_retain() {
        let mut s = Set::from([1, 2, 3, 4, 5]);
        s.retain(|v| *v % 2 == 0);
        assert_eq!(s.into_iter().collect::<Vec<_>>(), vec![2, 4]);
    }

    #[test]
    fn test_set_cloned() {
        let s = Set::from([&1, &2, &3]);
        let s2 = s.cloned();
        assert_eq!(s2.into_iter().collect::<Vec<_>>(), vec![1, 2, 3]);
    }

    #[test]
    fn test_ctx_traverse2() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);

        let result = CtxValueTraversal::traverse(ctx, &mut |v| Ok::<_, ()>(v * 2));
        assert!(result.is_ok());
        let ctx2 = result.unwrap();
        assert_eq!(ctx2.get(&1), Some(&20));
        assert_eq!(ctx2.get(&2), Some(&40));
    }

    #[test]
    fn test_ctx_traverse2_error() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);

        let result = CtxValueTraversal::traverse(ctx, &mut |v: i32| {
            if v > 15 {
                Err("Too large")
            } else {
                Ok(v)
            }
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_ctx_map2() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);

        let ctx2 = CtxValueTraversal::traverse(ctx, &mut |v| Ok::<_, ()>(v * 3)).unwrap();
        assert_eq!(ctx2.get(&1), Some(&30));
        assert_eq!(ctx2.get(&2), Some(&60));
    }

    #[test]
    fn test_ctx_display() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        let display = format!("{}", ctx);
        assert!(display.contains("1"));
        assert!(display.contains("2"));
    }

    #[test]
    fn test_set_display() {
        let s = Set::from([1, 2, 3]);
        let display = format!("{}", s);
        assert!(display.contains("1"));
        assert!(display.contains("2"));
        assert!(display.contains("3"));
    }

    #[test]
    fn test_ctx_from_array() {
        let ctx: Ctx<i32, &str> = Ctx::from([(1, "one"), (2, "two")]);
        assert_eq!(ctx.len(), 2);
        assert_eq!(ctx.get(&1), Some(&"one"));
    }

    #[test]
    fn test_ctx_from_vec() {
        let v = vec![(1, "one"), (2, "two"), (3, "three")];
        let ctx: Ctx<i32, &str> = Ctx::from(v);
        assert_eq!(ctx.len(), 3);
        assert_eq!(ctx.get(&2), Some(&"two"));
    }

    #[test]
    fn test_set_from_array() {
        let s: Set<i32> = Set::from([1, 2, 3]);
        assert_eq!(s.len(), 3);
    }

    #[test]
    fn test_set_from_vec() {
        let v = vec![1, 2, 3, 4];
        let s: Set<i32> = Set::from(v);
        assert_eq!(s.len(), 4);
    }

    #[test]
    fn test_set_into_vec() {
        let s = Set::from([3, 1, 2]);
        let v: Vec<i32> = s.into();
        assert_eq!(v, vec![1, 2, 3]); // BTreeSet is sorted
    }

    #[test]
    fn test_ctx_index_ref() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        assert_eq!(ctx[&1], "one");
        assert_eq!(ctx[&2], "two");
    }

    #[test]
    fn test_ctx_index_owned() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        assert_eq!(ctx[1], "one");
        assert_eq!(ctx[2], "two");
    }

    #[test]
    fn test_ctx_default() {
        let ctx: Ctx<i32, &str> = Ctx::default();
        assert_eq!(ctx.len(), 0);
        assert!(ctx.is_empty());
    }

    #[test]
    fn test_set_default() {
        let s: Set<i32> = Set::default();
        assert_eq!(s.len(), 0);
        assert!(s.is_empty());
    }

    #[test]
    fn test_ctx_into_iter() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        let vec: Vec<(i32, &str)> = ctx.into_iter().collect();
        assert_eq!(vec.len(), 2);
    }

    #[test]
    fn test_set_into_iter() {
        let s = Set::from([1, 2, 3]);
        let vec: Vec<i32> = s.into_iter().collect();
        assert_eq!(vec, vec![1, 2, 3]);
    }

    #[test]
    fn test_set_iter() {
        let s = Set::from([1, 2, 3]);
        let mut count = 0;
        for _v in s.iter() {
            count += 1;
        }
        assert_eq!(count, 3);
    }

    #[test]
    fn test_ctx_iter() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        let mut count = 0;
        for (_k, _v) in ctx.iter() {
            count += 1;
        }
        assert_eq!(count, 2);
    }

    #[test]
    fn test_ctx_modify_increment() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        ctx.modify(|_k, v| *v += 1);
        assert_eq!(ctx.get(&1), Some(&11));
        assert_eq!(ctx.get(&2), Some(&21));
    }

    #[test]
    fn test_ctx_modify() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        ctx.modify(|_k, v| *v *= 2);
        assert_eq!(ctx.get(&1), Some(&20));
        assert_eq!(ctx.get(&2), Some(&40));
    }

    #[test]
    fn test_ctx_retain() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        ctx.insert(&3, &30);
        ctx.retain(|k, _v| *k % 2 == 1);
        assert_eq!(ctx.len(), 2);
        assert!(ctx.contains(&1));
        assert!(ctx.contains(&3));
        assert!(!ctx.contains(&2));
    }

    #[test]
    fn test_ctx_entry() {
        let mut ctx = Ctx::new();
        ctx.entry(1).or_insert("one");
        ctx.entry(1).or_insert("uno");
        assert_eq!(ctx.get(&1), Some(&"one"));
    }

    #[test]
    fn test_ctx_extract_if() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        ctx.insert(&3, &30);
        let extracted = ctx.extract_if(|_k, v| *v >= 20);
        assert_eq!(ctx.len(), 1);
        assert_eq!(extracted.len(), 2);
        assert_eq!(ctx.get(&1), Some(&10));
        assert_eq!(extracted.get(&2), Some(&20));
    }

    #[test]
    fn test_ctx_keys() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        let keys = ctx.keys();
        assert_eq!(keys.len(), 2);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
    }

    #[test]
    fn test_ctx_values() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        let values = ctx.values();
        assert_eq!(values.len(), 2);
        assert!(values.contains(&"one"));
        assert!(values.contains(&"two"));
    }

    #[test]
    fn test_ctx_find() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &10);
        ctx.insert(&2, &20);
        let found = ctx.find(|k, v| *k == 1 && *v == 10);
        assert_eq!(found, Some((&1, &10)));
    }

    #[test]
    fn test_ctx_first() {
        let mut ctx = Ctx::new();
        ctx.insert(&1, &"one");
        ctx.insert(&2, &"two");
        let first = ctx.first();
        assert_eq!(first, Some((&1, &"one")));
    }

    #[test]
    fn test_ctx_first_empty() {
        let ctx: Ctx<i32, &str> = Ctx::new();
        assert_eq!(ctx.first(), None);
    }

    #[test]
    fn test_ctx_from_iter() {
        let v = vec![(1, "one"), (2, "two")];
        let ctx: Ctx<i32, &str> = v.into_iter().collect();
        assert_eq!(ctx.len(), 2);
    }
}
