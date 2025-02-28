use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::hash::Hash;

use crate::pretty::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use crate::traversal::{ToTraversal2, Traversal};

/// General BTreeMap context
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Ctx<K, V>(BTreeMap<K, V>);

/// Pretty printer instance for Ctx
impl<'a, D, A, K, V> Pretty<'a, D, A> for Ctx<K, V>
where
    K: Clone + Pretty<'a, D, A>,
    V: Clone + Pretty<'a, D, A>,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("{"),
            allocator.intersperse(
                self.0.iter().map(|(k, v)| {
                    k.clone().pretty(allocator)
                        .append(allocator.text(" -> "))
                        .append(v.clone().pretty(allocator))
                }),
                ", ",
            ),
            allocator.text("}"),
        ])
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Traversal instance for Ctx values
pub struct CtxValueTraversal<K, V>(std::marker::PhantomData<(K, V)>);
impl<K: Ord, V1, V2> Traversal<V1, V2> for CtxValueTraversal<K, V1> {
    type Domain = Ctx<K, V1>;
    type Codomain = Ctx<K, V2>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(V1) -> Result<V2, E>,
    ) -> Result<Self::Codomain, E> {
        on.into_iter().map(|(k, v)| Ok((k, f(v)?))).collect()
    }
}

impl<K: Ord, V1> ToTraversal2<V1> for Ctx<K, V1> {
    type Output<Z> = Ctx<K, Z>;
    fn traverse2<V2, E>(self, f: &mut dyn FnMut(V1) -> Result<V2, E>) -> Result<Self::Output<V2>, E> {
        CtxValueTraversal::traverse(self, f)
    }
}

/// IntoIterator instance for Ctx
impl<K, V> IntoIterator for Ctx<K, V> {
    type Item = (K, V);
    type IntoIter = std::collections::btree_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Iterator for borrowing key-value pairs
#[derive(Debug, Clone)]
pub struct CtxIterator<'a, K, V> {
    iter: std::collections::btree_map::Iter<'a, K, V>,
}

/// Iterator instance for Ctx
impl<'a, K, V> Iterator for CtxIterator<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<K, V> FromIterator<(K, V)> for Ctx<K, V>
where
    K: Ord
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Ctx(BTreeMap::from_iter(iter))
    }
}

/// Display instance for Ctx calls the pretty printer
impl<'a, K, V> fmt::Display for Ctx<K, V>
where
    K: Pretty<'a, BoxAllocator, ()> + Clone,
    V: Pretty<'a, BoxAllocator, ()> + Clone
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Ctx<_, _> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(80, f)
    }
}

/// Special and wrapper methods for Ctx
impl<K: Ord, V> Ctx<K, V> {
    pub fn new() -> Self {
        Ctx(BTreeMap::new())
    }

    pub fn singleton(k: K, v: V) -> Self {
        Ctx(BTreeMap::from([(k, v)]))
    }

    pub fn find<FF>(&self, f: FF) -> Option<(&K, &V)> where FF: Fn(&K, &V) -> bool {
        self.0.iter().find(|(k, v)| f(k, v))
    }

    pub fn any<FF>(&self, f: FF) -> bool where FF: Fn(&K, &V) -> bool {
        self.find(f).is_some()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }
    pub fn insert(&mut self, k: &K, v: &V) -> Option<V> where K: Clone, V: Clone {
        self.0.insert(k.clone(), v.clone())
    }

    pub fn insert_with<E, FF>(&mut self, k: K, v: V, f: &FF) -> Result<(), E>
    where
        K: Clone,
        V: Clone,
        FF: Fn(&K,&V,&V) -> Result<K, E>
    {
        match self.0.get(&k) {
            Some(v1) => {
                let k = f(&k, &v, &v1)?;
                self.insert_with(k, v, f)
            }
            None => {
                self.0.insert(k, v);
                Ok(())
            }
        }
    }

    pub fn union_with<E, FF>(&self, other: Self, f: &FF) -> Result<Self, E>
    where
        K: Clone,
        V: Clone,
        FF: Fn(&K,&V,&V) -> Result<K, E>
    {
        let mut c = self.clone();
        for (k, v2) in other.0.into_iter() {
            c.insert_with(k, v2, f)?;
        }
        Ok(c)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn get(&self, k: &K) -> Option<&V> {
        self.0.get(k)
    }

    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        self.0.get_mut(k)
    }

    pub fn remove(&mut self, k: &K) -> Option<V>
    where
        V: Clone,
    {
        self.0.remove(k)
    }
    pub fn keys(&self) -> Set<&K> {
        Set(self.0.keys().collect::<BTreeSet<_>>())
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.0.values()
    }
    pub fn contains(&self, k: &K) -> bool {
        self.0.contains_key(k)
    }
    pub fn iter(&self) -> CtxIterator<K, V> {
        CtxIterator {
            iter: self.0.iter(),
        }
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&K, &mut V)> {
        self.0.iter_mut()
    }
    pub fn modify<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V)
    {
        for (k, v) in self.iter_mut() {
            f(k, v);
        }
    }
    pub fn retain(&mut self, f: impl Fn(&K, &mut V) -> bool) {
        self.0.retain(f);
    }

    pub fn entry(&mut self, k: K) -> std::collections::btree_map::Entry<K, V> {
        self.0.entry(k)
    }
    pub fn extract_if(&mut self, f: impl Fn(&K, &V) -> bool) -> Ctx<K, V>
    where
        K: Clone,
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
        Ctx(BTreeMap::new())
    }
}

/// From instance
impl<X, Y, K: From<X> + Ord, V: From<Y>, const N: usize> From<[(X, Y); N]> for Ctx<K, V> {
    fn from(v: [(X, Y); N]) -> Self {
        Ctx(BTreeMap::from_iter(v.into_iter().map(|(k, v)| (K::from(k), V::from(v)))))
    }
}

impl<X, Y, K: From<X> + Ord, V: From<Y>> From<Vec<(X, Y)>> for Ctx<K, V> {
    fn from(v: Vec<(X, Y)>) -> Self {
        Ctx(BTreeMap::from_iter(v.into_iter().map(|(k, v)| (K::from(k), V::from(v)))))
    }
}

///////////////////////////////////////////////////////////////////////////////////
// A set of values with Pretty and Display traits and other useful methods
///////////////////////////////////////////////////////////////////////////////////
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Set<V>(BTreeSet<V>);

/// Pretty printer instance
impl<'a, D, A, V> Pretty<'a, D, A> for Set<V>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
    V: Pretty<'a, D, A> + Clone
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("{"),
            allocator.intersperse(
                self.0.into_iter()
                    .map(|k| k.pretty(allocator)), ", "),
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
    V: Pretty<'a, BoxAllocator, ()> + Clone
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Set<_> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
                .1
                .render_fmt(80, f)
    }
}

impl<V: Ord, const N: usize> From<[V; N]> for Set<V> {
    fn from(v: [V; N]) -> Self {
        Set(BTreeSet::from_iter(v.into_iter()))
    }
}

impl<V: Ord> From<Vec<V>> for Set<V> {
    fn from(v: Vec<V>) -> Self {
        Set(BTreeSet::from_iter(v.into_iter()))
    }
}

impl<V: Ord> Into<Vec<V>> for Set<V> {
    fn into(self) -> Vec<V> {
        self.0.into_iter().collect()
    }
}

impl<V: Ord> Set<V> {
    pub fn new() -> Self where V: Ord {
        Set(BTreeSet::new())
    }
    pub fn singleton(v: V) -> Self {
        Set(BTreeSet::from([v]))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn insert(&mut self, k: V) -> bool {
        self.0.insert(k)
    }

    pub fn pop_first(&mut self) -> Option<V> {
        self.0.pop_first()
    }

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
    pub fn first(&self) -> Option<&V> {
        self.0.iter().next()
    }
    pub fn contains(&self, k: &V) -> bool {
        self.0.contains(k)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Union of two sets
    pub fn union(&self, other: Set<V>) -> Self
    where
        V: Clone
    {
        let mut c = self.clone();
        c.append(other.into_iter());
        c
    }
    /// Intersection of two sets
    pub fn intersection(&self, other: Set<V>) -> Self
    where
        V: Clone
    {
        Set(self.0.intersection(&other.0).cloned().collect())
    }

    pub fn iter(&self) -> SetIterator<V> {
        SetIterator {
            iter: self.0.iter(),
        }
    }

    /// Method to iterate over a mutable Vec, modify elements, and return a new Set<T>
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
        V: Clone
    {
        self.0.extract_if(f).collect()
    }

    pub fn retain(&mut self, f: impl Fn(&V) -> bool) {
        self.0.retain(f);
    }
}

impl<V: Ord + Clone> Set<&V> {
    pub fn cloned(self) -> Set<V> {
        Set(self.0.into_iter().cloned().collect())
    }
}

#[test]
fn ctx_union_with() {
    let c = Ctx::from([("a", 1), ("b", 2), ("c", 3)]);
    let c2 = Ctx::from([("a", 2), ("b", 3), ("d", 4)]);
    let c3 = c.union_with(c2, &|v1, v2| Some(v1 + v2));
    assert_eq!(c3.get(&"a"), Some(&3));
    assert_eq!(c3.get(&"b"), Some(&5));
    assert_eq!(c3.get(&"c"), Some(&3));
    assert_eq!(c3.get(&"d"), Some(&4));
}

#[test]
fn ctx_intersection_with() {
    let c : Ctx<&str, i8> = Ctx::from([("a", 1), ("b", 2), ("c", 3)]);
    let c2 = Ctx::from([("a", 2), ("b", 3), ("d", 4)]);
    let c3 = c.intersection_with(c2, &|v1, v2| Some(v1 * v2));
    assert_eq!(c3.get(&"a"), Some(&2));
    assert_eq!(c3.get(&"b"), Some(&6));
    assert_eq!(c3.get(&"c"), None);
    assert_eq!(c3.get(&"d"), None);
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
