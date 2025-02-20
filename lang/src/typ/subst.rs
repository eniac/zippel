use itertools::Itertools;

use share::{Ctx, Set};
use crate::id::Tid;
use crate::typ::{Kind, TypeVars};
use crate::range::Range;

/// Represents a possible valuation of sized type variables
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Substs<T>(pub Ctx<Tid, T>);

/// Substitute type variables with sizes
pub type SizeSubsts = Substs<usize>;

/// Aliasing for type variables
pub type AliasSubsts = Substs<Set<Tid>>;


impl<T> Substs<T> {
    pub fn new() -> Self {
        Substs(Ctx::new())
    }
}

impl<T> IntoIterator for Substs<T> {
    type Item = (Tid, T);
    type IntoIter = std::vec::IntoIter<(Tid, T)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> Iterator for Substs<T> {
    type Item = (Tid, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<T> FromIterator<(Tid, T)> for Substs<T> {
    fn from_iter<I: IntoIterator<Item = (Tid, T)>>(iter: I) -> Self {
        Substs(Ctx::from_iter(iter))
    }
}

impl SizeSubsts {

    // Collect all sized type variables, for example [N: 0..10, M: 3,2..7]
    // and take all possible combinations of sizes
    // Warning: exponential, the idea is the are few sizes (or even 1)
    pub fn from_typevars(tv: &TypeVars) -> Set<Self> {
        let typevar_ranges: Vec<(Tid, Range<usize>)> =
            tv.clone()
                .into_iter()
                .filter_map(|tv|
                    match tv.kind {
                        Kind::Range(r) => Some((tv.id.clone(), r.clone())),
                        _ => None
                    }).collect();


        // Take the multi_cartesian_product of all ranges to get all possible size
        // substitutions
        typevar_ranges.into_iter()
            .map(|(tid, r)|
                r.into_iter().map(|i| (tid.clone(), i)).collect::<Vec<_>>())
            .multi_cartesian_product()
            .map(Substs::from)
            .collect::<Set<SizeSubsts>>()
    }
}

impl AliasSubsts {
    /// Transitive, symmetric closure of the equivalence relation
    pub fn add_equ(&mut self, a: &Tid, b: &Tid) -> bool {
        // Get or create sets for both a and b
        let mut a_set = self.entry(a.clone()).or_insert_with(Set::new);
        a_set.insert(b.clone());

        let mut b_set = self.entry(b.clone()).or_insert_with(Set::new);
        b_set.insert(a.clone());

        // Get the union of both sets
        let mut combined = a_set.union(b_set);

        combined.insert(a.clone());
        combined.insert(b.clone());

        // Update all related entries to maintain transitive closure
        for item in combined.clone() {
            self.insert(item, combined.clone());
        }
    }

    pub fn get_equivalents(&self, tid: &Tid) -> &Set<Tid> {
        self.get(tid).unwrap_or(&Set::new())
    }
}

impl<T> From<Vec<(Tid, T)>> for Substs<T> {
    fn from(v: Vec<(Tid, T)>) -> Self {
        Substs(Ctx::from(v))
    }
}

#[cfg(test)] use crate::decl::Decl;
#[test]
fn size_substs_from_typevars() {
    let decl = Decl::from_str("fn test<N: 0..4, M: 1..3>(public a: N) -> N { 1 }").unwrap();
    assert_eq!(SizeSubsts::from_typevars(decl.typevars()),
        Set::from(vec![
            SizeSubsts::from(vec![(Tid::from("N"), 0), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 1), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 3), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 0), (Tid::from("M"), 2)]),
            SizeSubsts::from(vec![(Tid::from("N"), 1), (Tid::from("M"), 2)]),
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 2)]),
            SizeSubsts::from(vec![(Tid::from("N"), 3), (Tid::from("M"), 2)])
        ]));
}

#[test]
fn alias_substs_equ_clos() {
    let mut alias = AliasSubsts::new();
    alias.add_equ(&Tid::from("A"), &Tid::from("B"));
    alias.add_equ(&Tid::from("B"), &Tid::from("C"));
    alias.add_equ(&Tid::from("D"), &Tid::from("E"));

    assert_eq!(alias.get_equivalents(&Tid::from("A")), &Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")]));
    assert_eq!(alias.get_equivalents(&Tid::from("B")), &Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")]));
    assert_eq!(alias.get_equivalents(&Tid::from("C")), &Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")]));
    assert_eq!(alias.get_equivalents(&Tid::from("D")), &Set::from(vec![Tid::from("D"), Tid::from("E")]));
    assert_eq!(alias.get_equivalents(&Tid::from("E")), &Set::from(vec![Tid::from("D"), Tid::from("E")]));
}
