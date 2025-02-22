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
    type IntoIter = std::collections::btree_map::IntoIter<Tid, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
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
    /// Transitive, reflexive, symmetric closure of the equivalence relation
    pub fn add_equ(&mut self, a: &Tid, b: &Tid) -> Tid {
        // Quick return if a and b are equal
        if a == b {
            return a.clone();
        }

        // Create a new equivalence class with [a, b]
        let mut eqclass = Set::from([a.clone(), b.clone()]);

        // Add equivalence classes of [a] into [eqclass]
        for v in self.0.get(a).map(|x|x.clone()).unwrap_or(Set::new()) {
            eqclass.insert(v.clone());
        }

        // Add equivalence classes of [b] into [eqclass]
        for v in self.0.get(b).map(|x|x.clone()).unwrap_or(Set::new()) {
            eqclass.insert(v.clone());
        }

        // Update all related entries to maintain transitive closure
        for item in eqclass.iter() {
            self.0.insert(item, &eqclass);
        }

        // Return the representative of the class as the lowest lexicographic [Tid]
        // TODO: Perhaps a better way would be to return the [Tid] with less dependencies
        // (i.e. the one with the lowest number of type variables)
        eqclass.into_iter().min().unwrap()
    }

    /// Union two equivalence classes
    pub fn union_equ(&mut self, other: &mut Self) {
        for (tid, set) in other.0.iter() {
            for item in set.iter() {
                self.add_equ(tid, item);
            }
        }
    }

    /// Return the equivalence class of a type variable
    pub fn get_equivalents(&self, tid: &Tid) -> Set<Tid> {
        if let Some(x) = self.0.get(tid) {
            x.clone()
        } else {
            Set::new()
        }
    }

    /// Return the representative of the equivalence class of a type variable
    pub fn get_repr(&self, tid: &Tid) -> Option<Tid> {
        self.get_equivalents(tid).into_iter().min()
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

    assert_eq!(alias.get_equivalents(&Tid::from("A")), Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")]));
    assert_eq!(alias.get_equivalents(&Tid::from("B")), Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")]));
    assert_eq!(alias.get_equivalents(&Tid::from("C")), Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")]));
    assert_eq!(alias.get_equivalents(&Tid::from("D")), Set::from(vec![Tid::from("D"), Tid::from("E")]));
    assert_eq!(alias.get_equivalents(&Tid::from("E")), Set::from(vec![Tid::from("D"), Tid::from("E")]));

    assert_eq!(alias.get_repr(&Tid::from("B")), Some(Tid::from("A")));
    assert_eq!(alias.get_repr(&Tid::from("C")), Some(Tid::from("A")));
    assert_eq!(alias.get_repr(&Tid::from("D")), Some(Tid::from("D")));
    assert_eq!(alias.get_repr(&Tid::from("E")), Some(Tid::from("D")));
}
