use itertools::Itertools;

use share::{Ctx, Set};
use crate::id::{Tid, TidSubst};
use crate::typ::{Kind, UTypeVars};
use crate::typ::range::Range;
use share::traversal::ToTraversal1;
use thiserror::Error;

#[derive(Error, PartialEq, Debug)]
pub enum SubstError {
    #[error("Size {1} for typevar {0} is outside its declared range")]
    OutOfRange(Tid, usize),
}

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
    pub fn get(&self, tid: &Tid) -> Option<&T> {
        self.0.get(tid)
    }
    pub fn contains(&self, tid: &Tid) -> bool {
        self.0.contains(tid)
    }
    pub fn keys(&self) -> Set<Tid> {
        self.0.keys()
    }
}

impl<T: Clone> IntoIterator for Substs<T> {
    type Item = (Tid, T);
    type IntoIter = share::CtxConsumingIter<(Tid, T)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Clone> FromIterator<(Tid, T)> for Substs<T> {
    fn from_iter<I: IntoIterator<Item = (Tid, T)>>(iter: I) -> Self {
        Substs(Ctx::from_iter(iter))
    }
}

impl SizeSubsts {

    // Collect all sized type variables, for example [N: 0..10, M: 3,2..7]
    // and take all possible combinations of sizes.
    // If `sizes` provides a value for a Range typevar, pin to that value
    // (generate only the singleton) after validating it's within range.
    // Warning: exponential, the idea is there are few sizes (or even 1)
    pub fn from_typevars(tv: &UTypeVars, sizes: &Ctx<Tid, usize>) -> Result<Set<Self>, SubstError> {
        let typevar_ranges: Vec<(Tid, Range<usize>)> =
            tv.clone()
                .into_iter()
                .filter_map(|tv|
                    match tv.kind {
                        Kind::Range(r) => {
                            let cr = r.traverse1(&mut |s| s.eval(sizes)).ok()?;
                            Some((tv.id.clone(), cr))
                        },
                        _ => None
                    }).collect();

        // Pin ranges that have an explicit value in `sizes`
        let pinned_ranges: Vec<(Tid, Range<usize>)> = typevar_ranges.into_iter()
            .map(|(tid, range)| {
                if let Some(&pinned) = sizes.get(&tid) {
                    if range.contains(pinned) {
                        Ok((tid, Range::singleton(pinned)))
                    } else {
                        Err(SubstError::OutOfRange(tid, pinned))
                    }
                } else {
                    Ok((tid, range))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        // If there are no type variables, return the empty substitution
        if pinned_ranges.is_empty() {
            return Ok(Set::from(vec![SizeSubsts::new()]));
        }

        // Take the multi_cartesian_product of all ranges to get all possible size
        // substitutions
        Ok(pinned_ranges.into_iter()
            .map(|(tid, r)|
                r.into_iter().map(|i| (tid.clone(), i)).collect::<Vec<_>>())
            .multi_cartesian_product()
            .map(Substs::from)
            .collect::<Set<SizeSubsts>>())
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

    /// Check if a Tid is a representative of its equivalence class
    pub fn is_repr(&self, tid: &Tid) -> bool {
        self.get_repr(tid) == Some(tid.clone())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Tid, &Tid)> {
        self.0.iter().map(|(k, v)| (k, v.iter().min().unwrap()))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn clear(&mut self) {
        self.0.clear();
    }

    pub fn tid_subst<T: TidSubst>(&self, on: &mut T) {
        for k in self.0.keys() {
            on.tid_subst(&k, &self.get_repr(&k).unwrap());
        }
    }

}

impl<T: Clone> From<Vec<(Tid, T)>> for Substs<T> {
    fn from(v: Vec<(Tid, T)>) -> Self {
        Substs(Ctx::from(v))
    }
}

#[cfg(test)] use crate::ast::decl::Decl;
#[test]
fn size_substs_from_typevars() {
    let decl = Decl::from_str("fn test<N: 0..4, M: 1..3>(public a: N) -> N { 1 }").unwrap();
    assert_eq!(SizeSubsts::from_typevars(&decl.sig.typevars, &Ctx::new()).unwrap(),
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
fn size_substs_pinning() {
    // Pin N=2 within range 0..4 — should produce only N=2 combinations
    let decl = Decl::from_str("fn test<N: 0..4, M: 1..3>(public a: N) -> N { 1 }").unwrap();
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("N"), &2);
    assert_eq!(SizeSubsts::from_typevars(&decl.sig.typevars, &sizes).unwrap(),
        Set::from(vec![
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 2)]),
        ]));
}

#[test]
fn size_substs_pinning_out_of_range() {
    // Pin N=10 outside range 0..4 — should error
    let decl = Decl::from_str("fn test<N: 0..4>(public a: N) -> N { 1 }").unwrap();
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("N"), &10);
    assert_eq!(
        SizeSubsts::from_typevars(&decl.sig.typevars, &sizes),
        Err(SubstError::OutOfRange(Tid::from("N"), 10))
    );
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
