use itertools::Itertools;
use std::fmt;

use share::{Ctx, Set, Pretty, DocAllocator, DocBuilder, BoxAllocator};
use crate::decl::Decl;
use crate::id::Tid;
use crate::range::Range;

/// Represents a possible valuation of sized type variables
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct SizeSubsts(pub Ctx<Tid, usize>);

impl SizeSubsts {
    pub fn from_decl<N, T>(decl: &Decl<N, T>) -> Set<Self> {
        // Collect all sized type variables, for example [N: 0..10, M: 3,2..7]
        let typevar_ranges: Vec<(Tid, Range<usize>)> =
            decl.typevars().clone().into_iter()
                .filter_map(|tv|
                    Some((tv.id.clone(), tv.get_range()?.clone()))
            ).collect();


        // Take the multi_cartesian_product of all ranges to get all possible size
        // substitutions
        typevar_ranges.into_iter()
            .map(|(tid, r)|
                r.into_iter().map(|i| (tid.clone(), i)).collect::<Vec<_>>())
            .multi_cartesian_product()
            .map(|v| SizeSubsts(Ctx::from(v)))
            .collect::<Set<SizeSubsts>>()
    }
}

impl From<Vec<(Tid, usize)>> for SizeSubsts {
    fn from(v: Vec<(Tid, usize)>) -> Self {
        SizeSubsts(Ctx::from(v))
    }
}

#[test]
fn test_size_substs() {
    let decl = Decl::from_str("fn test<N: 0..3, M: 1..2>(public a: N) -> N { 1 }").unwrap();
    assert_eq!(SizeSubsts::from_decl(&decl),
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


