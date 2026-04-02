use crate::id::{Tid, TidSubst};
use crate::typ::kind::Kind;
use crate::typ::Size;
use crate::typ::range::{Range, RangeTraversal};
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use share::{Pretty, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use share::traversal::ToTraversal1;
use std::fmt;

/// A type variable with an associated kind, parameterized by size type N
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVar<N> { pub id: Tid, pub kind: Kind<N> }

/// Symbolically-sized type variable
pub type UTypeVar = TypeVar<Size>;
/// Concretely-sized type variable
pub type CTypeVar = TypeVar<usize>;

impl<N> TypeVar<N> {
    pub fn new(id: &Tid, kind: &Kind<N>) -> Self where N: Clone {
        TypeVar { id: id.clone(), kind: kind.clone() }
    }
    pub fn new_str(id: &str, kind: Kind<N>) -> Self {
        TypeVar { id: Tid::new(id), kind }
    }
}

/// A collection of type variables, parameterized by size type N
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVars<N>(pub Vec<TypeVar<N>>);

/// Symbolically-sized type variables
pub type UTypeVars = TypeVars<Size>;
/// Concretely-sized type variables
pub type CTypeVars = TypeVars<usize>;

impl<N> TypeVars<N> {
    pub fn remove(&mut self, id: &Tid) {
        self.0.retain(|tvar| &tvar.id != id);
    }

    pub fn iter(&self) -> std::slice::Iter<'_, TypeVar<N>> {
        self.0.iter()
    }

    pub fn ids(&self) -> Vec<Tid> {
        self.0.iter().map(|tvar| tvar.id.clone()).collect()
    }

    pub fn contains(&self, id: &Tid) -> bool {
        self.0.iter().any(|tvar| &tvar.id == id)
    }
    pub fn to_ctx(&self) -> Ctx<Tid, Kind<N>> where N: Clone {
        self.0.iter().map(|tvar| (tvar.id.clone(), tvar.kind.clone())).collect()
    }
}

impl<N> IntoIterator for TypeVars<N> {
    type Item = TypeVar<N>;
    type IntoIter = std::vec::IntoIter<TypeVar<N>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N> FromIterator<TypeVar<N>> for TypeVars<N> {
    fn from_iter<I: IntoIterator<Item = TypeVar<N>>>(iter: I) -> Self {
        TypeVars(iter.into_iter().collect())
    }
}

impl<N, const L: usize> From<[TypeVar<N>; L]> for TypeVars<N> {
    fn from(arr: [TypeVar<N>; L]) -> Self {
        TypeVars(arr.into_iter().collect())
    }
}

impl<N> TidSubst for TypeVar<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        if &self.id == from {
            self.id = to.clone();
        }
    }
}

impl<N> TidSubst for TypeVars<N> {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|tvar| tvar.tid_subst(from, to));
    }
}

/// Traversal over the size parameter N
impl<N> ToTraversal1<N> for TypeVar<N> {
    type Output<Z> = TypeVar<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<TypeVar<Z>, E> {
        Ok(TypeVar { id: self.id, kind: self.kind.traverse1(f)? })
    }
}

/// Traversal over the size parameter N
impl<N> ToTraversal1<N> for TypeVars<N> {
    type Output<Z> = TypeVars<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<TypeVars<Z>, E> {
        Ok(TypeVars(self.0.into_iter().map(|tv| tv.traverse1(f)).collect::<Result<_, _>>()?))
    }
}

/// Range traversal for TypeVar
impl<N: Clone> RangeTraversal<N> for TypeVar<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(TypeVar { id: self.id, kind: self.kind.range_traverse(f)? })
    }
}

/// Range traversal for TypeVars
impl<N: Clone> RangeTraversal<N> for TypeVars<N> {
    fn range_traverse<E>(self, f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>) -> Result<Self, E> {
        Ok(TypeVars(self.0.into_iter().map(|tv| tv.range_traverse(f)).collect::<Result<_, _>>()?))
    }
}

impl<'pest> FromPest<'pest> for UTypeVar {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::tvar => {
                let mut inner = pair.into_inner();
                let id = Tid::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                if id == Tid::new("Bool") {
                    return Err(ConversionError::Malformed(InputError::ReservedType));
                }
                let kind = Kind::from_pest(&mut Pairs::single(inner.next().unwrap()))?;
                Ok(TypeVar { id, kind })
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

impl<'pest> FromPest<'pest> for UTypeVars {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::tvars => {
                let mut tvars = Vec::new();
                for pair in pair.into_inner() {
                    let tv = UTypeVar::from_pest(&mut Pairs::single(pair))?;
                    // No duplicate type variables
                    if tvars.iter().any(|t: &UTypeVar| t.id == tv.id) {
                        return Err(ConversionError::Malformed(InputError::DuplicateTid(tv.id)));
                    }
                    // Check the kinds are correct
                    match tv.kind.clone() {
                        Kind::Pairing(g1, g2) => {
                            // Is [g1] a group kind?
                            let tv1 = tvars.iter().find(|tv: &&UTypeVar| tv.id == g1)
                                .ok_or(ConversionError::Malformed(InputError::KindNotFound(g1.clone())))?;
                            if !tv1.kind.is_group() {
                                return Err(ConversionError::Malformed(InputError::PairingGroup(g1.clone(), g2, g1.clone(), tv1.kind.clone())));
                            }
                            // Is [g2] a group kind?
                            let tv2 = tvars.iter().find(|tv: &&UTypeVar| tv.id == g2)
                                .ok_or(ConversionError::Malformed(InputError::KindNotFound(g2.clone())))?;
                            if !tv2.kind.is_group() {
                                return Err(ConversionError::Malformed(InputError::PairingGroup(g1, g2.clone(), g2, tv2.kind.clone())));
                            }
                            tvars.push(tv);
                        },
                        Kind::Scalar(fs) => {
                            fs.iter().all(|f| {
                                // Is [f] in [fs] a group kind?
                                tvars.iter().any(|tv: &UTypeVar| &tv.id == f && tv.kind.is_group())
                            }).then(|| ()).ok_or(ConversionError::Malformed(InputError::ScalarGroup(fs.clone().into(), tv.kind.clone())))?;
                            tvars.push(tv);
                        },
                        _ => tvars.push(tv),
                    }
                }
                Ok(TypeVars(tvars))
            },
            _ => Err(ConversionError::Malformed(InputError::UnexpectedExp(pair))),
        }
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for TypeVar<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            self.id.pretty(allocator),
            allocator.text(": "),
            self.kind.pretty(allocator),
        ])
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone + 'a> fmt::Display for TypeVar<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVar<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, D, A, N> Pretty<'a, D, A> for TypeVars<N>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    N: Pretty<'a, D, A> + Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|tvar| tvar.pretty(allocator)), ", ")
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a, N: Pretty<'a, BoxAllocator, ()> + Clone + 'a> fmt::Display for TypeVars<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVars<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)] use pest::Parser;
#[test]
fn typevars_parser() {
    use crate::typ::range::Range as TRange;

    let ex = "A: Field, B1: Group, B2: Group, D1: Scalar<B2>, D2: Scalar<B1, B2>, E: Pairing<B1, B2>, F: 0..10";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex).unwrap();
    assert_eq!(
        UTypeVars::from_pest(&mut pairs),
        Ok(TypeVars::from([
            TypeVar::new_str("A", Kind::Field),
            TypeVar::new_str("B1", Kind::Group),
            TypeVar::new_str("B2", Kind::Group),
            TypeVar::new_str("D1", Kind::scalar1("B2")),
            TypeVar::new_str("D2", Kind::scalar2("B1", "B2")),
            TypeVar::new_str("E", Kind::pairing("B1", "B2")),
            TypeVar::new_str("F", Kind::Range(TRange {
                start: Size::zero(),
                step: Size::one(),
                end: Size::from(10),
            }))
        ]))
    );

    let ex_bad_dup = "A: Field, A: Group";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_bad_dup).unwrap();
    assert_eq!(
        UTypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::DuplicateTid(Tid::new("A"))))
    );

    let ex_bad_multiplicative = "A: Field, B: Group, D: Scalar<A>";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_bad_multiplicative).unwrap();
    assert!(UTypeVars::from_pest(&mut pairs).is_err());

    let ex_bad_pairing = "A: Field, B: Group, E: Pairing<A, B>";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_bad_pairing).unwrap();
    assert_eq!(
        UTypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::PairingGroup(Tid::new("A"), Tid::new("B"), Tid::new("A"), Kind::Field)))
    );

    let ex_reserved = "Bool: Field";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_reserved).unwrap();
    assert_eq!(
        UTypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::ReservedType))
    );
}
