use crate::id::{Tid, TidSubst};
use crate::typ::kind::Kind;
use crate::parser::*;
use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use share::{Pretty, Ctx, DocAllocator, DocBuilder, BoxAllocator};
use std::fmt;

/// A type variable with an associated kind
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVar { pub id: Tid, pub kind: Kind }
impl TypeVar {
    pub fn new<'a>(id: &'a str, kind: Kind) -> Self {
        TypeVar { id: Tid::new(id), kind }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct TypeVars(pub Vec<TypeVar>);

impl TypeVars {
    pub fn remove(&mut self, id: &Tid) {
        self.0.retain(|tvar| &tvar.id != id);
    }

    pub fn iter(&self) -> std::slice::Iter<TypeVar> {
        self.0.iter()
    }

    pub fn ids(&self) -> Vec<Tid> {
        self.0.iter().map(|tvar| tvar.id.clone()).collect()
    }

    pub fn contains(&self, id: &Tid) -> bool {
        self.0.iter().any(|tvar| &tvar.id == id)
    }
    pub fn to_ctx(&self) -> Ctx<Tid, Kind> {
        self.0.iter().map(|tvar| (tvar.id.clone(), tvar.kind.clone())).collect()
    }
}

impl IntoIterator for TypeVars {
    type Item = TypeVar;
    type IntoIter = std::vec::IntoIter<TypeVar>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<TypeVar> for TypeVars {
    fn from_iter<I: IntoIterator<Item = TypeVar>>(iter: I) -> Self {
        TypeVars(iter.into_iter().collect())
    }
}

impl<const L: usize> From<[TypeVar; L]> for TypeVars {
    fn from(arr: [TypeVar; L]) -> Self {
        TypeVars(arr.to_vec())
    }
}

impl TidSubst for TypeVar {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        if &self.id == from {
            self.id = to.clone();
        }
    }
}

impl TidSubst for TypeVars {
    fn tid_subst(&mut self, from: &Tid, to: &Tid) {
        self.0.iter_mut().for_each(|tvar| tvar.tid_subst(from, to));
    }
}

impl<'pest> FromPest<'pest> for TypeVar {
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

impl<'pest> FromPest<'pest> for TypeVars {
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
                    let tv = TypeVar::from_pest(&mut Pairs::single(pair))?;
                    // No duplicate type variables
                    if tvars.iter().any(|t: &TypeVar| t.id == tv.id) {
                        return Err(ConversionError::Malformed(InputError::DuplicateTid(tv.id)));
                    }
                    // Check the kinds are correct
                    match tv.kind.clone() {
                        Kind::Pairing(g1, g2) => {
                            // Is [g1] a group kind?
                            let tv1 = tvars.iter().find(|tv| tv.id == g1)
                                .ok_or(ConversionError::Malformed(InputError::KindNotFound(g1.clone())))?;
                            if !tv1.kind.is_group() {
                                return Err(ConversionError::Malformed(InputError::PairingGroup(g1.clone(), g2, g1.clone(), tv1.kind.clone())));
                            }
                            // Is [g2] a group kind?
                            let tv2 = tvars.iter().find(|tv| tv.id == g2)
                                .ok_or(ConversionError::Malformed(InputError::KindNotFound(g2.clone())))?;
                            if !tv2.kind.is_group() {
                                return Err(ConversionError::Malformed(InputError::PairingGroup(g1, g2.clone(), g2, tv2.kind.clone())));
                            }
                            tvars.push(tv);
                        },
                        Kind::Scalar(f) => {
                            // Is [f] a group kind?
                            let tvf = tvars.iter().find(|tv| tv.id == f)
                                .ok_or(ConversionError::Malformed(InputError::KindNotFound(f.clone())))?;
                            if ! (tvf.kind == Kind::Group) {
                                return Err(ConversionError::Malformed(InputError::ScalarGroup(f.clone(), tvf.kind.clone())));
                            }
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
impl<'a, D, A> Pretty<'a, D, A> for TypeVar
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
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

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVar as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<'a, D, A> Pretty<'a, D, A> for TypeVars
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
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

impl fmt::Display for TypeVars {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <TypeVars as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)] use pest::Parser;
#[test]
fn typevars_parser() {
    let ex = "A: Field, B1: Group, B2: Group, D: Scalar<B2>, E: Pairing<B1, B2>, F: 0..10";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex).unwrap();
    assert_eq!(
        TypeVars::from_pest(&mut pairs),
        Ok(TypeVars::from([
            TypeVar::new("A", Kind::Field),
            TypeVar::new("B1", Kind::Group),
            TypeVar::new("B2", Kind::Group),
            TypeVar::new("D", Kind::scalar("B2")),
            TypeVar::new("E", Kind::pairing("B1", "B2")),
            TypeVar::new("F", Kind::range(0, 1, 10))
        ]))
    );

    let ex_bad_dup = "A: Field, A: Group";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_bad_dup).unwrap();
    assert_eq!(
        TypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::DuplicateTid(Tid::new("A"))))
    );

    let ex_bad_multiplicative = "A: Field, B: Group, D: Scalar<A>";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_bad_multiplicative).unwrap();
    assert_eq!(
        TypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::ScalarGroup(Tid::new("A"), Kind::Field)))
    );

    let ex_bad_pairing = "A: Field, B: Group, E: Pairing<A, B>";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_bad_pairing).unwrap();
    assert_eq!(
        TypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::PairingGroup(Tid::new("A"), Tid::new("B"), Tid::new("A"), Kind::Field)))
    );

    let ex_reserved = "Bool: Field";
    let mut pairs = ZippelParser::parse(Rule::tvars, ex_reserved).unwrap();
    assert_eq!(
        TypeVars::from_pest(&mut pairs),
        Err(ConversionError::Malformed(InputError::ReservedType))
    );
}
