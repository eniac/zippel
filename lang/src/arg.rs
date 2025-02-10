use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;

use crate::id::Vid;
use crate::typ::{Size, Typ, Qualifier};
use crate::parser::*;

/// `Arg` represents an argument in the Zippel language, including its identifier, type, and principals.
///
///     **Zippel Code:**
///     ```zippel
///     fn foo<Verifier>(a: F  & Verifier) { ... }
///     ```
///
///     In this example, `a` is the identifier of the argument, `F` is the type and `Verifier` is
///     the principal.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Arg<N> {
    pub qualifier: Qualifier,
    pub id: Vid,
    pub typ: Typ<N>,
}

impl<N> Arg<N> {
    pub fn new<'a>(qualifier: Qualifier, id: &'a str, typ: Typ<N>) -> Self {
        Arg { qualifier, id: Vid::new(id.clone()), typ }
    }
}

impl<'pest> FromPest<'pest> for Arg<Size> {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::arg => {
                let mut inner = pair.into_inner();
                match inner.as_rule() {
                    Rule::qualifier => {
                        let qualifier = Qualifier::from_pest(&mut Pairs::single(inner.next().ok_or(ConversionError::NoMatch)?))?;
                        let id = Vid::from_pest(&mut Pairs::single(inner.next().ok_or(ConversionError::NoMatch)?))?;
                        let typ = Typ::from_pest(&mut inner)?;
                        Ok(Arg::new(qualifier, id, typ))
                    }
                    _ => unreachable!()
                }
            },
            _ => unreachable!()
        }
    }
}

#[test]
fn arg_parser() {
    let ex1 = "public a: F";
    let mut pairs = ZippelParser::parse(Rule::arg, ex1).expect("Failure to parse");
    assert_eq!(
        Arg::from_pest(&mut pairs),
        Ok(Arg::new(Qualifier::Public, "a", Typ::base("F")))
    );

    let ex2 = "private foo: X";
    let mut pairs = ZippelParser::parse(Rule::arg, ex2).expect("Failure to parse");
    assert_eq!(
        Arg::from_pest(&mut pairs),
        Ok(Arg::new(Qualifier::Private, "foo", Typ::base("X")))
    );
}
