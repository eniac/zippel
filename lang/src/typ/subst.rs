use crate::ast::range::{CRangeIter, RangeError};
use crate::ast::size::EvalError;
use crate::ast::{Range, Size};
use crate::id::Tid;
use crate::typ::{Kind, UTypeVars};
use share::traversal::ToTraversal1;
use share::{Ctx, Set};
use thiserror::Error;

/// Failure while building a [`SizeSubsts`] valuation from a signature's type variables.
#[derive(Error, Debug)]
pub enum SubstError {
    /// A range bound could not be evaluated to a concrete `usize`, typically because
    /// it mentions a size variable that is not yet bound.
    #[error("Error evaluating range for typevar {0}: {1}")]
    Eval(Tid, EvalError),
    /// A range has an unrepresentable end or a zero step.
    #[error("Invalid range for typevar {0}: {1}")]
    InvalidRange(Tid, RangeError),
    /// Default selection must not erase a declaration-range branch.
    #[error("Default sizes leave an empty size range for typevar {0}")]
    EmptyRange(Tid),
}

/// Represents a possible valuation of sized type variables
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Substs<T>(pub Ctx<Tid, T>);

/// Substitute type variables with sizes
pub type SizeSubsts = Substs<usize>;

impl<T> Default for Substs<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Substs<T> {
    /// Creates an empty substitution.
    pub fn new() -> Self {
        Substs(Ctx::new())
    }
    /// Looks up the value bound to `tid`, or `None` when it is unbound.
    pub fn get(&self, tid: &Tid) -> Option<&T> {
        self.0.get(tid)
    }
    /// Returns whether `tid` is bound by this substitution.
    pub fn contains(&self, tid: &Tid) -> bool {
        self.0.contains(tid)
    }
    /// Returns the set of type variables bound by this substitution.
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
    /// Enumerates substitutions for the signature's range-kinded type variables.
    ///
    /// Expands variables in declaration order. Each range is evaluated using `sizes`
    /// and the range variables already chosen on that branch; those local bindings
    /// take precedence over supplied values. Later ranges can therefore depend on earlier
    /// choices, so the result need not be a Cartesian product of independent ranges.
    /// Singleton ranges also bind a variable; empty ranges discard their branch.
    ///
    /// Returned substitutions contain only range-variable bindings. Other kinds are
    /// skipped; with no range variables, the result contains one empty substitution.
    ///
    /// # Errors
    /// Returns [`SubstError::Eval`] if a range expression cannot be evaluated under
    /// the supplied values and earlier bindings. Returns [`SubstError::InvalidRange`]
    /// for an unrepresentable singleton end or a zero step.
    pub fn from_typevars(tv: &UTypeVars, sizes: &Ctx<Tid, usize>) -> Result<Set<Self>, SubstError> {
        Self::iter_typevars(tv, sizes, false).collect()
    }

    /// Streams range assignments, optionally rejecting every empty dependent branch.
    pub(crate) fn iter_typevars(
        tv: &UTypeVars,
        sizes: &Ctx<Tid, usize>,
        require_nonempty: bool,
    ) -> SizeSubstsIter {
        SizeSubstsIter {
            ranges: tv
                .iter()
                .filter_map(|tv| match &tv.kind {
                    Kind::Range(range) => Some((tv.id.node.clone(), range.clone())),
                    _ => None,
                })
                .collect(),
            sizes: sizes.clone(),
            require_nonempty,
            stack: Vec::new(),
            started: false,
            finished: false,
        }
    }
}

struct RangeFrame {
    partial: Ctx<Tid, usize>,
    values: CRangeIter,
}

/// Depth-first expansion stores one iterator per range, never its full Cartesian product.
pub(crate) struct SizeSubstsIter {
    ranges: Vec<(Tid, Range<Size>)>,
    sizes: Ctx<Tid, usize>,
    require_nonempty: bool,
    stack: Vec<RangeFrame>,
    started: bool,
    finished: bool,
}

impl SizeSubstsIter {
    fn push_frame(&mut self, partial: Ctx<Tid, usize>) -> Result<(), SubstError> {
        let (id, range) = &self.ranges[self.stack.len()];
        let mut ctx = self.sizes.clone();
        for (name, value) in partial.iter() {
            ctx.insert(name, value);
        }
        let range = range
            .clone()
            .traverse1(&mut |size| size.eval(&ctx))
            .map_err(|error| SubstError::Eval(id.clone(), error))?;
        let end = range
            .checked_end()
            .map_err(|error| SubstError::InvalidRange(id.clone(), error))?;
        if range.step() == 0 {
            return Err(SubstError::InvalidRange(
                id.clone(),
                RangeError::RangeOrder(range.start(), 0, end),
            ));
        }
        if self.require_nonempty && range.start() >= end {
            return Err(SubstError::EmptyRange(id.clone()));
        }
        self.stack.push(RangeFrame {
            partial,
            values: range.into_iter(),
        });
        Ok(())
    }

    fn fail(&mut self, error: SubstError) -> Option<Result<SizeSubsts, SubstError>> {
        self.finished = true;
        self.stack.clear();
        Some(Err(error))
    }
}

impl Iterator for SizeSubstsIter {
    type Item = Result<SizeSubsts, SubstError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        if !self.started {
            self.started = true;
            if self.ranges.is_empty() {
                self.finished = true;
                return Some(Ok(SizeSubsts::new()));
            }
            if let Err(error) = self.push_frame(Ctx::new()) {
                return self.fail(error);
            }
        }
        while let Some(frame) = self.stack.last_mut() {
            let Some(value) = frame.values.next() else {
                self.stack.pop();
                continue;
            };
            let depth = self.stack.len() - 1;
            let mut partial = self.stack[depth].partial.clone();
            partial.insert(&self.ranges[depth].0, &value);
            if depth + 1 == self.ranges.len() {
                return Some(Ok(Substs(partial)));
            }
            if let Err(error) = self.push_frame(partial) {
                return self.fail(error);
            }
        }
        self.finished = true;
        None
    }
}

impl<T: Clone> From<Vec<(Tid, T)>> for Substs<T> {
    fn from(v: Vec<(Tid, T)>) -> Self {
        Substs(Ctx::from(v))
    }
}

#[cfg(test)]
use crate::parser::parse_decls;

#[cfg(test)]
fn parse_decl(src: &str) -> crate::ast::decl::UDecl {
    let (mut decls, errors) = parse_decls(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    decls.pop().map(|s| s.node).unwrap()
}

#[test]
fn size_substs_from_typevars() {
    let decl = parse_decl("fn test<N: 0..4, M: 1..3>(instance a: N) -> N { 1 }");
    assert_eq!(
        SizeSubsts::from_typevars(&decl.sig.typevars, &Ctx::new()).unwrap(),
        Set::from(vec![
            SizeSubsts::from(vec![(Tid::from("N"), 0), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 1), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 3), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 0), (Tid::from("M"), 2)]),
            SizeSubsts::from(vec![(Tid::from("N"), 1), (Tid::from("M"), 2)]),
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 2)]),
            SizeSubsts::from(vec![(Tid::from("N"), 3), (Tid::from("M"), 2)])
        ])
    );
}

#[test]
fn size_substs_never_pin_a_range_from_sizes() {
    // A size named like a range variable does not pin it: `N` still takes every
    // value of `0..4`.
    let decl = parse_decl("fn test<N: 0..4, M: 1..3>(instance a: N) -> N { 1 }");
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("N"), &2);
    assert_eq!(
        SizeSubsts::from_typevars(&decl.sig.typevars, &sizes).unwrap(),
        SizeSubsts::from_typevars(&decl.sig.typevars, &Ctx::new()).unwrap(),
    );
}

#[test]
fn size_substs_dependent_range_from_singleton_typevar() {
    let decl = parse_decl(
        "fn test<F: Field, NUM_VARS_CONST: 10, V: 2..NUM_VARS_CONST>(instance a: [F; V]) -> F { a[0] }",
    );

    let substs = SizeSubsts::from_typevars(&decl.sig.typevars, &Ctx::new()).unwrap();
    let v_values: Set<usize> = substs
        .iter()
        .map(|subst| *subst.get(&Tid::from("V")).unwrap())
        .collect();

    assert_eq!(v_values, Set::from(vec![2, 3, 4, 5, 6, 7, 8, 9]));
    assert!(
        substs
            .iter()
            .all(|subst| subst.get(&Tid::from("NUM_VARS_CONST")) == Some(&10))
    );
}
