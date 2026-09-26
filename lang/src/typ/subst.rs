use crate::ast::size::EvalError;
use crate::id::{Tid, TidSubst};
use crate::typ::{Kind, UTypeVars};
use share::traversal::ToTraversal1;
use share::{Ctx, Set};
use thiserror::Error;

/// Failure while building a [`SizeSubsts`] valuation from a signature's type variables.
#[derive(Error, Debug)]
pub enum SubstError {
    /// A caller-supplied size pins a `Range` type variable to a value outside the
    /// range declared for it.
    #[error("Size {1} for typevar {0} is outside its declared range")]
    OutOfRange(Tid, usize),
    /// A range bound could not be evaluated to a concrete `usize`, typically because
    /// it mentions a size variable that is not yet bound.
    #[error("Error evaluating range for typevar {0}: {1}")]
    Eval(Tid, EvalError),
}

/// Represents a possible valuation of sized type variables
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone)]
pub struct Substs<T>(pub Ctx<Tid, T>);

/// Substitute type variables with sizes
pub type SizeSubsts = Substs<usize>;

/// Aliasing for type variables
pub type AliasSubsts = Substs<Set<Tid>>;

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
    /// Enumerates every concrete size valuation admitted by a signature's type
    /// variables.
    ///
    /// Each `Range`-kinded type variable contributes one dimension of the product;
    /// `sizes` pins a variable to a single value instead of expanding it. Non-range
    /// type variables are skipped, and a signature with no range variables yields the
    /// single empty substitution.
    ///
    /// # Errors
    /// Returns [`SubstError::OutOfRange`] when a pinned size lies outside the
    /// variable's declared range, and [`SubstError::Eval`] when a range bound cannot
    /// be evaluated with the sizes bound so far.
    // Collect all sized type variables, for example [N: 0..10, M: 3,2..7]
    // and take all possible combinations of sizes.
    // If `sizes` provides a value for a Range typevar, pin to that value
    // (generate only the singleton) after validating it's within range.
    // Range bounds may reference earlier Range typevars in the same signature;
    // expand declarations left-to-right so dependent bounds such as
    // `NUM: 10, V: 2..NUM` can be resolved without an external size binding.
    // Warning: exponential, the idea is there are few sizes (or even 1)
    pub fn from_typevars(tv: &UTypeVars, sizes: &Ctx<Tid, usize>) -> Result<Set<Self>, SubstError> {
        let mut partials: Vec<Ctx<Tid, usize>> = vec![Ctx::new()];
        let mut saw_range = false;

        for tv in tv.clone().into_iter() {
            let tv = tv.node;
            let Kind::Range(r) = tv.kind else {
                continue;
            };
            saw_range = true;

            let mut next = Vec::new();
            for partial in partials.into_iter() {
                let eval_ctx = Self::eval_context_for_partial(sizes, &partial);

                let concrete_range = r
                    .clone()
                    .traverse1(&mut |s| s.eval(&eval_ctx))
                    .map_err(|e| SubstError::Eval(tv.id.node.clone(), e))?;

                if let Some(&pinned) = sizes.get(&tv.id.node) {
                    if concrete_range.contains(pinned) {
                        let mut pinned_partial = partial;
                        pinned_partial.insert(&tv.id.node, &pinned);
                        next.push(pinned_partial);
                    } else {
                        return Err(SubstError::OutOfRange(tv.id.node.clone(), pinned));
                    }
                } else {
                    for value in concrete_range {
                        let mut expanded = partial.clone();
                        expanded.insert(&tv.id.node, &value);
                        next.push(expanded);
                    }
                }
            }
            partials = next;
        }

        // If there are no range type variables, return the empty substitution.
        if !saw_range {
            return Ok(Set::from(vec![SizeSubsts::new()]));
        }

        Ok(partials.into_iter().map(Substs).collect())
    }

    fn eval_context_for_partial(
        sizes: &Ctx<Tid, usize>,
        partial: &Ctx<Tid, usize>,
    ) -> Ctx<Tid, usize> {
        let mut eval_ctx = sizes.clone();
        for (k, v) in partial.iter() {
            eval_ctx.insert(k, v);
        }
        eval_ctx
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
        for v in self.0.get(a).cloned().unwrap_or(Set::new()) {
            eqclass.insert(v.clone());
        }

        // Add equivalence classes of [b] into [eqclass]
        for v in self.0.get(b).cloned().unwrap_or(Set::new()) {
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

    /// Iterates over the bound type variables paired with the representative of their
    /// equivalence class.
    ///
    /// # Panics
    /// Panics if an equivalence class stored in this substitution is empty, which
    /// [`AliasSubsts::add_equ`] never produces.
    pub fn iter(&self) -> impl Iterator<Item = (&Tid, &Tid)> {
        self.0.iter().map(|(k, v)| (k, v.iter().min().unwrap()))
    }

    /// Returns whether no aliasing has been recorded.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Drops every recorded alias.
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Rewrites every aliased type variable in `on` to its class representative,
    /// canonicalising a type or expression after unification.
    ///
    /// # Panics
    /// Panics if an equivalence class stored in this substitution is empty, which
    /// [`AliasSubsts::add_equ`] never produces.
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
fn size_substs_pinning() {
    // Pin N=2 within range 0..4 — should produce only N=2 combinations
    let decl = parse_decl("fn test<N: 0..4, M: 1..3>(instance a: N) -> N { 1 }");
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("N"), &2);
    assert_eq!(
        SizeSubsts::from_typevars(&decl.sig.typevars, &sizes).unwrap(),
        Set::from(vec![
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 1)]),
            SizeSubsts::from(vec![(Tid::from("N"), 2), (Tid::from("M"), 2)]),
        ])
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

#[test]
fn size_substs_pinning_out_of_range() {
    // Pin N=10 outside range 0..4 — should error
    let decl = parse_decl("fn test<N: 0..4>(instance a: N) -> N { 1 }");
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("N"), &10);
    assert!(matches!(
        SizeSubsts::from_typevars(&decl.sig.typevars, &sizes),
        Err(SubstError::OutOfRange(_, 10))
    ));
}

#[test]
fn alias_substs_equ_clos() {
    let mut alias = AliasSubsts::new();
    alias.add_equ(&Tid::from("A"), &Tid::from("B"));
    alias.add_equ(&Tid::from("B"), &Tid::from("C"));
    alias.add_equ(&Tid::from("D"), &Tid::from("E"));

    assert_eq!(
        alias.get_equivalents(&Tid::from("A")),
        Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")])
    );
    assert_eq!(
        alias.get_equivalents(&Tid::from("B")),
        Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")])
    );
    assert_eq!(
        alias.get_equivalents(&Tid::from("C")),
        Set::from(vec![Tid::from("A"), Tid::from("B"), Tid::from("C")])
    );
    assert_eq!(
        alias.get_equivalents(&Tid::from("D")),
        Set::from(vec![Tid::from("D"), Tid::from("E")])
    );
    assert_eq!(
        alias.get_equivalents(&Tid::from("E")),
        Set::from(vec![Tid::from("D"), Tid::from("E")])
    );

    assert_eq!(alias.get_repr(&Tid::from("B")), Some(Tid::from("A")));
    assert_eq!(alias.get_repr(&Tid::from("C")), Some(Tid::from("A")));
    assert_eq!(alias.get_repr(&Tid::from("D")), Some(Tid::from("D")));
    assert_eq!(alias.get_repr(&Tid::from("E")), Some(Tid::from("D")));
}

#[test]
fn alias_substs_tid_subst() {
    let mut alias = AliasSubsts::new();
    alias.add_equ(&Tid::from("A"), &Tid::from("B"));
    alias.add_equ(&Tid::from("B"), &Tid::from("C"));

    use crate::typ::CTyp;
    let mut typ1 = CTyp::base(&Tid::from("C"));
    alias.tid_subst(&mut typ1);
    assert_eq!(typ1, CTyp::base(&Tid::from("A")));

    let mut typ2 = CTyp::base(&Tid::from("B"));
    alias.tid_subst(&mut typ2);
    assert_eq!(typ2, CTyp::base(&Tid::from("A")));
}
