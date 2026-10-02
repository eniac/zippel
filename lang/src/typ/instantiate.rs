//! Resolving a call to overloaded, generic declarations.
//!
//! [`CSig::resolve_call`] tries each declaration of the called name and picks the most specific
//! one that fits. Trying a declaration opens its signature as an [`Instantiation`]: one solution
//! slot per type parameter. Argument types are inferred before the call is resolved, so they
//! mention only caller type variables, and every binding goes one way, from a callee parameter
//! to a caller variable. Callee names are looked up only among the parameters and caller names
//! only in the caller's kind context, so the two scopes never mix and nothing is renamed.
//! Parameters the arguments leave open are resolved from their kinds, and
//! [`Instantiation::apply`] rewrites callee names to their solutions in one pass.

use std::cell::Cell;

use crate::ast::range::Range;
use crate::ast::sig::{CSig, SigError, Uninferable};
use crate::ast::spanned::Spanned;
use crate::id::{Tid, TidSubst};
use crate::typ::unify::UnifyError;
use crate::typ::{CKind, CTyp, CTyps, Kind};
use share::{Ctx, Set};

/// Why a call resolves to no single declaration.
#[derive(Debug, PartialEq)]
pub enum CallError {
    /// No declaration fits; each one's reason.
    NoMatch(Vec<(CSig, SigError)>),
    /// Several fit and none is at least as specific as all the others; the ones no other is
    /// more specific than.
    Ambiguous(Vec<CSig>),
}

impl CSig {
    /// Resolves a call against `decls`, the declarations of the called name: the one that fits
    /// the arguments and is at least as specific as every other one that fits. Returns it with
    /// its resolved signature and instantiation.
    ///
    /// # Errors
    /// [`CallError::NoMatch`] with each declaration's reason when none fits;
    /// [`CallError::Ambiguous`] with the fitting declarations no other one is more specific
    /// than, when none is at least as specific as all.
    pub fn resolve_call<'a>(
        decls: impl IntoIterator<Item = &'a CSig>,
        args: &CTyps,
        caller: &Ctx<Tid, CKind>,
    ) -> Result<(&'a CSig, CSig, Instantiation), CallError> {
        let mut fitting = Vec::new();
        let mut failures = Vec::new();
        for decl in decls {
            match decl.resolve(args, caller) {
                Ok((sig, inst)) => fitting.push((decl, sig, inst)),
                Err(e) => failures.push((decl.clone(), e)),
            }
        }
        if fitting.is_empty() {
            return Err(CallError::NoMatch(failures));
        }
        let best: Vec<usize> = (0..fitting.len())
            .filter(|&i| {
                fitting
                    .iter()
                    .all(|(other, _, _)| fitting[i].0.at_least_as_specific_as(other))
            })
            .collect();
        if let [i] = best[..] {
            return Ok(fitting.swap_remove(i));
        }
        let strictly_better =
            |a: &CSig, b: &CSig| a.at_least_as_specific_as(b) && !b.at_least_as_specific_as(a);
        let tied = fitting
            .iter()
            .filter(|(d, _, _)| !fitting.iter().any(|(o, _, _)| strictly_better(o, d)))
            .map(|(d, _, _)| (*d).clone())
            .collect();
        Err(CallError::Ambiguous(tied))
    }
    /// Whether every call that fits one of these declarations of the same name also fits the
    /// other, and neither is more specific, so every such call is ambiguous.
    pub(crate) fn interchangeable_with(&self, other: &CSig) -> bool {
        self.name.node == other.name.node
            && self.at_least_as_specific_as(other)
            && other.at_least_as_specific_as(self)
    }

    /// Whether this declaration is at least as specific as `other`: `other` accepts this
    /// declaration's parameter types. Return types are not compared, as calls never see them.
    fn at_least_as_specific_as(&self, other: &CSig) -> bool {
        let params = self.args.iter().map(|a| a.typ.clone()).collect();
        other.matches(&params, &self.typevars.to_ctx()).is_ok()
    }

    /// Resolves this signature against the argument types of a call in a caller whose kind
    /// context is `caller`. Returns the signature in caller names, and the instantiation, which
    /// also rewrites the callee's body when inlining.
    ///
    /// # Errors
    /// Arity or argument mismatches, a parameter whose kind its solution violates, and a
    /// parameter that no argument or kind determines.
    fn resolve(
        &self,
        args: &CTyps,
        caller: &Ctx<Tid, CKind>,
    ) -> Result<(CSig, Instantiation), SigError> {
        let inst = self.matches(args, caller)?;
        // The signature declares every parameter, so this requires all to be solved, and the
        // instantiation can rewrite anything the body mentions.
        let mut sig = self.clone();
        inst.apply(&mut sig)?;
        Ok((sig, inst))
    }

    /// [`Self::resolve`] without requiring every parameter to be solved: the arguments fit and
    /// the solved parameters satisfy their kinds.
    fn matches(&self, args: &CTyps, caller: &Ctx<Tid, CKind>) -> Result<Instantiation, SigError> {
        if self.args.len() != args.len() {
            return Err(SigError::ArityMismatch(self.args.len(), args.len()));
        }
        let mut inst = Instantiation::new(self);
        for (index, (param, arg)) in self.args.iter().zip(args.iter()).enumerate() {
            inst.match_typ(&param.typ.node, &arg.node, caller)
                .map_err(|cause| SigError::Mismatch {
                    index,
                    expected: param.typ.node.clone(),
                    found: arg.node.clone(),
                    cause,
                })?;
        }
        inst.resolve_dependent(caller)?;
        Ok(inst)
    }
}

/// One call site's instantiation of a callee signature. Indexes line up with `params`.
#[derive(Debug, Clone, PartialEq)]
pub struct Instantiation {
    /// The callee's type parameters, by their declared names.
    params: Vec<Tid>,
    /// Their declared kinds, in callee names.
    kinds: Vec<CKind>,
    /// Parameter `i` ↦ the caller type variable it stands for.
    solution: Vec<Option<Tid>>,
    /// Why parameter `i` is still unsolved, when resolution found a reason.
    unsolved: Vec<Option<Uninferable>>,
    /// Parameter `i` met an integer literal, so as a `Field` it may take the caller's unique
    /// field.
    met_literal: Vec<bool>,
}

impl Instantiation {
    /// Rewrites every callee parameter in `on` to its solution, in one pass.
    ///
    /// # Errors
    /// `on` mentions a parameter that is still unsolved.
    pub fn apply<T: TidSubst>(&self, on: &mut T) -> Result<(), SigError> {
        let missing = Cell::new(None);
        on.map_tids(&|t| {
            let i = self.index(t)?;
            let solved = self.solution[i].clone();
            if solved.is_none() && missing.get().is_none() {
                missing.set(Some(i));
            }
            solved
        });
        match missing.get() {
            None => Ok(()),
            Some(i) => Err(SigError::Uninferable {
                param: self.params[i].clone(),
                kind: self.kinds[i].clone(),
                reason: self.unsolved[i]
                    .clone()
                    .unwrap_or(Uninferable::Undetermined),
            }),
        }
    }

    /// Opens `sig` with every parameter unsolved.
    fn new(sig: &CSig) -> Self {
        let (params, kinds): (Vec<Tid>, Vec<CKind>) = sig
            .typevars
            .iter()
            .filter(|tv| !matches!(tv.kind, Kind::Range(_) | Kind::SizeVar))
            .map(|tv| (tv.id.node.clone(), tv.kind.clone()))
            .unzip();
        let n = params.len();
        Instantiation {
            params,
            kinds,
            solution: vec![None; n],
            unsolved: vec![None; n],
            met_literal: vec![false; n],
        }
    }

    /// Matches a parameter type (callee names) against an argument type (caller names),
    /// binding the parameters it meets. Three widenings are allowed: a polynomial where one with
    /// at least as many variables and as high a degree is expected, an integer where a wider
    /// integer range is expected, and an integer where a scalar is expected.
    ///
    /// # Errors
    /// The shapes differ, a kind class differs, or a parameter would stand for two different
    /// caller variables.
    fn match_typ(
        &mut self,
        param: &CTyp,
        arg: &CTyp,
        caller: &Ctx<Tid, CKind>,
    ) -> Result<(), UnifyError> {
        let mismatch = || UnifyError::typ_mismatch(param, arg);
        let within = |e| UnifyError::typ(param, arg, e);
        match (param, arg) {
            (CTyp::Base(p), CTyp::Base(a)) => self.bind(p, a, caller).map_err(within),
            (CTyp::Unit, CTyp::Unit) | (CTyp::Bool, CTyp::Bool) => Ok(()),
            // An integer fits an integer parameter whose range contains its range.
            (CTyp::Fin(p), CTyp::Fin(a)) => a.is_subset_of(p).then_some(()).ok_or_else(mismatch),
            // A polynomial fits a parameter with at least as many variables and as high a degree.
            (CTyp::Poly(p, pn, pd), CTyp::Poly(a, an, ad)) => {
                if pn.node < an.node || pd.node < ad.node {
                    return Err(mismatch());
                }
                self.bind(p, a, caller).map_err(within)
            }
            (CTyp::Vec(p, pn), CTyp::Vec(a, an)) => {
                if pn != an {
                    return Err(mismatch());
                }
                self.match_typ(&p.node, &a.node, caller).map_err(within)
            }
            (CTyp::Record(pf), CTyp::Record(af)) => {
                for (name, p) in pf.iter() {
                    let a = af.get(name).ok_or_else(mismatch)?;
                    self.match_typ(&p.node, &a.node, caller).map_err(within)?;
                }
                Ok(())
            }
            (CTyp::Base(p), CTyp::Fin(_) | CTyp::FieldLiteral) => {
                self.meet_literal(p).then_some(()).ok_or_else(mismatch)
            }
            _ => Err(mismatch()),
        }
    }

    /// Binds parameter `p` to caller variable `a` after checking that `a`'s kind [`fits`] `p`'s;
    /// the kinds' own parameters are checked by [`Self::resolve_dependent`].
    fn bind(&mut self, p: &Tid, a: &Tid, caller: &Ctx<Tid, CKind>) -> Result<(), UnifyError> {
        let i = self.index(p).ok_or_else(|| UnifyError::kind_not_found(p))?;
        let ka = caller.get(a).ok_or_else(|| UnifyError::kind_not_found(a))?;
        let kp = &self.kinds[i];
        if !fits(kp, ka) {
            return Err(UnifyError::kind_mismatch(p, kp, a, ka));
        }
        match &self.solution[i] {
            None => {
                self.solution[i] = Some(a.clone());
                Ok(())
            }
            Some(b) if b == a => Ok(()),
            // Caller variables are distinct types; one parameter cannot stand for two.
            Some(b) => Err(UnifyError::typ_mismatch(&CTyp::base(b), &CTyp::base(a))),
        }
    }

    /// Records that parameter `p` met an integer literal: fine for a scalar parameter, and a
    /// `Field` parameter may then take the caller's unique field. Returns whether `p` is scalar.
    fn meet_literal(&mut self, p: &Tid) -> bool {
        match self.index(p) {
            Some(i) if self.kinds[i].is_scalar() => {
                self.met_literal[i] = true;
                true
            }
            _ => false,
        }
    }

    /// Resolves the parameters the arguments left open from their kinds, then checks every
    /// solved parameter's kind under the solution.
    ///
    /// - `Scalar<S>`: a group has exactly one scalar field, so once `S` is solved the parameter
    ///   is the caller's scalar over groups containing it. Conversely a solved scalar over
    ///   groups `S'` determines a single unsolved group of `S` when one caller group is left.
    /// - `Pairing<A, B>`: a pair of groups has one target, so once `A` and `B` are solved the
    ///   parameter is the caller's pairing over them; a solved pairing determines `A` and `B`
    ///   in declaration order.
    /// - A `Field` parameter that met only integer literals takes the caller's unique field.
    ///
    /// A parameter left unsolved is reported by [`Self::apply`], with the reason kept here.
    ///
    /// # Errors
    /// A solved parameter whose kind its solution violates.
    fn resolve_dependent(&mut self, caller: &Ctx<Tid, CKind>) -> Result<(), SigError> {
        while self.improve(caller) {}
        for i in 0..self.params.len() {
            if self.solution[i].is_none() && self.unsolved[i].is_none() {
                self.unsolved[i] = Some(self.reason(i, caller));
            }
        }
        self.check_kinds(caller)
    }

    /// One round of resolution; returns whether it solved anything.
    fn improve(&mut self, caller: &Ctx<Tid, CKind>) -> bool {
        let mut progress = false;
        for i in 0..self.params.len() {
            match (&self.solution[i], self.kinds[i].clone()) {
                (None, Kind::Scalar(groups)) => {
                    if let Some(groups) = self.solved_all(groups.iter().map(|g| &g.node))
                        && let [c] = &scalars_over(caller, &groups)[..]
                    {
                        self.solution[i] = Some(c.clone());
                        progress = true;
                    }
                }
                (None, Kind::Pairing(a, b)) => {
                    if let Some(groups) = self.solved_all([&a.node, &b.node])
                        && let [c] = &pairings_over(caller, &groups)[..]
                    {
                        self.solution[i] = Some(c.clone());
                        progress = true;
                    }
                }
                (None, _) if self.met_literal[i] => {
                    if let Some(f) = CTyp::Fin(Range::singleton(0)).to_scalar(caller)
                        && caller.get(&f).is_some_and(|k| fits(&self.kinds[i], k))
                    {
                        self.solution[i] = Some(f);
                        progress = true;
                    }
                }
                (Some(c), Kind::Scalar(groups)) => {
                    let Some(Kind::Scalar(caller_groups)) = caller.get(c) else {
                        continue;
                    };
                    let open: Vec<&Tid> = groups
                        .iter()
                        .map(|g| &g.node)
                        .filter(|g| self.solution_of(g).is_none())
                        .collect();
                    let left: Vec<&Tid> = caller_groups
                        .iter()
                        .map(|g| &g.node)
                        .filter(|g| !groups.iter().any(|h| self.solution_of(&h.node) == Some(*g)))
                        .collect();
                    if let ([g], [h]) = (&open[..], &left[..]) {
                        let (g, h) = ((*g).clone(), (*h).clone());
                        progress |= self.set(&g, h);
                    }
                }
                (Some(c), Kind::Pairing(a, b)) => {
                    let Some(Kind::Pairing(ca, cb)) = caller.get(c) else {
                        continue;
                    };
                    let (ca, cb) = (ca.node.clone(), cb.node.clone());
                    match (
                        self.solution_of(&a.node).cloned(),
                        self.solution_of(&b.node).cloned(),
                    ) {
                        (None, None) => {
                            progress |= self.set(&a.node, ca);
                            progress |= self.set(&b.node, cb);
                        }
                        (Some(x), None) => {
                            let other = if x == ca { cb } else { ca };
                            progress |= self.set(&b.node, other);
                        }
                        (None, Some(y)) => {
                            let other = if y == cb { ca } else { cb };
                            progress |= self.set(&a.node, other);
                        }
                        (Some(_), Some(_)) => {}
                    }
                }
                _ => {}
            }
        }
        progress
    }

    /// Why unsolved parameter `i` could not be resolved.
    fn reason(&self, i: usize, caller: &Ctx<Tid, CKind>) -> Uninferable {
        let groups: Vec<&Tid> = match &self.kinds[i] {
            Kind::Scalar(groups) => groups.iter().map(|g| &g.node).collect(),
            Kind::Pairing(a, b) => vec![&a.node, &b.node],
            _ => return Uninferable::Undetermined,
        };
        if let Some(g) = groups.iter().find(|g| self.solution_of(g).is_none()) {
            return Uninferable::DependsOn((*g).clone());
        }
        let solved = self.solved_all(groups).expect("every group is solved");
        let (candidates, required) = match &self.kinds[i] {
            Kind::Scalar(_) => (
                scalars_over(caller, &solved),
                Kind::Scalar(solved.iter().map(|g| Spanned::dummy(g.clone())).collect()),
            ),
            Kind::Pairing(a, b) => {
                let at = |g: &Tid| Spanned::dummy(self.solution_of(g).cloned().expect("solved"));
                (
                    pairings_over(caller, &solved),
                    Kind::Pairing(at(&a.node), at(&b.node)),
                )
            }
            _ => unreachable!("only scalars and pairings reach here"),
        };
        if candidates.is_empty() {
            Uninferable::NoMatch(required)
        } else {
            Uninferable::Ambiguous(candidates)
        }
    }

    /// Checks each solved `Scalar`/`Pairing` parameter's kind under the solution.
    fn check_kinds(&self, caller: &Ctx<Tid, CKind>) -> Result<(), SigError> {
        for (i, solved) in self.solution.iter().enumerate() {
            let Some(c) = solved else { continue };
            let ok = match (&self.kinds[i], caller.get(c)) {
                (Kind::Scalar(groups), Some(Kind::Scalar(caller_groups))) => groups
                    .iter()
                    .filter_map(|g| self.solution_of(&g.node))
                    .all(|g| caller_groups.iter().any(|h| &h.node == g)),
                (Kind::Pairing(a, b), Some(Kind::Pairing(ca, cb))) => {
                    let sources = [&ca.node, &cb.node];
                    match (self.solution_of(&a.node), self.solution_of(&b.node)) {
                        (Some(x), Some(y)) => {
                            x != y && sources.contains(&x) && sources.contains(&y)
                        }
                        (Some(x), None) | (None, Some(x)) => sources.contains(&x),
                        (None, None) => true,
                    }
                }
                _ => true,
            };
            if !ok {
                return Err(SigError::KindUnsatisfied {
                    param: self.params[i].clone(),
                    kind: self.kinds[i].clone(),
                    bound_to: c.clone(),
                });
            }
        }
        Ok(())
    }

    fn index(&self, t: &Tid) -> Option<usize> {
        self.params.iter().position(|p| p == t)
    }

    fn solution_of(&self, t: &Tid) -> Option<&Tid> {
        self.index(t).and_then(|i| self.solution[i].as_ref())
    }

    /// The solutions of all of `groups`, or `None` if any is unsolved.
    fn solved_all<'a>(&self, groups: impl IntoIterator<Item = &'a Tid>) -> Option<Set<Tid>> {
        groups
            .into_iter()
            .map(|g| self.solution_of(g).cloned())
            .collect()
    }

    /// Solves parameter `p` to `c` if it is unsolved; returns whether it did.
    fn set(&mut self, p: &Tid, c: Tid) -> bool {
        match self.index(p) {
            Some(i) if self.solution[i].is_none() => {
                self.solution[i] = Some(c);
                true
            }
            _ => false,
        }
    }
}

/// The caller's scalar fields over groups containing all of `groups`.
fn scalars_over(caller: &Ctx<Tid, CKind>, groups: &Set<Tid>) -> Vec<Tid> {
    caller
        .iter()
        .filter(|(_, k)| match k {
            Kind::Scalar(over) => groups.iter().all(|g| over.iter().any(|h| &h.node == g)),
            _ => false,
        })
        .map(|(t, _)| t.clone())
        .collect()
}

/// The caller's pairing targets over exactly the two `groups`, in either order.
fn pairings_over(caller: &Ctx<Tid, CKind>, groups: &Set<Tid>) -> Vec<Tid> {
    caller
        .iter()
        .filter(|(_, k)| match k {
            Kind::Pairing(a, b) => {
                groups.len() == 2 && groups.contains(&a.node) && groups.contains(&b.node)
            }
            _ => false,
        })
        .map(|(t, _)| t.clone())
        .collect()
}

/// Whether a caller variable of kind `arg` can stand for a parameter of kind `param`: the same
/// class, or any scalar field for a `Field` parameter (every `Scalar<S>` is a field).
fn fits(param: &CKind, arg: &CKind) -> bool {
    matches!(
        (param, arg),
        (Kind::Field, Kind::Field | Kind::Scalar(_))
            | (Kind::Group, Kind::Group)
            | (Kind::Scalar(_), Kind::Scalar(_))
            | (Kind::Pairing(..), Kind::Pairing(..))
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_decls;
    use crate::typ::Typs;

    fn csig(decl: &str) -> CSig {
        let (mut decls, errors) = parse_decls(decl);
        assert!(errors.is_empty(), "parse errors: {errors:?}");
        let udecl = decls.pop().unwrap().node;
        udecl
            .concretize(&crate::typ::subst::SizeSubsts::new())
            .unwrap()
            .sig
    }

    fn args(ts: &[&str]) -> CTyps {
        Typs(
            ts.iter()
                .map(|t| Spanned::dummy(CTyp::base(&Tid::from(*t))))
                .collect(),
        )
    }

    fn ret(sig: &CSig) -> CTyp {
        sig.ret.as_ref().unwrap().node.clone()
    }

    /// `<G: Group, H: Group, GT: Pairing<G, H>, F: Scalar<G, H>>`.
    fn caller() -> Ctx<Tid, CKind> {
        let g = || Spanned::dummy(Tid::from("G"));
        let h = || Spanned::dummy(Tid::from("H"));
        Ctx::from([
            (Tid::from("G"), Kind::Group),
            (Tid::from("H"), Kind::Group),
            (Tid::from("GT"), Kind::Pairing(g(), h())),
            (Tid::from("F"), Kind::Scalar(Set::from_iter([g(), h()]))),
        ])
    }

    #[test]
    fn parameters_take_the_callers_types() {
        let sig = csig("fn f<G: Group>(instance x: G) -> G { x }");
        let (resolved, _) = sig.resolve(&args(&["H"]), &caller()).unwrap();
        assert_eq!(ret(&resolved), CTyp::base(&Tid::from("H")));
        assert_eq!(
            resolved.args.node.0[0].typ.node,
            CTyp::base(&Tid::from("H"))
        );
    }

    #[test]
    fn arity_is_checked() {
        let sig = csig("fn f<T: Field>(instance x: T) -> T { x }");
        assert_eq!(
            sig.resolve(&args(&[]), &caller()),
            Err(SigError::ArityMismatch(1, 0))
        );
        assert_eq!(
            sig.resolve(&args(&["F", "F"]), &caller()),
            Err(SigError::ArityMismatch(1, 2))
        );
    }

    #[test]
    fn kind_classes_must_agree() {
        let sig = csig("fn f<T: Group>(instance x: T) -> T { x }");
        assert!(matches!(
            sig.resolve(&args(&["F"]), &caller()),
            Err(SigError::Mismatch { index: 0, .. })
        ));
    }

    #[test]
    fn one_parameter_never_stands_for_two_types() {
        let sig = csig("fn f<T: Group>(instance x: T, instance y: T) -> T { x }");
        assert!(matches!(
            sig.resolve(&args(&["G", "H"]), &caller()),
            Err(SigError::Mismatch { index: 1, .. })
        ));
    }

    #[test]
    fn scalar_and_pairing_follow_their_groups() {
        let sig = csig("fn f<A: Group, S: Scalar<A>>(instance x: A) -> S { random<S> }");
        let (resolved, _) = sig.resolve(&args(&["G"]), &caller()).unwrap();
        assert_eq!(ret(&resolved), CTyp::base(&Tid::from("F")));

        let sig = csig(
            "fn f<A: Group, B: Group, T: Pairing<A, B>>(instance x: A, instance y: B) -> T { pair(x, y) }",
        );
        let (resolved, _) = sig.resolve(&args(&["G", "H"]), &caller()).unwrap();
        assert_eq!(ret(&resolved), CTyp::base(&Tid::from("GT")));
    }

    #[test]
    fn groups_follow_a_pairing() {
        let sig =
            csig("fn f<A: Group, B: Group, T: Pairing<A, B>>(instance t: T) -> B { random<B> }");
        let (resolved, _) = sig.resolve(&args(&["GT"]), &caller()).unwrap();
        assert_eq!(ret(&resolved), CTyp::base(&Tid::from("H")));
    }

    #[test]
    fn unsolved_parameters_are_reported_with_a_reason() {
        let sig = csig("fn f<A: Group, B: Group>(instance x: A) -> B { random<B> }");
        assert!(matches!(
            sig.resolve(&args(&["G"]), &caller()),
            Err(SigError::Uninferable {
                reason: Uninferable::Undetermined,
                ..
            })
        ));

        // `S` depends on `B`; the first unsolved parameter in declaration order is reported.
        let sig = csig("fn f<A: Group, B: Group, S: Scalar<B>>(instance x: A) -> S { random<S> }");
        assert_eq!(
            sig.resolve(&args(&["G"]), &caller())
                .unwrap_err()
                .to_string(),
            "type parameter `B` (Group) appears in no argument type"
        );
    }

    #[test]
    fn matching_keeps_the_coercions() {
        let sig = csig("fn f<T: Field>(instance x: T) -> T { x }");
        let caller = caller();
        let t = Tid::from("T");
        let f = Tid::from("F");
        let fin = |a, b| CTyp::fin(crate::ast::range::CRange::from_raw(a, 1, b));
        let ok = |p: &CTyp, a: &CTyp| Instantiation::new(&sig).match_typ(p, a, &caller);

        // A polynomial widens to more variables or a higher degree, never the other way.
        assert_eq!(ok(&CTyp::uni(&t, 11), &CTyp::uni(&f, 10)), Ok(()));
        assert!(ok(&CTyp::uni(&t, 10), &CTyp::uni(&f, 11)).is_err());
        assert_eq!(ok(&CTyp::mle(&t, 11), &CTyp::mle(&f, 10)), Ok(()));
        assert!(ok(&CTyp::mle(&t, 10), &CTyp::mle(&f, 11)).is_err());
        assert!(ok(&CTyp::mle(&t, 3), &CTyp::uni(&f, 2)).is_err());
        // No coercion between scalars and polynomials.
        assert!(ok(&CTyp::uni(&t, 3), &CTyp::base(&f)).is_err());
        assert!(ok(&CTyp::uni(&t, 3), &fin(0, 2)).is_err());
        assert!(ok(&CTyp::base(&t), &CTyp::uni(&f, 3)).is_err());
        // An integer literal where a scalar is expected, but no scalar where an integer is.
        assert_eq!(ok(&CTyp::base(&t), &fin(0, 2)), Ok(()));
        // An integer fits an integer parameter whose range contains its range.
        assert_eq!(ok(&fin(0, 10), &fin(1, 5)), Ok(()));
        assert!(ok(&fin(0, 2), &fin(1, 10)).is_err());
        assert!(ok(&fin(0, 2), &CTyp::base(&f)).is_err());
        // Vector lengths must agree.
        assert_eq!(
            ok(
                &CTyp::vec(&CTyp::base(&t), 2),
                &CTyp::vec(&CTyp::base(&f), 2)
            ),
            Ok(())
        );
        assert!(
            ok(
                &CTyp::vec(&CTyp::base(&t), 2),
                &CTyp::vec(&CTyp::base(&f), 3)
            )
            .is_err()
        );
        // A caller type variable outside the caller's kind context.
        assert_eq!(
            ok(&CTyp::base(&t), &CTyp::base(&Tid::from("X"))),
            Err(UnifyError::typ(
                &CTyp::base(&t),
                &CTyp::base(&Tid::from("X")),
                UnifyError::kind_not_found(&Tid::from("X"))
            ))
        );
    }

    fn uni_arg(t: &str, degree: usize) -> CTyps {
        Typs(vec![Spanned::dummy(CTyp::uni(&Tid::from(t), degree))])
    }

    #[test]
    fn a_call_resolves_to_the_most_specific_declaration() {
        let low = csig("fn f<T: Field>(instance x: Uni<T, 3>) -> T { x(0) }");
        let high = csig("fn f<T: Field>(instance x: Uni<T, 5>) -> T { x(0) }");
        let (chosen, _, _) =
            CSig::resolve_call([&high, &low], &uni_arg("F", 2), &caller()).unwrap();
        assert_eq!(chosen, &low);
        // Only the higher-degree declaration fits a degree-4 argument.
        let (chosen, _, _) =
            CSig::resolve_call([&high, &low], &uni_arg("F", 4), &caller()).unwrap();
        assert_eq!(chosen, &high);
    }

    #[test]
    fn an_integer_prefers_an_integer_parameter() {
        let int = csig("fn f<>(instance i: Fin<0..4>) -> Fin<0..4> { i }");
        let scalar = csig("fn f<T: Field>(instance x: T) -> T { x }");
        let literal = Typs(vec![Spanned::dummy(CTyp::fin(
            crate::ast::range::CRange::from_raw(0, 1, 2),
        ))]);
        let (chosen, _, _) = CSig::resolve_call([&scalar, &int], &literal, &caller()).unwrap();
        assert_eq!(chosen, &int);
    }

    #[test]
    fn a_call_with_no_most_specific_declaration_is_ambiguous() {
        let a = csig("fn f<T: Field>(instance x: Uni<T, 3>, instance y: Uni<T, 5>) -> T { x(0) }");
        let b = csig("fn f<T: Field>(instance x: Uni<T, 5>, instance y: Uni<T, 3>) -> T { x(0) }");
        let args = Typs(vec![
            Spanned::dummy(CTyp::uni(&Tid::from("F"), 2)),
            Spanned::dummy(CTyp::uni(&Tid::from("F"), 2)),
        ]);
        assert_eq!(
            CSig::resolve_call([&a, &b], &args, &caller()),
            Err(CallError::Ambiguous(vec![a.clone(), b.clone()]))
        );
        assert!(matches!(
            CSig::resolve_call([&a], &uni_arg("F", 2), &caller()),
            Err(CallError::NoMatch(failures)) if failures.len() == 1
        ));
    }

    #[test]
    fn declarations_differing_only_in_names_are_interchangeable() {
        let a = csig("fn f<A: Group>(instance x: A) -> A { x }");
        let b = csig("fn f<B: Group>(instance y: B) -> B { y }");
        let c = csig("fn f<B: Field>(instance y: B) -> B { y }");
        assert!(a.interchangeable_with(&b));
        assert!(!a.interchangeable_with(&c));
    }

    #[test]
    fn a_field_parameter_takes_any_scalar() {
        let sig = csig("fn f<T: Field>(instance x: T) -> T { x }");
        let (resolved, _) = sig.resolve(&args(&["F"]), &caller()).unwrap();
        assert_eq!(ret(&resolved), CTyp::base(&Tid::from("F")));
    }

    #[test]
    fn a_kind_its_solution_violates_is_reported() {
        let caller = Ctx::from([
            (Tid::from("G"), Kind::Group),
            (Tid::from("H"), Kind::Group),
            (
                Tid::from("F"),
                Kind::Scalar(Set::from_iter([Spanned::dummy(Tid::from("G"))])),
            ),
        ]);
        let sig = csig("fn f<A: Group, S: Scalar<A>>(instance x: A, instance s: S) -> S { s }");
        assert!(matches!(
            sig.resolve(&args(&["H", "F"]), &caller),
            Err(SigError::KindUnsatisfied { .. })
        ));
    }
}
