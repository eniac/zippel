//! Modules: building them from declarations, concretizing their sizes, and type-checking them.

use crate::ast::decl::{BodyTypes, DeclError, UDecl};
use crate::ast::exp::ExpLiteral;
use crate::ast::spanned::Spanned;
use crate::ast::{Body, CBody, CSig, Sig};
use crate::diagnostic::Diagnostic;
use crate::id::Tid;

use num::BigUint;
use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::ast::Size;
use crate::typ::{Kind, SizeSubsts, TypeError, TypeInline, UTyp};
use share::{Ctx, Set};

mod error;

pub use error::{ExpandedRange, ModuleError};

/// Identity within one source module, independent of diagnostic locations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct DeclId(pub(super) usize);

pub(super) struct ExpandedModule {
    pub(super) module: CModule,
    pub(super) origins: std::collections::BTreeMap<CSig, DeclId>,
}

pub(super) enum ExpansionFailure {
    Substitutions(ModuleError),
    Concretization(ModuleError),
    Limit { expanded: usize },
}

/// Polymorphic Module, a collection of declarations indexed by their typevars and signature
pub struct Module<N: ExpLiteral>(pub Ctx<Sig<N::Size>, Body<N>>);

impl<N: ExpLiteral> Clone for Module<N> {
    fn clone(&self) -> Self {
        Module(self.0.clone())
    }
}

impl<N: ExpLiteral + PartialEq> PartialEq for Module<N> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<N: ExpLiteral + Eq> Eq for Module<N> {}

impl<N: ExpLiteral + Ord> PartialOrd for Module<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<N: ExpLiteral + Ord> Ord for Module<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<N: ExpLiteral + fmt::Debug> fmt::Debug for Module<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Module").field(&self.0).finish()
    }
}

/// Polymorphic module with symbolic sizes
pub type UModule = Module<Size>;

/// Module with concrete signatures and full-magnitude body literals
pub type CModule = Module<BigUint>;

impl<N: ExpLiteral> Module<N> {
    /// Number of declarations in the module.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Whether the module declares nothing.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Iterate over `(signature, body)` pairs in declaration order.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&Sig<N::Size>, &Body<N>)> {
        self.0.iter()
    }
    /// Names of all declarations, including each overload separately.
    pub fn get_names(&self) -> impl Iterator<Item = &str> {
        self.0.iter().map(|(sig, _)| sig.name.0.as_str())
    }
}

/// Module with concrete sizes
impl CModule {
    /// Type-check every declaration, returning one diagnostic per failing declaration, sorted
    /// by source position.
    ///
    /// Range-kinded type variables expand one declaration into several instances that share
    /// source spans, so an error common to several instances is reported once, naming the
    /// first failing instance.
    ///
    /// # Errors
    /// The diagnostics, if any declaration fails to type-check.
    pub fn typecheck(self) -> Result<TypedModule, Vec<Diagnostic>> {
        let (diagnostics, types) = self.check();
        if diagnostics.is_empty() {
            Ok(TypedModule {
                module: self,
                types,
            })
        } else {
            Err(diagnostics)
        }
    }

    /// The diagnostics of every declaration that fails to type-check, and the types of every
    /// one that checks.
    fn check(&self) -> (Vec<Diagnostic>, ModuleTypes) {
        let fctx: Set<CSig> = self.iter().map(|(sig, _)| sig.clone()).collect();
        let mut instances: HashMap<&str, usize> = HashMap::new();
        for (sig, _) in self.iter() {
            *instances.entry(sig.name.node.0.as_str()).or_default() += 1;
        }
        // Instances share source spans, so an error common to several is reported once, naming
        // the instance when the declaration has several.
        let mut seen = HashSet::new();
        let mut diags = Vec::new();
        let mut report = |sig: &CSig, mut d: Diagnostic| {
            if seen.insert((d.span.clone(), d.summary.clone())) {
                if instances[sig.name.node.0.as_str()] > 1 {
                    d = d.note(&format!("in the instance `{}`", one_line(&sig.to_string())));
                }
                diags.push(d);
            }
        };
        let mut types = ModuleTypes::new();
        let mut failed = false;
        for (sig, body) in self.iter() {
            match body.typecheck(sig.clone(), &fctx) {
                Ok(body_types) => {
                    types.insert(sig.clone(), body_types);
                }
                Err(e) => {
                    failed = true;
                    // Fall back to the declaration's name when inference located nothing.
                    report(sig, Diagnostic::from(TypeError::located(&sig.name.span, e)));
                }
            }
        }
        // Checks that follow calls need every call resolved, so they run once every
        // declaration type-checks.
        if !failed {
            let typed = self.iter().map(|(sig, body)| (sig, body, &types[sig]));
            for (sig, d) in crate::semantic::check_instances(typed) {
                report(sig, d);
            }
        }
        diags.sort_by_key(|d| d.span.start);
        (diags, types)
    }
}

/// The types of the nodes of a module's declarations, by signature.
type ModuleTypes = std::collections::BTreeMap<CSig, BodyTypes>;

/// A module whose declarations all type-check, with the types of their nodes: what lowering
/// takes.
#[derive(Debug, Clone)]
pub struct TypedModule {
    module: CModule,
    types: ModuleTypes,
}

impl TypedModule {
    /// The module.
    pub const fn module(&self) -> &CModule {
        &self.module
    }

    /// Each declaration, with the types of its nodes and the declarations its calls resolve to.
    pub fn iter(&self) -> impl Iterator<Item = (&CSig, &CBody, &BodyTypes)> {
        self.module
            .iter()
            .map(|(sig, body)| (sig, body, &self.types[sig]))
    }
}

/// Polymorphic module with symbolic sizes
impl UModule {
    /// Type variables whose values a caller may supply to [`Self::concretize`]: the `Size`
    /// parameters. A range-kinded variable takes every value of its range instead.
    pub fn size_params(&self) -> Set<Tid> {
        self.iter()
            .flat_map(|(sig, _)| sig.typevars.0.iter())
            .filter(|tv| matches!(tv.kind, Kind::SizeVar))
            .map(|tv| tv.id.node.clone())
            .collect()
    }

    /// The range-kinded type variables, which [`Self::concretize`] expands over their
    /// whole range; a caller cannot supply their values.
    pub fn range_params(&self) -> Set<Tid> {
        self.iter()
            .flat_map(|(sig, _)| sig.typevars.0.iter())
            .filter(|tv| matches!(tv.kind, Kind::Range(_)))
            .map(|tv| tv.id.node.clone())
            .collect()
    }

    /// Parse source text into a polymorphic, untyped module with symbolic
    /// sizes, running the semantic checks that need no type information
    /// ([`crate::semantic::check_decls`]).
    ///
    /// Returns `(Some(module), diagnostics)` if parsing produced any
    /// declarations, `(None, diagnostics)` if parsing failed completely.
    /// Diagnostics are sorted by (span.start, severity, phase) for
    /// deterministic output.
    ///
    /// Type aliases (`type X = T;`) are expanded inline before returning.
    pub fn parse(src: &str) -> (Option<Self>, Vec<Diagnostic>) {
        let mut diags = Vec::new();

        // Phase 1: Parse (with recovery)
        let (decls, parse_errors) = crate::parser::parse_decls(src);
        diags.extend(parse_errors);

        // Skip semantic checks only if we got NO declarations
        if decls.is_empty() && !diags.is_empty() {
            return (None, diags);
        }

        // Phase 2: Semantic checks
        let checks = crate::semantic::check_decls(&decls, 0..src.len());
        diags.extend(checks.diagnostics);

        // Phase 3: Build module (type alias inlining)
        // Skip inlining if there are type alias cycle errors — inlining
        // cyclic aliases would cause infinite recursion.
        let module = if checks.alias_cycle {
            // Build without type alias inlining to avoid infinite recursion.
            // The module will be incomplete but diagnostics have the error.
            Self::from_decls_no_inline(decls)
        } else {
            Self::from_decls(decls)
        };

        // Deterministic ordering: span.start → severity → phase
        diags.sort_by(|a, b| {
            a.span
                .start
                .cmp(&b.span.start)
                .then_with(|| a.severity.cmp(&b.severity))
                .then_with(|| a.phase.cmp(&b.phase))
        });

        (Some(module), diags)
    }

    /// Build a module from pre-parsed declarations (with spans).
    /// Type aliases are expanded inline. Does NOT run semantic checks —
    /// those are handled by `parse()`.
    pub fn from_decls(decls: Vec<Spanned<UDecl>>) -> Self {
        // Collect type aliases from type_decl declarations
        let mut type_ctx: Ctx<Tid, UTyp> = Ctx::new();
        for d in decls.iter() {
            if d.node.body.is_type_alias()
                && let Some(ret) = &d.node.sig.ret
            {
                type_ctx.insert(&Tid::from(d.node.sig.name.node.0.as_str()), ret);
            }
        }

        let mut m = Ctx::new();
        for d in decls.into_iter() {
            if d.node.body.is_type_alias() {
                continue;
            }
            let d = if type_ctx.is_empty() {
                d.node
            } else {
                d.node.type_inline(&type_ctx)
            };
            m.insert(&d.sig, &d.body);
        }
        Module(m)
    }

    /// Build a module without type alias inlining.
    /// Used when type alias cycles are detected to avoid infinite recursion.
    fn from_decls_no_inline(decls: Vec<Spanned<UDecl>>) -> Self {
        let mut m = Ctx::new();
        for d in decls.into_iter() {
            if d.node.body.is_type_alias() {
                continue;
            }
            m.insert(&d.node.sig, &d.node.body);
        }
        Module(m)
    }

    /// Rebuild owned `UDecl` values from the stored signature/body pairs,
    /// for passes that want whole declarations rather than the split map.
    pub fn iter_decls(&self) -> impl Iterator<Item = UDecl> + '_ {
        self.0.iter().map(|(sig, body)| UDecl {
            sig: sig.clone(),
            body: body.clone(),
        })
    }

    /// Concretize sizes in all declarations to generate a CModule
    ///
    /// Each declaration is expanded once per assignment of its range-kinded
    /// type variables, with `sizes` supplying values for the remaining
    /// `Size` variables.
    ///
    /// # Errors
    /// Returns `ModuleError::DeclarationError` if a declaration's sizes
    /// cannot be resolved or concretized, and
    /// `ModuleError::OverlapDeclaration` if two expansions collapse onto the
    /// same concrete signature, and `ModuleError::InterchangeableDeclarations` if two
    /// declarations of the same name accept exactly the same arguments.
    pub fn concretize(&self, sizes: &Ctx<Tid, usize>) -> Result<CModule, ModuleError> {
        self.expand(sizes, false, None)
            .map(|expanded| expanded.module)
            .map_err(|error| match error {
                ExpansionFailure::Substitutions(error)
                | ExpansionFailure::Concretization(error) => error,
                ExpansionFailure::Limit { .. } => {
                    unreachable!("ordinary concretization has no instance limit")
                }
            })
    }

    pub(super) fn expand(
        &self,
        sizes: &Ctx<Tid, usize>,
        require_nonempty: bool,
        max_instances: Option<usize>,
    ) -> Result<ExpandedModule, ExpansionFailure> {
        // Only `Size` variables take values from `sizes`; a name that is a range everywhere
        // it is declared would otherwise be silently ignored.
        let params = self.size_params();
        for (name, _) in sizes.iter().filter(|(name, _)| !params.contains(name)) {
            if let Some((var, Kind::Range(range))) = self
                .iter()
                .flat_map(|(sig, _)| sig.typevars.0.iter())
                .map(|tv| (&tv.id, &tv.kind))
                .find(|(id, kind)| id.node == *name && matches!(kind, Kind::Range(_)))
            {
                return Err(ExpansionFailure::Concretization(
                    ModuleError::SizeForRange {
                        var: var.clone(),
                        range: range.to_string(),
                    },
                ));
            }
        }

        let mut ctx = Ctx::new();
        let mut origins = std::collections::BTreeMap::new();
        for (source, decl) in self.iter_decls().enumerate() {
            for substs in
                SizeSubsts::iter_typevars(&decl.sig.typevars.node, sizes, require_nonempty)
            {
                let mut substs = substs.map_err(|error| {
                    ExpansionFailure::Substitutions(ModuleError::DeclarationError(
                        decl.sig.name.span.clone(),
                        DeclError::SubstError(error),
                    ))
                })?;
                if max_instances.is_some_and(|limit| ctx.len() == limit) {
                    return Err(ExpansionFailure::Limit {
                        expanded: ctx.len(),
                    });
                }
                // Range bindings shadow supplied Size values from other declarations.
                for (name, value) in sizes.iter() {
                    if !substs.contains(name) {
                        substs.0.insert(name, value);
                    }
                }
                let concrete = decl.concretize(&substs).map_err(|error| {
                    ExpansionFailure::Concretization(ModuleError::DeclarationError(
                        decl.sig.name.span.clone(),
                        error,
                    ))
                })?;
                origins.insert(concrete.sig.clone(), DeclId(source));
                ctx.insert_with(concrete.sig, concrete.body, &|sig, _, _| {
                    Err(ModuleError::OverlapDeclaration(sig.clone()))
                })
                .map_err(ExpansionFailure::Concretization)?;
            }
        }
        let sigs: Vec<&CSig> = ctx.iter().map(|(sig, _)| sig).collect();
        for (i, a) in sigs.iter().enumerate() {
            if let Some(b) = sigs[i + 1..].iter().find(|b| a.interchangeable_with(b)) {
                let (first, second) = if a.name.span.start <= b.name.span.start {
                    (a, b)
                } else {
                    (b, a)
                };
                return Err(ExpansionFailure::Concretization(
                    ModuleError::InterchangeableDeclarations((*first).clone(), (**second).clone()),
                ));
            }
        }
        Ok(ExpandedModule {
            module: Module(ctx),
            origins,
        })
    }
}

impl<N: ExpLiteral> IntoIterator for Module<N> {
    type Item = (Sig<N::Size>, Body<N>);
    type IntoIter = std::collections::btree_map::IntoIter<Sig<N::Size>, Body<N>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N: ExpLiteral> FromIterator<(Sig<N::Size>, Body<N>)> for Module<N> {
    fn from_iter<I: IntoIterator<Item = (Sig<N::Size>, Body<N>)>>(iter: I) -> Self {
        Module(iter.into_iter().collect())
    }
}

fn one_line(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn from_decl_subst1() {
    let ex = concat!(
        "fn sum<N: 1..4, F: Field>(instance a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(instance a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}"
    );
    let umod = UModule::parse(ex).0.unwrap();
    assert_eq!(umod.len(), 2);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 4);
}

#[test]
fn from_decl_duplicate() {
    let ex = concat!(
        "fn sum<N: 1..2, F: Field>(instance a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(instance a: [F; 1]) -> F {\n",
        "   a[0]\n",
        "}"
    );
    assert!(
        UModule::parse(ex)
            .0
            .unwrap()
            .concretize(&Ctx::new())
            .is_err()
    );
}

#[test]
fn from_decl_underflow() {
    let ex = concat!(
        "fn sum<N: 0..3, F: Field>(instance a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}"
    );
    assert!(
        UModule::parse(ex)
            .0
            .unwrap()
            .concretize(&Ctx::new())
            .is_err()
    );
}

#[test]
fn from_decl_subst2() {
    let ex = concat!(
        "fn sum<N: 1..4, F: Field>(instance a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(instance a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}\n",
        "fn prod_sum<N: 0..4, M: 0..3, F: Field>(instance a: [F; N], instance b: [F; M]) -> F {\n",
        "   sum(a) * sum(b)\n",
        "}\n"
    );
    let umod = UModule::parse(ex).0.unwrap();
    assert_eq!(umod.len(), 3);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 16);
}

#[test]
fn type_alias_record() {
    let ex = concat!(
        "type Point = { x: F, y: F };\n",
        "fn origin<F: Field>(instance zero: F) -> Point {\n",
        "    {| x: zero, y: zero |}\n",
        "}\n"
    );
    let umod = UModule::parse(ex).0.unwrap();
    // type alias is inlined, only the fn remains
    assert_eq!(umod.len(), 1);
    // The return type should be expanded to the record type
    let (sig, _) = umod.iter().next().unwrap();
    assert!(
        sig.ret
            .as_ref()
            .is_some_and(|r| matches!(&r.node, crate::typ::Typ::Record(_))),
        "Return type should be a Record, got {:?}",
        sig.ret
    );
}

#[test]
fn type_alias_in_args() {
    let ex = concat!(
        "type Vec3 = [F; 3];\n",
        "fn dotprod<F: Field>(instance a: Vec3, instance b: Vec3) -> F {\n",
        "    reduce(+, a * b)\n",
        "}\n"
    );
    let umod = UModule::parse(ex).0.unwrap();
    assert_eq!(umod.len(), 1);
    let (sig, _) = umod.iter().next().unwrap();
    // First arg should be Vec(Base(F), 3), not Base(Vec3)
    assert!(
        matches!(&*sig.args.0[0].typ, crate::typ::Typ::Vec(_, _)),
        "Arg type should be Vec, got {:?}",
        sig.args.0[0].typ
    );
}

#[test]
fn typed_let_binding() {
    let ex = concat!(
        "fn f<F: Field>(instance a: F, instance b: F) -> F {\n",
        "    let c: F = a + b;\n",
        "    c\n",
        "}\n"
    );
    let umod = UModule::parse(ex).0.unwrap();
    assert_eq!(umod.len(), 1);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 1);
}

#[test]
fn test_concretize_size_var() {
    let ex = "fn foo<S: Size, F: Field>(instance a: [F; S]) -> F { a[0] }";
    let umod = UModule::parse(ex).0.unwrap();
    assert_eq!(umod.len(), 1);

    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("S"), &5);

    let cmod = umod.concretize(&sizes).unwrap();
    assert_eq!(cmod.len(), 1);

    let (sig, _) = cmod.iter().next().unwrap();
    let arg_typ = &sig.args.0[0].typ;
    assert_eq!(
        arg_typ.clone(),
        Spanned::dummy(crate::typ::Typ::vec(
            &crate::typ::Typ::base(&Tid::from("F")),
            5
        ))
    );
}

#[test]
fn test_module_overlap_error_message() {
    let ex = concat!(
        "fn sum<N: 1..2, F: Field>(instance a: [F; N]) -> F {\n",
        "    a[0]\n",
        "}\n",
        "fn sum<F: Field>(instance a: [F; 1]) -> F {\n",
        "    a[0]\n",
        "}\n"
    );
    let umod = UModule::parse(ex).0.unwrap();
    let res = umod.concretize(&Ctx::new());
    assert!(res.is_err());
    let err_msg = res.unwrap_err().to_string();
    assert!(err_msg.contains("Overlapping declarations"));
    assert!(err_msg.contains("sum"));
}

/// Issue #173: overload resolution fails when a Size type variable is
/// passed to a function overloaded on a Range type variable.
/// `eq_weights` has two overloads: `[F; 1]` and `[F; N]` where `N: 2..20`.
/// The protocol passes `placeholder_tau: [F; M]` where `M: Size`.
/// After concretization (M pinned to e.g. 4), the call should resolve
/// to the recursive overload with N=4.
#[test]
fn test_issue_173_overload_resolution_with_size_var() {
    let ex = concat!(
        "fn eq_weights<F: Field>(instance x: [F; 1]) -> [F; 2] {\n",
        "    [(1 - x[0]), x[0]]\n",
        "}\n",
        "fn eq_weights<F: Field, N: 2..20>(instance x: [F; N]) -> [F; 2^N] {\n",
        "    let x_lo = x[0..(N-1)];\n",
        "    let a    = x[N-1];\n",
        "    let prev = eq_weights(x_lo);\n",
        "    (prev * (1 - a)) ++ (prev * a)\n",
        "}\n",
        "proto spartan<F: Field, M: Size>(\n",
        "    instance placeholder_tau: [F; M]\n",
        ") where placeholder_tau[0] == placeholder_tau[0] {\n",
        "    let tau = eq_weights(placeholder_tau);\n",
        "    verify(placeholder_tau[0] == placeholder_tau[0])\n",
        "}\n"
    );
    let umod = UModule::parse(ex).0.unwrap();

    // Without size pinning, M stays abstract — concretize cannot resolve
    // the overload since it doesn't know if M=1 (base case) or M∈2..20.
    let no_size = umod.concretize(&Ctx::new());
    assert!(no_size.is_err(), "expected error without size pinning");

    // Pin M=4 (a power of 2, within N's range 2..20)
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("M"), &4);

    let result = umod.concretize(&sizes);
    match result {
        Ok(cmod) => {
            // Should produce concrete declarations for the protocol and
            // all recursive eq_weights instantiations (N=4, N=3, N=2, N=1)
            assert!(
                cmod.len() >= 3,
                "expected at least 3 decls, got {}",
                cmod.len()
            );
        }
        Err(e) => {
            panic!("concretize failed (issue #173 not fixed): {}", e);
        }
    }
}
