use crate::ast::decl::{DeclError, UDecl};
use crate::ast::spanned::Spanned;
use crate::ast::{Body, CSig, Sig};
use crate::diagnostic::Diagnostic;
use crate::id::Tid;
use crate::semantic::{
    check_dead_variables, check_duplicate_declarations, check_proto_requirement, check_purity,
    check_scope, check_size_binding, check_type_alias_cycles, check_typevars,
};

use std::fmt;
use thiserror::Error;

use crate::ast::Size;
use crate::typ::{TypeInline, UTyp};
use share::{BoxAllocator, Ctx, DocAllocator, DocBuilder, Pretty};

/// Polymorphic Module, a collection of declarations indexed by their typevars and signature
pub struct Module<N>(pub Ctx<Sig<N>, Body<N>>);

impl<N: Clone> Clone for Module<N>
where
    Sig<N>: Clone,
    Body<N>: Clone,
{
    fn clone(&self) -> Self {
        Module(self.0.clone())
    }
}

impl<N: Ord + Clone> PartialEq for Module<N>
where
    Sig<N>: Ord + PartialEq,
    Body<N>: PartialEq + Clone,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<N: Ord + Clone> Eq for Module<N>
where
    Sig<N>: Ord + Eq,
    Body<N>: Eq + Clone,
{
}

impl<N: Ord + Clone> PartialOrd for Module<N>
where
    Sig<N>: Ord + PartialOrd + Clone,
    Body<N>: PartialOrd + Clone,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<N: Ord + Clone> Ord for Module<N>
where
    Sig<N>: Ord + Clone,
    Body<N>: Ord + Clone,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<N: Ord + Clone> fmt::Debug for Module<N>
where
    Sig<N>: Ord + fmt::Debug,
    Body<N>: fmt::Debug + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Module").field(&self.0).finish()
    }
}

/// Failure while assembling or concretizing a module.
#[derive(Error, Debug)]
pub enum ModuleError {
    /// Two declarations concretized to the same signature, so a call could
    /// not be resolved to a unique body.
    #[error("Overlapping declarations: {0}")]
    OverlapDeclaration(CSig),
    /// A declaration failed its own checks (size substitution, range
    /// instantiation, concretization).
    #[error("Declaration error: {0}")]
    DeclarationError(#[from] DeclError),
    /// No declaration with the requested name exists in the module.
    #[error("Declaration not found: {0}")]
    DeclarationNotFound(String),
}

/// Polymorphic module with symbolic sizes
pub type UModule = Module<Size>;

/// Polymorphic module with concrete sizes
pub type CModule = Module<usize>;

impl<N: Ord> Module<N> {
    /// Number of declarations in the module.
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// Whether the module declares nothing.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// Iterate over `(signature, body)` pairs in declaration order.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&Sig<N>, &Body<N>)> {
        self.0.iter()
    }
    /// Names of all declarations, including each overload separately.
    pub fn get_names(&self) -> impl Iterator<Item = &str> {
        self.0.iter().map(|(sig, _)| sig.name.0.as_str())
    }
}

/// Polymorphic module with symbolic sizes
impl UModule {
    /// Parse source text into a polymorphic, untyped module with symbolic
    /// sizes, running all semantic checks (scope, typevar, size binding,
    /// duplicate declarations, proto requirement, type alias cycles).
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

        // Phase 2: Module-level semantic checks
        let file_span = 0..src.len();
        diags.extend(check_duplicate_declarations(&decls));
        diags.extend(check_proto_requirement(&decls, file_span));
        let alias_cycle_errors = check_type_alias_cycles(&decls);
        let has_alias_cycle = !alias_cycle_errors.is_empty();
        diags.extend(alias_cycle_errors);

        // Phase 3: Per-declaration semantic checks
        for decl in &decls {
            diags.extend(check_typevars(&decl.node.sig));
            diags.extend(check_size_binding(&decl.node.sig));
            diags.extend(check_scope(&decl.node));
            diags.extend(check_dead_variables(&decl.node));
            if let Body::Proto { relation, .. } = &decl.node.body {
                diags.extend(check_purity(relation));
            }
        }

        // Phase 4: Build module (type alias inlining)
        // Skip inlining if there are type alias cycle errors — inlining
        // cyclic aliases would cause infinite recursion.
        let module = if has_alias_cycle {
            // Build without type alias inlining to avoid infinite recursion.
            // The module will be incomplete but diagnostics have the error.
            Self::from_decls_no_inline(decls)
        } else {
            Self::from_decls(decls)
        };

        // Phase 5: Type checking (deferred — TypeError stays as-is)
        // TODO: Integrate type inference here, then enable:
        //   - check_relation_assertion (proto relation has assert, direct or transitive)
        //   - check_proto_verify (proto body has verify, direct or transitive)
        //   - check_dead_code (uncalled function)
        // All need a typed call graph (CSig::unify) for correct overload resolution.

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
            if d.node.body.is_type_alias() {
                if let Some(ret) = &d.node.sig.ret {
                    type_ctx.insert(&Tid::from(d.node.sig.name.node.0.as_str()), ret);
                }
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
    /// same concrete signature.
    pub fn concretize(&self, sizes: &Ctx<Tid, usize>) -> Result<CModule, ModuleError> {
        let mut ctx = Ctx::new();

        for decl in self.iter_decls() {
            let all_substs = decl.get_size_substitutions(sizes)?;
            for mut substs in all_substs.into_iter() {
                // Merge externally-provided SizeVar values (e.g. S: Size) into the
                // substitution context. Skip keys already set by range expansion
                // to avoid overriding pinned Range typevar values.
                for (k, v) in sizes.iter() {
                    if !substs.contains(k) {
                        substs.0.insert(k, v);
                    }
                }
                let cdecl = decl.concretize(&substs)?;
                ctx.insert_with(cdecl.sig, cdecl.body, &|sig, _, _| {
                    Err(ModuleError::OverlapDeclaration(sig.clone()))
                })?;
            }
        }
        // Return the concretized module
        Ok(Module(ctx))
    }
}

impl<N: Ord + Clone> IntoIterator for Module<N>
where
    Sig<N>: Ord + Clone,
    Body<N>: Clone,
{
    type Item = (Sig<N>, Body<N>);
    type IntoIter = share::CtxConsumingIter<(Sig<N>, Body<N>)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<N: Ord + Clone> FromIterator<(Sig<N>, Body<N>)> for Module<N>
where
    Sig<N>: Ord + Clone,
    Body<N>: Clone,
{
    fn from_iter<I: IntoIterator<Item = (Sig<N>, Body<N>)>>(iter: I) -> Self {
        Module(iter.into_iter().collect())
    }
}

/// Pretty printer instance
impl<'a, D, A, N> Pretty<'a, D, A> for Module<N>
where
    N: Pretty<'a, D, A> + Ord + Clone + 'a,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.intersperse(
            self.0.into_iter().map(|(sig, body)| {
                allocator.concat([
                    if body.is_proto() {
                        allocator.text("proto")
                    } else {
                        allocator.text("fn")
                    },
                    allocator.space(),
                    sig.pretty(allocator),
                    body.pretty(allocator),
                    allocator.hardline(),
                ])
            }),
            allocator.hardline(),
        )
    }

    fn is_nil(&self) -> bool {
        self.0.is_empty()
    }
}

/// Display instance calls the pretty printer
impl<'a, N> fmt::Display for Module<N>
where
    N: Clone + Ord + Pretty<'a, BoxAllocator, ()> + 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Module<N> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
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
    assert!(UModule::parse(ex)
        .0
        .unwrap()
        .concretize(&Ctx::new())
        .is_err());
}

#[test]
fn from_decl_underflow() {
    let ex = concat!(
        "fn sum<N: 0..3, F: Field>(instance a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}"
    );
    assert!(UModule::parse(ex)
        .0
        .unwrap()
        .concretize(&Ctx::new())
        .is_err());
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
fn test_module_round_trip() {
    let ex = concat!(
        "fn f<F: Field>(instance a: F) -> F {\n",
        "    a\n",
        "}\n",
        "fn g<F: Field>(instance a: F) -> F {\n",
        "    a\n",
        "}\n"
    );
    let umod1 = UModule::parse(ex).0.unwrap();
    let formatted = umod1.to_string();
    let umod2 = UModule::parse(&formatted).0.unwrap();
    assert_eq!(umod1, umod2);
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
