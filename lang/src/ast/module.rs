use crate::ast::decl::{DeclError, UDecl, UDecls};
use crate::ast::{Body, CSig, Sig};
use crate::id::Tid;

use bumpalo::Bump;
use from_pest::{ConversionError, FromPest};
use pest::Parser;
use std::fmt;
use thiserror::Error;

use crate::parser::*;
use crate::typ::{Size, TypeInline, UTyp};
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

#[derive(Error, PartialEq, Debug)]
pub enum ModuleError {
    #[error("Overlapping declarations: {0}")]
    OverlapDeclaration(CSig),
    #[error("Declaration error: {0}")]
    DeclarationError(#[from] DeclError),
    #[error("Declaration not found: {0}")]
    DeclarationNotFound(String),
}

/// Polymorphic module with symbolic sizes
pub type UModule = Module<Size>;

/// Polymorphic module with concrete sizes
pub type CModule = Module<usize>;

impl<N: Ord> Module<N> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&Sig<N>, &Body<N>)> {
        self.0.iter()
    }
    pub fn get_names(&self) -> impl Iterator<Item = &str> {
        self.0.iter().map(|(sig, _)| sig.name.0.as_str())
    }
}

/// Polymorphic module with symbolic sizes
impl UModule {
    /// Entry point to the zippel compiler.
    /// Parse a Zippel declarations list into a polymorphic,
    /// untyped module, with symbolic sizes.
    /// Type aliases (`type X = T;`) are expanded inline before returning.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str<'a>(input_str: &'a str) -> Result<Self, ConversionError<InputError<'a>>> {
        let mut pairs = ZippelParser::parse(Rule::decls, input_str).unwrap();
        let decls = UDecls::from_pest(&mut pairs)?;

        // Collect type aliases from type_decl declarations
        let mut type_ctx: Ctx<Tid, UTyp> = Ctx::new();
        for d in decls.0.iter() {
            if d.body.is_type_alias() {
                // Store the alias: name (as Tid) → aliased type (in sig.ret)
                type_ctx.insert(&Tid::from(d.sig.name.0.as_str()), &d.sig.ret);
            }
        }

        // Validate type aliases do not have cycles
        detect_alias_cycles(&type_ctx).map_err(ConversionError::Malformed)?;

        let mut m = Ctx::new();
        for d in decls.into_iter() {
            if d.body.is_type_alias() {
                // Already stored and validated, type aliases do not go to Module execution decls
                continue;
            } else {
                // Inline type aliases in the declaration
                let d = if type_ctx.is_empty() {
                    d
                } else {
                    d.type_inline(&type_ctx)
                };
                m.insert_with(d.sig, d.body, &|sig, _, _| {
                    Err(ConversionError::Malformed(InputError::DuplicateDecl(
                        sig.clone(),
                    )))
                })?;
            }
        }
        Ok(Module(m))
    }

    /// Parse a file into a Zippel declarations list
    pub fn from_file<'a>(
        file: &str,
        allocator: &'a Bump,
    ) -> Result<Self, ConversionError<InputError<'a>>> {
        let input_str = std::fs::read_to_string(file).unwrap();
        let stored_str = allocator.alloc_str(&input_str);
        Self::from_str(stored_str)
    }

    pub fn iter_decls(&self) -> impl Iterator<Item = UDecl> + '_ {
        self.0.iter().map(|(sig, body)| UDecl {
            sig: sig.clone(),
            body: body.clone(),
        })
    }

    /// Concretize sizes in all declarations to generate a CModule
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

// Helper to extract type alias dependencies from UTyp
fn type_dependencies(typ: &UTyp) -> share::Set<Tid> {
    use crate::typ::Typ;
    let mut deps = share::Set::new();
    fn recurse(typ: &UTyp, deps: &mut share::Set<Tid>) {
        match typ {
            Typ::Base(t) => {
                deps.insert(t.clone());
            }
            Typ::Poly(t, _, _) => {
                deps.insert(t.clone());
            }
            Typ::Vec(box_typ, _) => {
                recurse(box_typ, deps);
            }
            Typ::Record(ctx) => {
                for (_, t) in ctx.iter() {
                    recurse(t, deps);
                }
            }
            Typ::Fin(_) | Typ::Unit => {}
        }
    }
    recurse(typ, &mut deps);
    deps
}

// DFS cycle checker
fn check_cycle<'pest>(
    node: &Tid,
    type_ctx: &Ctx<Tid, UTyp>,
    visiting: &mut share::Set<Tid>,
    visited: &mut share::Set<Tid>,
) -> Result<(), InputError<'pest>> {
    if visiting.contains(node) {
        return Err(InputError::CyclicTypeAlias(node.clone()));
    }
    if visited.contains(node) {
        return Ok(());
    }
    visiting.insert(node.clone());
    if let Some(typ) = type_ctx.get(node) {
        for dep in type_dependencies(typ).into_iter() {
            if type_ctx.contains(&dep) {
                check_cycle(&dep, type_ctx, visiting, visited)?;
            }
        }
    }
    visiting.retain(|k| k != node);
    visited.insert(node.clone());
    Ok(())
}

fn detect_alias_cycles<'pest>(type_ctx: &Ctx<Tid, UTyp>) -> Result<(), InputError<'pest>> {
    let mut visiting = share::Set::new();
    let mut visited = share::Set::new();

    for name in type_ctx.keys() {
        if !visited.contains(&name) {
            check_cycle(&name, type_ctx, &mut visiting, &mut visited)?;
        }
    }
    Ok(())
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
        "fn sum<N: 1..4, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}"
    );
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 2);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 4);
}

#[test]
fn from_decl_duplicate() {
    let ex = concat!(
        "fn sum<N: 1..2, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 1]) -> F {\n",
        "   a[0]\n",
        "}"
    );
    assert!(UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .is_err());
}

#[test]
fn from_decl_underflow() {
    let ex = concat!(
        "fn sum<N: 0..3, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}"
    );
    assert!(UModule::from_str(ex)
        .unwrap()
        .concretize(&Ctx::new())
        .is_err());
}

#[test]
fn from_decl_subst2() {
    let ex = concat!(
        "fn sum<N: 1..4, F: Field>(public a: [F; N]) -> F {\n",
        "    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 0]) -> F {\n",
        "   a[0]\n",
        "}\n",
        "fn prod_sum<N: 0..4, M: 0..3, F: Field>(public a: [F; N], public b: [F; M]) -> F {\n",
        "   sum(a) * sum(b)\n",
        "}\n"
    );
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 3);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 16);
}

#[test]
fn type_alias_record() {
    let ex = concat!(
        "type Point = { x: F, y: F };\n",
        "fn origin<F: Field>(public zero: F) -> Point {\n",
        "    {| x: zero, y: zero |}\n",
        "}\n"
    );
    let umod = UModule::from_str(ex).unwrap();
    // type alias is inlined, only the fn remains
    assert_eq!(umod.len(), 1);
    // The return type should be expanded to the record type
    let (sig, _) = umod.iter().next().unwrap();
    assert!(
        matches!(&sig.ret, crate::typ::Typ::Record(_)),
        "Return type should be a Record, got {:?}",
        sig.ret
    );
}

#[test]
fn type_alias_in_args() {
    let ex = concat!(
        "type Vec3 = [F; 3];\n",
        "fn dot<F: Field>(public a: Vec3, public b: Vec3) -> F {\n",
        "    reduce(+, a * b)\n",
        "}\n"
    );
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 1);
    let (sig, _) = umod.iter().next().unwrap();
    // First arg should be Vec(Base(F), 3), not Base(Vec3)
    assert!(
        matches!(&sig.args.0[0].typ, crate::typ::Typ::Vec(_, _)),
        "Arg type should be Vec, got {:?}",
        sig.args.0[0].typ
    );
}

#[test]
fn typed_let_binding() {
    let ex = concat!(
        "fn f<F: Field>(public a: F, public b: F) -> F {\n",
        "    let c: F = a + b;\n",
        "    c\n",
        "}\n"
    );
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 1);
    let cmod = umod.concretize(&Ctx::new()).unwrap();
    assert_eq!(cmod.len(), 1);
}

#[test]
fn test_concretize_size_var() {
    let ex = "fn foo<S: Size, F: Field>(public a: [F; S]) -> F { a[0] }";
    let umod = UModule::from_str(ex).unwrap();
    assert_eq!(umod.len(), 1);

    let mut sizes = Ctx::new();
    sizes.insert(&Tid::from("S"), &5);

    let cmod = umod.concretize(&sizes).unwrap();
    assert_eq!(cmod.len(), 1);

    let (sig, _) = cmod.iter().next().unwrap();
    let arg_typ = &sig.args.0[0].typ;
    assert_eq!(
        arg_typ.clone(),
        crate::typ::Typ::Vec(Box::new(crate::typ::Typ::base(&Tid::from("F"))), 5)
    );
}

#[test]
fn test_module_round_trip() {
    let ex = concat!(
        "fn f<F: Field>(public a: F) -> F {\n",
        "    a\n",
        "}\n",
        "fn g<F: Field>(public a: F) -> F {\n",
        "    a\n",
        "}\n"
    );
    let umod1 = UModule::from_str(ex).unwrap();
    let formatted = umod1.to_string();
    let umod2 = UModule::from_str(&formatted).unwrap();
    assert_eq!(umod1, umod2);
}

#[test]
fn test_module_overlap_error_message() {
    let ex = concat!(
        "fn sum<N: 1..2, F: Field>(public a: [F; N]) -> F {\n",
        "    a[0]\n",
        "}\n",
        "fn sum<F: Field>(public a: [F; 1]) -> F {\n",
        "    a[0]\n",
        "}\n"
    );
    let umod = UModule::from_str(ex).unwrap();
    let res = umod.concretize(&Ctx::new());
    assert!(res.is_err());
    let err_msg = res.unwrap_err().to_string();
    assert!(err_msg.contains("Overlapping declarations"));
    assert!(err_msg.contains("sum"));
}
