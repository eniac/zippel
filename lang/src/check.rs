//! Front-end check of `.zippel` source: parsing, semantic checks, size concretization, and type
//! inference, without lowering to the Graph IR or needing protocol inputs.
//!
//! Type inference runs on concretized declarations, so every `Size` parameter needs a value.
//! Callers pass the ones they care about; the rest default to the smallest value that keeps every
//! dependent range non-empty (see [`find_minimal_sizes`]). A program can be well-typed at one size
//! and ill-typed at another, so a clean report only covers the sizes in [`CheckReport::sizes`].

use std::collections::{HashMap, HashSet};

use crate::ast::decl::DeclError;
use crate::ast::module::ModuleError;
use crate::ast::range::Range;
use crate::ast::{Body, CBody, CExp, CModule, CSig, Exp, Size, Spanned, UModule};
use crate::diagnostic::{Diagnostic, Phase, Severity};
use crate::id::{Tid, Vid};
use crate::typ::{Kind, TypeError};
use share::traversal::ToTraversal1;
use share::{Ctx, Set};

/// One reported problem, with the full typing judgement behind it when there is one.
#[derive(Debug, Clone)]
pub struct Finding {
    /// The problem, anchored at its source span.
    pub diagnostic: Diagnostic,
    /// The complete error chain, including the kind and variable contexts the failing judgement
    /// was checked under. Too noisy for default output, but useful when debugging a type error.
    pub detail: Option<String>,
}

/// Outcome of [`check_source`].
#[derive(Debug, Clone)]
pub struct CheckReport {
    /// Parse, semantic, concretization, and type findings, ordered by source position.
    pub findings: Vec<Finding>,
    /// The size assignment the module was checked under, including defaulted values.
    pub sizes: Ctx<Tid, usize>,
    /// `Size` parameters that the caller left unset and that received a default value.
    pub defaulted: Vec<Tid>,
    /// Caller-provided sizes that name no size or range type variable in the module.
    pub unknown: Vec<Tid>,
    /// The concretized module, when it concretized and type-checked without errors; later
    /// stages (Graph IR construction) start from it.
    pub module: Option<CModule>,
}

impl CheckReport {
    /// Whether any finding is an error (warnings alone do not fail a check).
    pub fn has_errors(&self) -> bool {
        self.findings
            .iter()
            .any(|f| f.diagnostic.severity == Severity::Error)
    }
}

/// Parse and type-check `src` under `sizes`, stopping before Graph IR construction.
///
/// Type checking is skipped when parsing or the semantic checks report an error, since those
/// errors would otherwise cascade into spurious type errors.
pub fn check_source(src: &str, sizes: &Ctx<Tid, usize>) -> CheckReport {
    let (module, diags) = UModule::parse(src);
    let mut report = CheckReport {
        findings: diags
            .into_iter()
            .map(|diagnostic| Finding {
                diagnostic,
                detail: None,
            })
            .collect(),
        sizes: Ctx::new(),
        defaulted: vec![],
        unknown: vec![],
        module: None,
    };
    let Some(module) = module else {
        return report;
    };
    if report.has_errors() {
        return report;
    }

    let params = size_params(&module);
    report.unknown = sizes
        .iter()
        .map(|(k, _)| k.clone())
        .filter(|k| !params.contains(k))
        .collect();
    let known: Ctx<Tid, usize> = sizes
        .iter()
        .filter(|(k, _)| params.contains(k))
        .map(|(k, v)| (k.clone(), *v))
        .collect();
    report.sizes = minimal_sizes_with(&module, &known);
    report.defaulted = report
        .sizes
        .iter()
        .map(|(k, _)| k.clone())
        .filter(|k| !sizes.contains(k))
        .collect();

    match module.concretize(&report.sizes) {
        Ok(cmodule) => {
            let fctx: Set<CSig> = cmodule.iter().map(|(sig, _)| sig.clone()).collect();
            let mut instances: HashMap<&str, usize> = HashMap::new();
            for (sig, _) in cmodule.iter() {
                *instances.entry(sig.name.node.0.as_str()).or_default() += 1;
            }
            // Range-kinded type variables expand one declaration into several instances that
            // share source spans, so the same error can surface once per instance.
            let mut seen = HashSet::new();
            for (sig, body) in cmodule.iter() {
                let Err(e) = body.typecheck(sig.clone(), &fctx) else {
                    continue;
                };
                let mut finding = type_error_finding(&e, sig.name.span.clone());
                let d = &finding.diagnostic;
                if !seen.insert((d.span.start, d.span.end, d.summary.clone())) {
                    continue;
                }
                if instances[sig.name.node.0.as_str()] > 1 {
                    finding.diagnostic = finding
                        .diagnostic
                        .note(&format!("in the instance `{}`", one_line(&sig.to_string())));
                }
                report.findings.push(finding);
            }
            if !report.has_errors() {
                report.module = Some(cmodule);
            }
        }
        Err(e) => report
            .findings
            .push(concretize_finding(&module, &report.sizes, e)),
    }

    report.findings.sort_by(|a, b| {
        a.diagnostic
            .span
            .start
            .cmp(&b.diagnostic.span.start)
            .then_with(|| a.diagnostic.severity.cmp(&b.diagnostic.severity))
    });
    report
}

/// A finding for type error `e`, anchored at the innermost expression inference located, or
/// at `fallback` when it recorded none.
pub fn type_error_finding(e: &TypeError, fallback: std::ops::Range<usize>) -> Finding {
    let span = e.span().unwrap_or(fallback);
    Finding {
        diagnostic: Diagnostic::error(Phase::Type, span, &e.summary())
            .primary_label("type error here"),
        detail: Some(e.to_string()),
    }
}

/// Source span of the binding of `name` in `module`: a declaration argument, or a `let`/`<-`
/// binding in any declaration body, preferring the protocol. With `random` set, only a `let`
/// whose value is a `random<..>` sample matches, and an unnamed (`None`) sample matches the
/// only `random<..>` in the protocol, if there is exactly one.
pub fn binding_span(
    module: &CModule,
    name: Option<&Vid>,
    random: bool,
) -> Option<std::ops::Range<usize>> {
    // Protocol first, so its bindings win over same-named ones in helper functions.
    let decls = || {
        module
            .iter()
            .filter(|(_, b)| b.is_proto())
            .chain(module.iter().filter(|(_, b)| !b.is_proto()))
    };
    let Some(name) = name else {
        let mut samples = Vec::new();
        for (_, body) in decls().filter(|(_, b)| b.is_proto()) {
            for_each_exp(body, &mut |e| {
                if matches!(e.node, Exp::Random(..)) {
                    samples.push(e.span.clone());
                }
            });
        }
        samples.dedup();
        return (samples.len() == 1).then(|| samples.remove(0));
    };
    if !random {
        if let Some(arg) = decls()
            .flat_map(|(sig, _)| sig.args.iter())
            .find(|arg| arg.id.node == *name)
        {
            return Some(arg.id.span.clone());
        }
    }
    let mut found = None;
    for (_, body) in decls() {
        for_each_exp(body, &mut |e| {
            let (var, val) = match &e.node {
                Exp::Let(Some(var), val, _) | Exp::Log(var, val, _) => (var, val),
                _ => return,
            };
            if var.node == *name && (!random || matches!(val.node, Exp::Random(..))) {
                found.get_or_insert_with(|| var.span.clone());
            }
        });
        if found.is_some() {
            break;
        }
    }
    found
}

fn for_each_exp(body: &CBody, f: &mut impl FnMut(&Spanned<CExp>)) {
    fn walk(e: &Spanned<CExp>, f: &mut impl FnMut(&Spanned<CExp>)) {
        f(e);
        for child in e.node.children() {
            walk(child, f);
        }
    }
    match body {
        Body::Proto { body, relation } => {
            walk(relation, f);
            if let Some(b) = body {
                walk(b, f);
            }
        }
        Body::Func { body: Some(b) } => walk(b, f),
        Body::Func { body: None } | Body::TypeAlias => {}
    }
}

/// Find the smallest concrete value for each `Kind::SizeVar` parameter in the module
/// such that all dependent `Kind::Range` expressions have at least one element.
pub fn find_minimal_sizes(module: &UModule) -> Ctx<Tid, usize> {
    minimal_sizes_with(module, &Ctx::new())
}

/// [`find_minimal_sizes`], but keeping every value in `fixed` and choosing the remaining
/// `Size` parameters given those values.
fn minimal_sizes_with(module: &UModule, fixed: &Ctx<Tid, usize>) -> Ctx<Tid, usize> {
    // Pass 1: Collect all SizeVar params
    let mut size_vars: Vec<Tid> = Vec::new();
    for (sig, _body) in module.iter() {
        for tv in &sig.typevars.0 {
            if matches!(&tv.kind, Kind::SizeVar) && !size_vars.contains(&tv.id.node) {
                size_vars.push(tv.id.node.clone());
            }
        }
    }

    // Pass 2: Collect all Range params that depend on SizeVars
    let mut ranges: Vec<Range<Size>> = Vec::new();
    for (sig, _body) in module.iter() {
        for tv in &sig.typevars.0 {
            if let Kind::Range(r) = &tv.kind {
                if range_free_vars(r).iter().any(|v| size_vars.contains(v)) {
                    ranges.push(r.clone());
                }
            }
        }
    }

    // For each SizeVar, brute-force S=1..=10 to find the smallest value
    // where all dependent ranges have at least one element (start < end)
    let mut sizes = fixed.clone();
    for sv in &size_vars {
        if sizes.contains(sv) {
            continue;
        }
        let mut found = false;
        for candidate in 1..=10usize {
            let mut ctx = sizes.clone();
            ctx.insert(sv, &candidate);

            let all_ok = ranges.iter().all(|r| {
                if !range_free_vars(r).contains(sv) {
                    return true; // Not dependent on this SizeVar
                }
                r.clone()
                    .traverse1(&mut |s| s.eval(&ctx))
                    .is_ok_and(|cr| cr.start() < cr.end())
            });

            if all_ok {
                sizes.insert(sv, &candidate);
                found = true;
                break;
            }
        }
        if !found {
            // Fallback: use 3 if brute-force fails
            sizes.insert(sv, &3);
        }
    }
    sizes
}

fn range_free_vars(r: &Range<Size>) -> Set<Tid> {
    r.start.node.free_vars().union(
        r.end
            .as_ref()
            .map(|e| e.node.free_vars())
            .unwrap_or_default(),
    )
}

/// Type variables a caller may assign through `sizes`: `Size` parameters, and range-kinded
/// variables (pinning one checks a single value instead of the whole range).
fn size_params(module: &UModule) -> Set<Tid> {
    module
        .iter()
        .flat_map(|(sig, _)| sig.typevars.0.iter())
        .filter(|tv| matches!(tv.kind, Kind::SizeVar | Kind::Range(_)))
        .map(|tv| tv.id.node.clone())
        .collect()
}

fn concretize_finding(module: &UModule, sizes: &Ctx<Tid, usize>, e: ModuleError) -> Finding {
    // `UModule::concretize` does not say which declaration failed; redo the per-declaration
    // step to find it.
    let failing_decl_span = || {
        module
            .iter_decls()
            .find(|d| UModule::concretize_decl(d, sizes).is_err())
            .map_or(0..0, |d| d.sig.name.span.clone())
    };
    let (span, summary) = match &e {
        ModuleError::OverlapDeclaration(sig) => (
            sig.name.span.clone(),
            format!(
                "ModuleError: Overlapping declarations of `{}` after size concretization",
                sig.name.node
            ),
        ),
        ModuleError::DeclarationError(DeclError::EvalError(ee)) => (
            failing_decl_span(),
            format!("DeclError: Cannot evaluate a size expression: {ee}"),
        ),
        ModuleError::DeclarationError(DeclError::InvalidRange(sig, re)) => (
            sig.name.span.clone(),
            format!("DeclError: Invalid range in `{}`: {re}", sig.name.node),
        ),
        ModuleError::DeclarationError(DeclError::SubstError(se)) => {
            (failing_decl_span(), format!("DeclError: {se}"))
        }
        ModuleError::DeclarationNotFound(name) => {
            (0..0, format!("ModuleError: Declaration not found: {name}"))
        }
    };
    let mut diagnostic = Diagnostic::error(Phase::Type, span, &one_line(&summary))
        .primary_label("while concretizing sizes for this declaration");
    if let ModuleError::OverlapDeclaration(sig) = &e {
        diagnostic = diagnostic.note(&format!(
            "both declarations concretize to `{}`",
            one_line(&sig.to_string())
        ));
    }
    Finding {
        diagnostic,
        detail: Some(e.to_string()),
    }
}

fn one_line(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn errors(report: &CheckReport) -> Vec<&Diagnostic> {
        report
            .findings
            .iter()
            .map(|f| &f.diagnostic)
            .filter(|d| d.severity == Severity::Error)
            .collect()
    }

    #[test]
    fn well_typed_protocol_has_no_findings() {
        let src = r"
proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = random<F>;
    u <- g * r;
    c <- challenge<F*>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
";
        let report = check_source(src, &Ctx::new());
        assert!(report.findings.is_empty(), "{:?}", report.findings);
        assert!(report.sizes.is_empty());
    }

    #[test]
    fn type_error_points_at_the_failing_subexpression() {
        let src = r"
proto bad<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    u <- g * x;
    verify(x + g == u)
}
";
        let report = check_source(src, &Ctx::new());
        let errs = errors(&report);
        assert_eq!(errs.len(), 1, "{:?}", report.findings);
        assert_eq!(&src[errs[0].span.clone()], "x + g");
        assert_eq!(errs[0].phase, Phase::Type);
        assert!(
            errs[0].summary.starts_with("LubError"),
            "{}",
            errs[0].summary
        );
    }

    #[test]
    fn where_clause_error_is_reported() {
        let src = r"
proto bad<G: Group, F: Scalar<G>>(witness x: F, instance h: G) where h == x {
    verify(h == h)
}
";
        let report = check_source(src, &Ctx::new());
        let errs = errors(&report);
        assert_eq!(errs.len(), 1, "{:?}", report.findings);
        assert_eq!(&src[errs[0].span.clone()], "h == x");
    }

    #[test]
    fn size_dependent_error_depends_on_given_sizes() {
        // Indexing a[1] needs at least two elements.
        let src = r"
proto p<F: Field, N: Size>(instance a: [F; N]) where a[1] == a[1] {
    verify(a[1] == a[1])
}
";
        let defaulted = check_source(src, &Ctx::new());
        assert!(defaulted.has_errors());
        assert_eq!(defaulted.defaulted, vec![Tid::new("N")]);
        assert_eq!(defaulted.sizes.get(&Tid::new("N")), Some(&1));

        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &2);
        let pinned = check_source(src, &sizes);
        assert!(!pinned.has_errors(), "{:?}", pinned.findings);
        assert!(pinned.defaulted.is_empty());
    }

    #[test]
    fn unknown_sizes_are_reported() {
        let src = r"
proto p<F: Field>(instance a: F) where a == a {
    verify(a == a)
}
";
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("Q"), &4);
        let report = check_source(src, &sizes);
        assert_eq!(report.unknown, vec![Tid::new("Q")]);
        assert!(
            report.sizes.is_empty(),
            "unknown sizes are not reported as used"
        );
    }

    #[test]
    fn errors_in_several_instances_are_reported_once() {
        // Every instance N = 1..4 fails at the same span.
        let src = r"
fn f<F: Field, G: Group, N: 1..4>(instance a: [F; N], instance g: G) -> F {
    a[0] + g
}
proto p<F: Field, G: Group>(instance a: [F; 3], instance g: G) where a[0] == a[0] {
    verify(f(a, g) == a[0])
}
";
        let report = check_source(src, &Ctx::new());
        let errs = errors(&report);
        assert_eq!(errs.len(), 1, "{:?}", report.findings);
        assert_eq!(&src[errs[0].span.clone()], "a[0] + g");
        assert!(errs[0].notes[0].message.contains("in the instance"));
    }

    #[test]
    fn parse_errors_skip_type_checking() {
        let report = check_source("proto p<F: Field>(instance a: F) where { ", &Ctx::new());
        assert!(report.has_errors());
        assert!(report
            .findings
            .iter()
            .all(|f| f.diagnostic.phase == Phase::Parse));
    }

    #[test]
    fn concretize_error_is_located_at_its_declaration() {
        let src = r"
fn sum<N: 0..3, F: Field>(instance a: [F; N]) -> F {
    sum(a[0..2^(N-1)]) + sum(a[2^(N-1)..2^N])
}
proto p<F: Field>(instance a: F) where a == a {
    verify(a == a)
}
";
        let report = check_source(src, &Ctx::new());
        let errs = errors(&report);
        assert_eq!(errs.len(), 1, "{:?}", report.findings);
        assert_eq!(&src[errs[0].span.clone()], "sum");
    }

    /// Regression: `find_minimal_sizes` must collect all `SizeVars` before
    /// collecting ranges, so ranges that appear before their `SizeVar`
    /// in typevars are still found.
    #[test]
    fn test_find_minimal_sizes_ordering() {
        // Protocol where N: 1..S appears before S: Size in a different declaration
        let src = r"
            fn foo<F: Field, N: 1..S, S: Size>(a: [F; N]) -> F { a[0] }
            proto bar<F: Field, S: Size, M: 2..S+1>(instance x: F) where x == x {
                verify(x == x)
            }
        ";
        let module = UModule::parse(src).0.unwrap();
        let sizes = find_minimal_sizes(&module);
        // S should be found and have a value ≥ 2 (so N: 1..S and M: 2..S+1 are non-empty)
        assert!(
            sizes.get(&Tid::new("S")).is_some(),
            "SizeVar S should be found even when Range appears first"
        );
        let s_val = *sizes.get(&Tid::new("S")).unwrap();
        assert!(s_val >= 2, "S should be ≥ 2, got {}", s_val);
    }
}
