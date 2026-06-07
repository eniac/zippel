use crate::PRef;
use crate::analyses::groebner::ark_gb_adapter::{
    ArgNodeGuard, LocalRankGuard, get_local_rank, is_arg_node,
};
use crate::analyses::groebner::monomial::{GrevLexTerm, LexElimMono, LexElimStrategy, Monomial};
use crate::analyses::groebner::{GroebnerBuilder, GroebnerResult, SparsePolynomial};
use crate::analyses::trans_clos::TransClos;
use ark_ff::Zero;
use backend::ArkConfig;
use backend::op::HasOpFactory;
use core::cmp::Ordering;
use log::{info, warn};
use share::Set;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExtractLocal;

impl LexElimStrategy for ExtractLocal {
    fn eliminate_var(v: &PRef) -> bool {
        !is_arg_node(v)
    }

    fn cmp_vars(a: &PRef, b: &PRef) -> Ordering {
        let a_elim = !is_arg_node(a);
        let b_elim = !is_arg_node(b);
        match (a_elim, b_elim) {
            (true, true) => {
                let ra = get_local_rank(a);
                let rb = get_local_rank(b);
                rb.cmp(&ra).then_with(|| a.cmp(b))
            }
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => a.cmp(b),
        }
    }
}

pub type ExtractLocalTerm = LexElimMono<ExtractLocal>;

type Poly<C> = SparsePolynomial<<C as ArkConfig>::F, ExtractLocalTerm>;
type GPoly<C> = SparsePolynomial<<C as ArkConfig>::F, GrevLexTerm>;

pub(crate) fn convert_poly<C: ArkConfig>(p: &Poly<C>) -> GPoly<C> {
    let mut terms: share::Ctx<GrevLexTerm, C::F> = share::Ctx::new();
    for (term, coeff) in p.terms.iter() {
        let pairs: Vec<(PRef, usize)> = term.vars().into_iter().zip(term.powers()).collect();
        let new_term: GrevLexTerm = pairs.into();
        *terms.entry(new_term).or_insert(C::F::zero()) += *coeff;
    }
    SparsePolynomial { terms }
}
/// Best-effort extraction of local variables from the relation TC.
///
/// Computes a Gröbner basis with a pure-lex elimination ordering that
/// prioritises non-arg variables, then scans the basis for polynomials whose
/// leading term is a single non-arg variable with all remaining variables
/// visible (args or already extracted).  Each such polynomial is an
/// *extractor* for that variable.
///
/// Candidates are processed in ascending NodeIndex order so that
/// earlier-introduced variables are extracted first and become visible
/// when checking later ones.
///
/// This is best-effort: if no extractor exists for a given variable
/// (e.g. the leading term is not a single variable, or the remainder
/// contains invisible variables), the variable is simply skipped.  The
/// caller decides how to handle unextracted variables.
///
/// ## Two-phase construction
///
/// The polynomials are first built with `GrevLexTerm` (which has a stable
/// `Ord` backed only by `PRef`), then converted to `ExtractLocalTerm`
/// (a pure-lex elimination monomial whose `Ord` depends on
/// `LocalRankGuard`). This avoids BTreeMap corruption: `ExtractLocalTerm`'s
/// `Ord` calls `get_local_rank()`, which returns `usize::MAX` for every
/// variable before the guard is installed. If polynomials were created
/// under that default ordering and the guard were later changed, the
/// BTreeMap invariants would silently break — entries become unreachable,
/// polynomials appear empty, and the GB reducer eliminates them as zero.
/// By building with the stable `GrevLexTerm` first and converting only
/// after the guard is in place, every BTreeMap is constructed with the
/// correct ordering from the start.
pub fn extract_locals<C: ArkConfig + HasOpFactory>(tc: &TransClos<C>) -> Vec<(PRef, GPoly<C>)> {
    let arg_nodes: std::collections::HashSet<usize> = tc
        .prefs
        .iter()
        .map(|pr| pr.reference.node().index())
        .collect();
    let _arg_guard = ArgNodeGuard::install(arg_nodes);

    let mut builder: GroebnerBuilder<C, GrevLexTerm> = GroebnerBuilder::new();
    let grev_result = builder.build(tc.clone());

    let rank_map: std::collections::HashMap<usize, usize> = grev_result
        .var_order
        .iter()
        .enumerate()
        .filter(|(_, pr)| !is_arg_node(pr))
        .map(|(i, pr)| (pr.reference.node().index(), i))
        .collect();
    let _rank_guard = LocalRankGuard::install(rank_map);

    let mut result = GroebnerResult::<C, ExtractLocalTerm>::reconstruct_from(&grev_result);

    eprintln!(
        "EXTRACT_LOCALS basis BEFORE run ({} polys):",
        result.basis.len()
    );
    for (i, p) in result.basis.iter().enumerate() {
        eprintln!("  [{}] {}", i, p);
    }

    result.run::<128>();

    eprintln!(
        "EXTRACT_LOCALS var_order ({} vars):",
        result.var_order.len()
    );
    for (i, pr) in result.var_order.iter().enumerate() {
        eprintln!(
            "  [{}] {} elim={} is_arg={}",
            i,
            pr.verbose(),
            ExtractLocal::eliminate_var(pr),
            is_arg_node(pr)
        );
    }
    eprintln!("EXTRACT_LOCALS basis ({} polys):", result.basis.len());
    for (i, p) in result.basis.iter().enumerate() {
        eprintln!("  [{}] {}", i, p);
    }

    let mut candidates: Vec<(PRef, Poly<C>)> = Vec::new();
    for poly in result.basis.iter() {
        if let Some((_lc, lt)) = poly.leading_term() {
            let lt_vars = lt.vars();
            let lt_powers = lt.powers();
            eprintln!(
                "  CANDIDATE SCAN: poly={} lt_vars={:?} lt_powers={:?}",
                poly,
                lt_vars.iter().map(|v| v.verbose()).collect::<Vec<_>>(),
                lt_powers
            );
            if lt_vars.len() != 1 || lt_powers[0] != 1 {
                eprintln!("    SKIP: not single var power 1");
                continue;
            }
            let var = &lt_vars[0];
            if is_arg_node(var) {
                eprintln!("    SKIP: {} is arg node", var.verbose());
                continue;
            }
            eprintln!("    ACCEPT: {}", var.verbose());
            candidates.push((var.clone(), poly.clone()));
        }
    }
    candidates.sort_by_key(|(v, _)| get_local_rank(v));

    eprintln!("  CANDIDATES sorted:");
    for (v, p) in &candidates {
        eprintln!("    {} rank={} => {}", v.verbose(), get_local_rank(v), p);
    }

    let mut extracted: Set<PRef> = Set::new();
    let mut found_extractors: Vec<(PRef, GPoly<C>)> = Vec::new();

    for (var, poly) in candidates {
        if extracted.contains(&var) {
            continue;
        }

        let remainder_vars: Set<PRef> = poly
            .terms
            .iter()
            .filter(|(t, _)| {
                let tv = t.vars();
                let tp = t.powers();
                !(tv.len() == 1 && tv[0] == var && tp[0] == 1)
            })
            .flat_map(|(t, _)| t.vars())
            .collect();

        let all_visible = remainder_vars
            .iter()
            .all(|v| is_arg_node(v) || extracted.contains(v));
        if !all_visible {
            eprintln!(
                "Local extractor for {:?} has invisible remainder vars {:?}, skipping",
                var, remainder_vars
            );
            continue;
        }

        let is_field_var = var.typ.is_scalar();
        if is_field_var {
            let has_group_var = remainder_vars.iter().any(|v| v.typ.is_group());
            if has_group_var {
                warn!(
                    "Local extractor for field var {:?} depends on group vars, skipping",
                    var
                );
                continue;
            }
        } else {
            let mut valid = true;
            for (term, _coeff) in poly.terms.iter() {
                let group_count: usize = term
                    .iter()
                    .filter_map(|(v, i)| if v.typ.is_group() { Some(*i) } else { None })
                    .sum();
                eprintln!("    GROUP CHECK: {} group_count={}", term, group_count);
                if group_count > 1 {
                    valid = false;
                    break;
                }
            }
            if !valid {
                warn!(
                    "Local extractor for {:?} has multi-group term, skipping",
                    var
                );
                continue;
            }
        }

        eprintln!("    EXTRACTOR FOUND: {} => {}", var.verbose(), poly);
        info!("Found local extractor for {:?}", var);
        extracted.insert(var.clone());
        found_extractors.push((var.clone(), convert_poly::<C>(&poly)));
    }

    found_extractors
}
