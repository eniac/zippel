use crate::PRef;
use crate::analyses::groebner::ark_gb_adapter::{LocalRankGuard, get_local_rank};
use crate::analyses::groebner::monomial::{GrevLexTerm, LexElimMono, LexElimStrategy, Monomial};
use crate::analyses::groebner::{GroebnerBuilder, GroebnerResult, SparsePolynomial};
use crate::analyses::trans_clos::TransClos;
use ark_ff::Zero;
use backend::ATyp;
use backend::ArkConfig;
use backend::op::HasOpFactory;
use core::cmp::Ordering;
use log::{info, warn};
use share::Set;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExtractLocal;

impl LexElimStrategy for ExtractLocal {
    fn eliminate_var(v: &PRef) -> bool {
        get_local_rank(v).is_some()
    }

    fn cmp_vars(a: &PRef, b: &PRef) -> Ordering {
        let a_rank = get_local_rank(a);
        let b_rank = get_local_rank(b);
        match (a_rank, b_rank) {
            (Some(ra), Some(rb)) => rb.cmp(&ra).then_with(|| a.cmp(b)),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => a.cmp(b),
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

/// Check whether a polynomial's group-variable terms are compatible with
/// extracting a witness of the given type:
///
/// - **Scalar**: must have no group variables at all.
/// - **G1**: each term may contain at most one G1 var; no G2 or GT vars.
/// - **G2**: each term may contain at most one G2 var; no G1 or GT vars.
/// - **GT**: each term may contain either at most one GT var (no G1/G2),
///   or at most one G1 and one G2 var (no GT).
pub(crate) fn valid_extractor<C: ArkConfig, T: Monomial>(
    witness_typ: &ATyp,
    poly: &SparsePolynomial<C::F, T>,
) -> bool {
    for (term, _coeff) in poly.terms.iter() {
        let vars = term.vars();
        let pows = term.powers();
        let g1: usize = vars
            .iter()
            .zip(pows.iter())
            .filter_map(|(v, &i)| if v.typ.is_g1() { Some(i) } else { None })
            .sum();
        let g2: usize = vars
            .iter()
            .zip(pows.iter())
            .filter_map(|(v, &i)| if v.typ.is_g2() { Some(i) } else { None })
            .sum();
        let gt: usize = vars
            .iter()
            .zip(pows.iter())
            .filter_map(|(v, &i)| if v.typ.is_gt() { Some(i) } else { None })
            .sum();
        let valid = if witness_typ.is_scalar() {
            g1 == 0 && g2 == 0 && gt == 0
        } else if witness_typ.is_g1() {
            g1 == 1 && g2 == 0 && gt == 0
        } else if witness_typ.is_g2() {
            g2 == 1 && g1 == 0 && gt == 0
        } else if witness_typ.is_gt() {
            (gt == 1 && g1 == 0 && g2 == 0) || (gt == 0 && g1 == 1 && g2 == 1)
        } else {
            true
        };
        if !valid {
            return false;
        }
    }
    true
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
    let arg_node_set: std::collections::HashSet<usize> = tc
        .prefs
        .iter()
        .map(|pr| pr.reference.node().index())
        .collect();

    let mut builder: GroebnerBuilder<C, GrevLexTerm> = GroebnerBuilder::new();
    let grev_result = builder.build(tc.clone());

    let rank_map: std::collections::HashMap<usize, usize> = grev_result
        .var_order
        .iter()
        .enumerate()
        .map(|(i, pr)| (pr.reference.node().index(), i))
        .collect();

    debug_assert!(
        !rank_map.keys().any(|k| arg_node_set.contains(k)),
        "rank_map contains arg nodes: {:?}",
        rank_map
            .keys()
            .filter(|k| arg_node_set.contains(k))
            .collect::<Vec<_>>()
    );

    let _rank_guard = LocalRankGuard::install(rank_map);

    let mut result = GroebnerResult::<C, ExtractLocalTerm>::reconstruct_from(&grev_result);

    result.run::<128>();

    let mut candidates: Vec<(PRef, Poly<C>)> = Vec::new();
    for poly in result.basis.iter() {
        if let Some((_lc, lt)) = poly.leading_term() {
            let lt_vars = lt.vars();
            let lt_powers = lt.powers();
            if lt_vars.len() != 1 || lt_powers[0] != 1 {
                continue;
            }
            let var = &lt_vars[0];
            if get_local_rank(var).is_none() {
                continue;
            }
            candidates.push((var.clone(), poly.clone()));
        }
    }
    candidates.sort_by_key(|(v, _)| get_local_rank(v).unwrap());

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
            .all(|v| get_local_rank(v).is_none() || extracted.contains(v));
        if !all_visible {
            continue;
        }

        if !valid_extractor::<C, _>(&var.typ, &poly) {
            warn!("Local extractor for {:?} has invalid term, skipping", var);
            continue;
        }

        info!("Found local extractor for {:?}", var);
        extracted.insert(var.clone());
        found_extractors.push((var.clone(), convert_poly::<C>(&poly)));
    }

    found_extractors
}
