use crate::Op;
use crate::PRef;
use crate::analyses::groebner::ark_gb_adapter::get_local_rank;
use crate::analyses::groebner::monomial::{GrevLexTerm, Monomial};
use crate::analyses::groebner::tiered::{TieredElimMono, TieredElimStrategy};
use crate::analyses::groebner::{GroebnerBuilder, GroebnerResult, SparsePolynomial};
use crate::analyses::trans_clos::TransClos;
use backend::ATyp;
use backend::ArkConfig;
use backend::op::HasOpFactory;
use lang::ast::BinOp;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExtractLocal;

impl TieredElimStrategy for ExtractLocal {
    fn tier(v: &PRef) -> Option<usize> {
        if get_local_rank(v).is_some() {
            Some(0)
        } else {
            Some(1)
        }
    }
}

pub type ExtractLocalTerm = TieredElimMono<ExtractLocal>;

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

/// Extract constraints for all intermediates of the given transitive closure
/// by stripping `Equ` assertions and building the Gröbner basis.
///
/// Each basis polynomial defines an intermediate variable in terms of
/// arguments and other witnesses, collectively serving as Skolem function
/// for the existentially quantified intermediates.
///
/// ## Replacing Equality nodes
///
/// `Op::Bin(BinOp::Equ, ...)` entries represent assertions, not definitions.
/// They are neutralised to `Op::Ref(pr)` — an identity operation that
/// defines the result PRef without emitting any assertion polynomial.
///
/// ## Shared builder and PRef alignment
///
/// The `builder` is cloned befor
///
/// ## Replacing Equality nodes
///
/// `Op::Bin(BinOp::Equ, ...)` entries represent assertions.
/// They are neutralised to `Op::Ref(pr)` — an identity operation that
/// defines the result PRef without emitting any assertion polynomial.
///
/// ## Shared builder and PRef alignment
///
/// The `builder` is cloned before use so that its witness/sentinel allocation
/// counters remain unchanged. **The caller must immediately use the original
/// (un-cloned) builder to build the same `TransClos` (or a superset) whose
/// locals were extracted.** This ensures that `div_wit` and other sentinel
/// variables allocated by `extract_locals`'s internal clone receive the same
/// `PRef` identities as those allocated by the caller's subsequent build,
/// keeping division-witness references aligned across the two results.
pub fn extract_locals<C: ArkConfig + HasOpFactory>(
    builder: &GroebnerBuilder<C, GrevLexTerm>,
    tc: &TransClos<C>,
) -> GroebnerResult<C, GrevLexTerm> {
    let tc_no_equ = strip_equ(tc);
    let mut comp_builder = builder.clone();
    comp_builder.build(tc_no_equ)
}

fn strip_equ<C: ArkConfig>(tc: &TransClos<C>) -> TransClos<C> {
    let mut tc_no_equ = tc.clone();
    for entry in &mut tc_no_equ.clos {
        if let Op::Bin(BinOp::Equ, ..) = entry.1 {
            let pr = entry.0.clone();
            entry.1 = Op::Ref(pr.reference, pr.typ.clone());
        }
    }
    tc_no_equ
}
