use crate::AnalysisBackend;
use crate::frontend::Polynomial;
use backend::ATyp;

/// Check whether a polynomial's group-variable terms are compatible with
/// extracting a witness of the given type:
///
/// - **Scalar**: must have no group variables at all.
/// - **G1**: each term may contain at most one G1 var; no G2 or GT vars.
/// - **G2**: each term may contain at most one G2 var; no G1 or GT vars.
/// - **GT**: each term may contain either at most one GT var (no G1/G2),
///   or at most one G1 and one G2 var (no GT).
pub(crate) fn valid_extractor<C: AnalysisBackend>(
    witness_typ: &ATyp,
    poly: &Polynomial<C::F>,
) -> bool {
    for term in poly.terms.keys() {
        let vars = term.vars();
        let pows = term.powers();
        // Total power of the term's variables whose type satisfies `is`.
        let power = |is: fn(&ATyp) -> bool| -> usize {
            vars.iter()
                .zip(&pows)
                .filter(|(v, _)| is(&v.typ))
                .map(|(_, &i)| i)
                .sum()
        };
        let (g1, g2, gt) = (power(ATyp::is_g1), power(ATyp::is_g2), power(ATyp::is_gt));
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
