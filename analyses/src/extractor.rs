use crate::Var;
use crate::frontend::{Polynomial, TransClos};
use crate::ideal::{Ideal, IdealBuilder};
use backend::ATyp;
use backend::ArkConfig;
use backend::op::{GOp, HasOpFactory, mk};
use graph::Op;

/// Check whether a polynomial's group-variable terms are compatible with
/// extracting a witness of the given type:
///
/// - **Scalar**: must have no group variables at all.
/// - **G1**: each term may contain at most one G1 var; no G2 or GT vars.
/// - **G2**: each term may contain at most one G2 var; no G1 or GT vars.
/// - **GT**: each term may contain either at most one GT var (no G1/G2),
///   or at most one G1 and one G2 var (no GT).
pub(crate) fn valid_extractor<C: ArkConfig>(witness_typ: &ATyp, poly: &Polynomial<C::F>) -> bool {
    for term in poly.terms.keys() {
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
/// ## Replacing Check nodes
///
/// `Op::Check(lhs, rhs)` entries represent assertions (lhs == rhs), not
/// definitions. They are neutralised to `Op::Ref(var)` — an identity
/// operation that defines the result Var without emitting any assertion
/// polynomial.
///
/// ## Shared builder and Var alignment
///
/// The `builder` is cloned before use so that its witness/sentinel allocation
/// counters remain unchanged. **The caller must immediately use the original
/// (un-cloned) builder to build the same `TransClos` (or a superset) whose
/// locals were extracted.** This ensures that `div_wit` and other sentinel
/// variables allocated by `extract_locals`'s internal clone receive the same
/// `Var` identities as those allocated by the caller's subsequent build,
/// keeping division-witness references aligned across the two results.
pub fn extract_locals<C: ArkConfig + HasOpFactory>(
    builder: &IdealBuilder<C>,
    tc: &TransClos<C>,
) -> Ideal<C> {
    let tc_no_check = strip_check(tc);
    let mut comp_builder = builder.clone();
    comp_builder.build(tc_no_check)
}

fn strip_check<C: ArkConfig + HasOpFactory>(tc: &TransClos<C>) -> TransClos<C> {
    let mut tc_no_check = tc.clone();
    for entry in &mut tc_no_check.clos {
        let var = entry.0.clone();
        entry.1 = strip_check_op(entry.1.clone(), &var);
    }
    tc_no_check
}

fn strip_check_op<C: ArkConfig + HasOpFactory>(op: GOp<C>, result: &Var) -> GOp<C> {
    match op {
        Op::Check(_, _) => Op::Ref(
            backend::op::Ref(result.reference.node()),
            result.typ.clone(),
        ),
        Op::Map(d, b) => Op::Map(
            mk(strip_check_op(d.get().clone(), result)),
            mk(strip_check_op(b.get().clone(), result)),
        ),
        Op::ReduceMap(rop, d, b) => Op::ReduceMap(
            rop,
            mk(strip_check_op(d.get().clone(), result)),
            mk(strip_check_op(b.get().clone(), result)),
        ),
        Op::Reduce(rop, v) => Op::Reduce(rop, mk(strip_check_op(v.get().clone(), result))),
        Op::Bin(bop, a, b, typ) => Op::Bin(
            bop,
            mk(strip_check_op(a.get().clone(), result)),
            mk(strip_check_op(b.get().clone(), result)),
            typ,
        ),
        Op::Interpolate(pts, evals) => Op::Interpolate(
            mk(strip_check_op(pts.get().clone(), result)),
            mk(strip_check_op(evals.get().clone(), result)),
        ),
        Op::Evaluate(p, range, xs) => Op::Evaluate(
            mk(strip_check_op(p.get().clone(), result)),
            range,
            xs.map(|v| mk(strip_check_op(v.get().clone(), result))),
        ),
        Op::Vec(vs) => Op::Vec(
            vs.into_iter()
                .map(|v| mk(strip_check_op(v.get().clone(), result)))
                .collect(),
        ),
        Op::Ram(a, b) => Op::Ram(
            mk(strip_check_op(a.get().clone(), result)),
            mk(strip_check_op(b.get().clone(), result)),
        ),
        Op::Poly(v) => Op::Poly(mk(strip_check_op(v.get().clone(), result))),
        Op::Mle(v) => Op::Mle(mk(strip_check_op(v.get().clone(), result))),
        Op::Coef(v) => Op::Coef(mk(strip_check_op(v.get().clone(), result))),
        Op::Ifft(v) => Op::Ifft(mk(strip_check_op(v.get().clone(), result))),
        Op::Fft(v) => Op::Fft(mk(strip_check_op(v.get().clone(), result))),
        other => other,
    }
}
