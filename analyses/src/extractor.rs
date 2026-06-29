use crate::frontend::{Polynomial, TransClos};
use crate::ideal::{Ideal, IdealBuilder};
use backend::ATyp;
use backend::ArkConfig;
use backend::op::{GOp, HasOpFactory, mk};
use graph::Op;
use graph::PRef;
use lang::ast::BinOp;

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
    builder: &IdealBuilder<C>,
    tc: &TransClos<C>,
) -> Ideal<C> {
    let tc_no_equ = strip_equ(tc);
    let mut comp_builder = builder.clone();
    comp_builder.build(tc_no_equ)
}

fn strip_equ<C: ArkConfig + HasOpFactory>(tc: &TransClos<C>) -> TransClos<C> {
    let mut tc_no_equ = tc.clone();
    for entry in &mut tc_no_equ.clos {
        let pr = entry.0.clone();
        entry.1 = strip_equ_op(entry.1.clone(), &pr);
    }
    tc_no_equ
}

fn strip_equ_op<C: ArkConfig + HasOpFactory>(op: GOp<C>, result: &PRef) -> GOp<C> {
    match op {
        Op::Bin(BinOp::Equ, ..) => Op::Ref(
            backend::op::Ref(result.reference.node()),
            result.typ.clone(),
        ),
        Op::Map(d, b) => Op::Map(
            mk(strip_equ_op(d.get().clone(), result)),
            mk(strip_equ_op(b.get().clone(), result)),
        ),
        Op::ReduceMap(rop, d, b) => Op::ReduceMap(
            rop,
            mk(strip_equ_op(d.get().clone(), result)),
            mk(strip_equ_op(b.get().clone(), result)),
        ),
        Op::Reduce(rop, v) => Op::Reduce(rop, mk(strip_equ_op(v.get().clone(), result))),
        Op::Bin(bop, a, b, typ) => Op::Bin(
            bop,
            mk(strip_equ_op(a.get().clone(), result)),
            mk(strip_equ_op(b.get().clone(), result)),
            typ,
        ),
        Op::Check(a) => Op::Check(mk(strip_equ_op(a.get().clone(), result))),
        Op::Interpolate(pts, evals) => Op::Interpolate(
            mk(strip_equ_op(pts.get().clone(), result)),
            mk(strip_equ_op(evals.get().clone(), result)),
        ),
        Op::Evaluate(p, range, xs) => Op::Evaluate(
            mk(strip_equ_op(p.get().clone(), result)),
            range,
            xs.map(|v| mk(strip_equ_op(v.get().clone(), result))),
        ),
        Op::Vec(vs) => Op::Vec(
            vs.into_iter()
                .map(|v| mk(strip_equ_op(v.get().clone(), result)))
                .collect(),
        ),
        Op::Ram(a, b) => Op::Ram(
            mk(strip_equ_op(a.get().clone(), result)),
            mk(strip_equ_op(b.get().clone(), result)),
        ),
        Op::Poly(v) => Op::Poly(mk(strip_equ_op(v.get().clone(), result))),
        Op::Mle(v) => Op::Mle(mk(strip_equ_op(v.get().clone(), result))),
        Op::Coef(v) => Op::Coef(mk(strip_equ_op(v.get().clone(), result))),
        Op::Ifft(v) => Op::Ifft(mk(strip_equ_op(v.get().clone(), result))),
        Op::Fft(v) => Op::Fft(mk(strip_equ_op(v.get().clone(), result))),
        other => other,
    }
}
