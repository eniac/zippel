use crate::Var;
use crate::frontend::{Polynomial, TransClos};
use crate::ideal::{Ideal, IdealBuilder};
use backend::ATyp;
use backend::ArkConfig;
use backend::op::{GOp, HOp, HasOpFactory, mk};
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

/// Extract constraints for all intermediates of the given transitive closure
/// by stripping its checks and building the Gröbner basis.
///
/// Each basis polynomial defines an intermediate variable in terms of
/// arguments and other witnesses, collectively serving as Skolem function
/// for the existentially quantified intermediates.
///
/// ## Stripping checks
///
/// `Op::Verify(exp)` (a verifier check) and `Op::Assert(exp)` (the `where`
/// clause) are checks, not definitions. Both are neutralised to
/// `Op::Ref(var)` — an identity operation that defines the result Var
/// without emitting any assertion polynomial — so the locals never assume
/// what the protocol is checking.
///
/// ## Shared builder and Var alignment
///
/// The `builder` is cloned before use so that its witness/sentinel allocation
/// counters remain unchanged. **The caller must immediately use the original
/// (un-cloned) builder to build the same `TransClos` (or a superset) whose
/// locals were extracted.** This ensures that sentinel variables allocated
/// by `extract_locals`'s internal clone receive the same `Var` identities
/// as those allocated by the caller's subsequent build, keeping references
/// aligned across the two results.
pub fn extract_locals<C: ArkConfig + HasOpFactory>(
    builder: &IdealBuilder<C>,
    tc: &TransClos<C>,
) -> Ideal<C> {
    let definitions = strip_checks(tc);
    let mut comp_builder = builder.clone();
    comp_builder.build(definitions)
}

/// `tc` with every `Verify` and `Assert` stripped; see [`strip_checks_op`].
fn strip_checks<C: ArkConfig + HasOpFactory>(tc: &TransClos<C>) -> TransClos<C> {
    let mut definitions = tc.clone();
    for (var, op) in &mut definitions.clos {
        *op = strip_checks_op(op.clone(), var);
    }
    definitions
}

/// `op` with every `Verify` and `Assert` in it replaced by an identity on
/// `result`.
fn strip_checks_op<C: ArkConfig + HasOpFactory>(op: GOp<C>, result: &Var) -> GOp<C> {
    let strip = |o: &HOp<C>| mk(strip_checks_op(o.get().clone(), result));
    match op {
        Op::Verify(_) | Op::Assert(_) => Op::Ref(
            backend::op::Ref(result.reference.node()),
            result.typ.clone(),
        ),
        Op::Map(d, b) => Op::Map(strip(&d), strip(&b)),
        Op::ReduceMap(rop, d, b) => Op::ReduceMap(rop, strip(&d), strip(&b)),
        Op::Reduce(rop, v) => Op::Reduce(rop, strip(&v)),
        Op::Bin(bop, a, b, typ) => Op::Bin(bop, strip(&a), strip(&b), typ),
        Op::Interpolate(pts, evals) => Op::Interpolate(strip(&pts), strip(&evals)),
        Op::Evaluate(p, range, xs) => Op::Evaluate(strip(&p), range, xs.map(|v| strip(&v))),
        Op::Vec(vs) => Op::Vec(vs.iter().map(strip).collect()),
        Op::Ram(a, b) => Op::Ram(strip(&a), strip(&b)),
        Op::Poly(v) => Op::Poly(strip(&v)),
        Op::Mle(v) => Op::Mle(strip(&v)),
        Op::Coef(v) => Op::Coef(strip(&v)),
        Op::ToScalar(v) => Op::ToScalar(strip(&v)),
        Op::Ifft(v) => Op::Ifft(strip(&v)),
        Op::Fft(v) => Op::Fft(strip(&v)),
        other => other,
    }
}
