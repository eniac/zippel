use super::*;
use crate::ast::range::{CRange, Range};
use crate::ast::spanned::Spanned;
use crate::ast::{Args, BinOp, CArg, CExp, Exp, Exps, Sig};
use crate::id::{Tid, Vid};
use crate::typ::{CTyp, Kind, TypeVar, TypeVars};
use lazy_static::lazy_static;
use share::{Ctx, Set};

fn lit<N>(v: N) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Lit(v))
}
fn varstr<N>(x: &str) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Var(Vid::from(x)))
}
fn range<N>(r: Range<N>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Range(r))
}
fn challenge<N>(t: Tid) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Challenge(t, false))
}
fn random<N>(t: Tid) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Random(t, false))
}
fn bin<N>(op: BinOp, l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Bin(op, Box::new(l), Box::new(r)))
}
fn add<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Add, l, r)
}
fn sub<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Sub, l, r)
}
fn mul<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Mul, l, r)
}
fn div<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Div, l, r)
}
fn pow<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Pow, l, r)
}
fn dot<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Dot, l, r)
}
fn rem<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Rem, l, r)
}
fn concat<N>(l: Spanned<Exp<N>>, r: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    bin(BinOp::Concat, l, r)
}
fn poly<N>(a: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Poly(Box::new(a)))
}
fn mle<N>(a: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Mle(Box::new(a)))
}
fn coef<N>(a: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Coef(Box::new(a)))
}
fn vec<N>(v: Vec<Spanned<Exp<N>>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Vec(Exps(v)))
}
fn map<N>(l: Spanned<Exp<N>>, x: Vid, range: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Map(Box::new(l), x, Box::new(range)))
}
fn reduce<N>(op: BinOp, a: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Reduce(op, Box::new(a)))
}
fn ram<N>(v: Spanned<Exp<N>>, i: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Ram(Box::new(v), Box::new(i)))
}
fn interpolate_at<N>(points: Spanned<Exp<N>>, evals: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Interpolate(Some(Box::new(points)), Box::new(evals)))
}
fn interpolate_grid<N>(evals: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Interpolate(None, Box::new(evals)))
}
fn evaluate_at<N>(p: Spanned<Exp<N>>, points: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Evaluate(Box::new(p), None, Some(Box::new(points))))
}
fn evaluate_grid<N>(p: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Evaluate(Box::new(p), None, None))
}
fn evaluate_selected<N>(
    range: Range<N>,
    p: Spanned<Exp<N>>,
    fixed: Spanned<Exp<N>>,
) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Evaluate(
        Box::new(p),
        Some(range),
        Some(Box::new(fixed)),
    ))
}
fn assert_eq<N>(lhs: Spanned<Exp<N>>, rhs: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Assert(Box::new(lhs), Box::new(rhs)))
}
fn verify_eq<N>(lhs: Spanned<Exp<N>>, rhs: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Verify(Box::new(lhs), Box::new(rhs)))
}
fn letx<N>(a: Vid, d: Spanned<Exp<N>>, e: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Let(Some(a), Box::new(d), Some(Box::new(e))))
}
fn logx<N>(a: Vid, d: Spanned<Exp<N>>, e: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Log(a, Box::new(d), Some(Box::new(e))))
}
fn seq<N>(a: Spanned<Exp<N>>, b: Spanned<Exp<N>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Let(None, Box::new(a), Some(Box::new(b))))
}
fn app<N>(id: Vid, args: Exps<N>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::App(id, args))
}
fn record<N>(fields: Ctx<String, Spanned<Exp<N>>>) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Record(fields))
}
fn proj<N>(exp: Spanned<Exp<N>>, field: String) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::Proj(Box::new(exp), field))
}
fn set_record<N>(
    record: Spanned<Exp<N>>,
    field: String,
    value: Spanned<Exp<N>>,
) -> Spanned<Exp<N>> {
    Spanned::dummy(Exp::SetRecord(Box::new(record), field, Box::new(value)))
}

/// Extension trait so `Spanned<CExp>` can call `.infer()` directly, delegating
/// to the inner `CExp`'s `Typeable` impl. This lets test-helper-constructed
/// expressions (which return `Spanned<Exp<N>>`) call `.infer()` without
/// manually unwrapping `.node` at every call site.
trait SpannedTypeable {
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
    ) -> Result<CTyp, TypeError>;
}

impl SpannedTypeable for Spanned<CExp> {
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
    ) -> Result<CTyp, TypeError> {
        self.node.infer(kctx, fctx, vctx)
    }
}

lazy_static! {
    static ref KIND_CTX: Ctx<Tid, CKind> = {
        let mut kctx = Ctx::new();
        // Add field type "F"
        kctx.insert(&Tid::from("F"), &Kind::Field);
        // Add group type "G"
        kctx.insert(&Tid::from("G"), &Kind::Group);
        // Add scalar type "S"
        kctx.insert(&Tid::from("S"), &Kind::scalar1("G"));
        kctx
    };

    static ref VAR_CTX: Ctx<Vid, CTyp> = {
        let mut vctx = Ctx::new();
        // Add variable "x" of type "F"
        vctx.insert(&Vid::from("f1"), &CTyp::Base(Tid::from("F")));
        // Add variable "y" of type "F"
        vctx.insert(&Vid::from("f2"), &CTyp::Base(Tid::from("F")));
        // Add vector variable "v1" with element type "F" and length 5
        vctx.insert(&Vid::from("v1"), &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 5));
        // Add vector variable "v2" with element type "F" and length 4
        vctx.insert(&Vid::from("v2"), &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 4));
        // Add variable "g" of type "G"
        vctx.insert(&Vid::from("g1"), &CTyp::Base(Tid::from("G")));
        // Add variable "g2" of type "G"
        vctx.insert(&Vid::from("g2"), &CTyp::Base(Tid::from("G")));
        // Add variable "s1" of type "S"
        vctx.insert(&Vid::from("s1"), &CTyp::Base(Tid::from("S")));
        // Add variable "s2" of type "S"
        vctx.insert(&Vid::from("s2"), &CTyp::Base(Tid::from("S")));
        // Add variable "p" of type "Uni<F, 5>"
        vctx.insert(&Vid::from("p"), &CTyp::Poly(Tid::from("F"), 1, 5));
        // Add variable "m" of type "Mle<F, 8>"
        vctx.insert(&Vid::from("m"), &CTyp::Poly(Tid::from("F"), 8, 1));
        vctx
    };
}

// Tests for literals
#[test]
fn test_literal_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create a literal expression "5"
    let lit = lit(5);

    // Run type inference
    assert_eq!(
        lit.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Fin(Range::singleton(5)))
    );
}

// Tests for binary operations
#[test]
fn test_binary_add_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression x + y
    let field_add = add(varstr("f1"), varstr("f2"));

    assert_eq!(
        field_add.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create expression g1 + g2
    let group_add = add(varstr("g1"), varstr("g2"));
    assert_eq!(
        group_add.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("G")))
    );

    // Create expression s1 + s2
    let mult_group_add = add(varstr("s1"), varstr("s2"));
    assert_eq!(
        mult_group_add.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("S")))
    );

    // Create expression v1 + v1
    let vec_add1 = add(varstr("v1"), varstr("v1"));
    assert_eq!(
        vec_add1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Vec(
            Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))),
            5
        ))
    );

    // Create expression v1 + v2
    let vec_add2 = add(varstr("v1"), varstr("v2"));
    assert!(vec_add2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test for subtraction
#[test]
fn test_binary_sub_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression x - y
    let field_sub = sub(varstr("f1"), varstr("f2"));

    assert_eq!(
        field_sub.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create expression g1 - g2
    let group_sub = sub(varstr("g1"), varstr("g2"));
    assert_eq!(
        group_sub.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("G")))
    );

    // Create expression s1 - s2
    let mult_group_sub = sub(varstr("s1"), varstr("s2"));
    assert_eq!(
        mult_group_sub.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("S")))
    );

    // Create expression v1 - v1
    let vec_sub1 = sub(varstr("v1"), varstr("v1"));
    assert_eq!(
        vec_sub1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Vec(
            Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))),
            5
        ))
    );

    // Create expression v1 - v2
    let vec_sub2 = sub(varstr("v1"), varstr("v2"));
    assert!(vec_sub2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test for multiplication
#[test]
fn test_binary_mul_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression x * y
    let field_mul = mul(varstr("f1"), varstr("f2"));

    assert_eq!(
        field_mul.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create expression g1 * g2
    let group_mul = mul(varstr("g1"), varstr("g2"));
    assert!(group_mul.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression s1 * s2
    let mult_group_mul = mul(varstr("s1"), varstr("s2"));
    assert_eq!(
        mult_group_mul.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("S")))
    );

    // Create expression v1 * v1
    let vec_mul1 = mul(varstr("v1"), varstr("v1"));
    assert_eq!(
        vec_mul1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Vec(
            Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))),
            5
        ))
    );

    // Create expression v1 * v2
    let vec_mul2 = mul(varstr("v1"), varstr("v2"));
    assert!(vec_mul2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test for division
#[test]
fn test_binary_div_inference() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    vctx.insert(&Vid::from("pc"), &CTyp::Poly(Tid::from("F"), 1, 0));

    // Create expression x / y
    let field_div = div(varstr("f1"), varstr("f2"));

    assert_eq!(
        field_div.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create expression g1 / g2
    let group_div = div(varstr("g1"), varstr("g2"));
    assert!(group_div.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression s1 / s2
    let mult_group_div = div(varstr("s1"), varstr("s2"));
    assert_eq!(
        mult_group_div.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("S")))
    );

    // Create expression v1 / v1
    let vec_div1 = div(varstr("v1"), varstr("v1"));
    assert_eq!(
        vec_div1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Vec(
            Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))),
            5
        ))
    );

    // Create expression v1 / v2
    let vec_div2 = div(varstr("v1"), varstr("v2"));
    assert!(vec_div2.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Base(F) / Poly<F,1,0> is not a source-typed division door.
    let scalar_div_constant_poly = div(varstr("f1"), varstr("pc"));
    assert!(
        scalar_div_constant_poly
            .infer(&KIND_CTX, &fctx, &vctx)
            .is_err(),
        "Base(F) / Poly<F,1,0> must be rejected"
    );

    // Base(F) / nonconstant Poly is likewise rejected.
    let scalar_div_nonconstant_poly = div(varstr("f1"), varstr("p"));
    assert!(
        scalar_div_nonconstant_poly
            .infer(&KIND_CTX, &fctx, &vctx)
            .is_err(),
        "Base(F) / nonconstant Poly must be rejected"
    );

    // Poly / scalar remains accepted.
    let poly_div_scalar = div(varstr("p"), varstr("f1"));
    assert_eq!(
        poly_div_scalar.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 1, 5))
    );

    // Create expression p / p; Poly / Poly remains accepted.
    let uni_div = div(varstr("p"), varstr("p"));
    assert_eq!(
        uni_div.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 1, 0))
    );
}

// Test for remainder
#[test]
fn test_binary_rem_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression x % y
    let field_rem = rem(varstr("f1"), varstr("f2"));

    // fields have no modulo
    assert!(field_rem.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression g1 % g2, groups have no modulo
    let group_rem = rem(varstr("g1"), varstr("g2"));
    assert!(group_rem.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression s1 % s2
    let mult_group_rem = rem(varstr("s1"), varstr("s2"));
    assert!(mult_group_rem.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression p % p
    let uni_rem = rem(varstr("p"), varstr("p"));
    assert_eq!(
        uni_rem.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 1, 4))
    );
}

// Test for power
#[test]
fn test_binary_pow_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression x ^ y
    let field_pow = pow(varstr("f1"), lit(2));

    assert_eq!(
        field_pow.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create expression g1 ^ g2
    let group_pow = pow(varstr("g1"), varstr("g2"));
    assert!(group_pow.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression s1 ^ s2
    let mult_group_pow1 = pow(varstr("s1"), lit(2));
    assert_eq!(
        mult_group_pow1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("S")))
    );

    // Create expression s1 ^ f1
    let mult_group_pow1 = pow(varstr("s1"), varstr("f1"));
    assert!(mult_group_pow1.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression v1 ^ v1
    let vec_pow1 = pow(varstr("v1"), vec(vec![lit(1); 5]));
    assert_eq!(
        vec_pow1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::varstr("F"), 5))
    );

    // Create expression v1 ^ v2
    let vec_pow2 = pow(varstr("v1"), varstr("v2"));
    assert!(vec_pow2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test for dot product
#[test]
fn test_binary_dot_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression x . y
    let field_dot = dot(varstr("f1"), varstr("f2"));
    // Only vectors and polynomials can be dotted
    assert!(field_dot.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression g1 . g2
    let group_dot = dot(varstr("g1"), varstr("g2"));
    assert!(group_dot.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression s1 . s2
    let mult_group_dot = dot(varstr("s1"), varstr("s2"));
    assert!(mult_group_dot.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Create expression v1 . v1
    let vec_dot1 = dot(varstr("v1"), varstr("v1"));
    assert_eq!(
        vec_dot1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create expression v1 . v2
    let vec_dot2 = dot(varstr("v1"), varstr("v2"));
    assert!(vec_dot2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test for concatenation
#[test]
fn test_binary_concat_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create expression v1 ++ v2
    let vec_concat = concat(varstr("v1"), varstr("v2"));

    assert_eq!(
        vec_concat.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::varstr("F"), 9))
    );

    // Create expression v1 ++ f1
    let fv1_concat = concat(varstr("v1"), varstr("f1"));

    assert_eq!(
        fv1_concat.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::varstr("F"), 6))
    );

    // Create expression f2 ++ v1
    let fv2_concat = concat(varstr("f2"), varstr("v2"));
    assert_eq!(
        fv2_concat.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::varstr("F"), 5))
    );
}

// Test for vector creation
#[test]
fn test_vector_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create a vector expression [1, 2, 3]
    let lit_vec = vec(vec![lit(1), lit(2), lit(3)]);
    assert_eq!(
        lit_vec.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::Fin(CRange::from_raw(1, 1, 4)), 3,))
    );

    // Create a vector expression [1, f1, 3]
    let lit_vec2 = vec(vec![lit(1), varstr("f1"), lit(3)]);
    assert_eq!(
        lit_vec2.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::varstr("F"), 3))
    );

    // Create a vector expression [1, f1, g1]
    let lit_vec_bad = vec(vec![lit(1), varstr("f1"), varstr("g1")]);
    assert!(lit_vec_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test for error: empty vector
#[test]
fn test_empty_vector_error() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create an empty vector expression []
    let empty = vec(vec![]);

    assert!(empty.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test interpolate — mixed-element-type rejection (shape sweeps cover accept/reject by length).
#[test]
fn test_interpolate() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Mixed-element-type vector is rejected (F and G are incompatible).
    let interp_bad = interpolate_grid(vec(vec![varstr("f1"), varstr("g1")]));
    assert!(interp_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // Lagrange interpolation with empty range (length 0) must be rejected, not panic.
    let interp_empty = interpolate_at(
        range(CRange::from_raw(0, 1, 0)),
        range(CRange::from_raw(0, 1, 0)),
    );
    let res = interp_empty.infer(&KIND_CTX, &fctx, &vctx);
    assert!(res.is_err());
}

// Test poly — mixed-element-type rejection (shape sweeps cover all accept cases).
#[test]
fn test_poly() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Mixed-element-type vector is rejected (F and G are incompatible).
    let interp_bad = poly(vec(vec![varstr("f1"), varstr("g1")]));
    assert!(interp_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

// Test coef . interpolate_grid roundtrip (Phase 14 m+1 convention)
#[test]
fn test_fft() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // interpolate_grid([f1, 2, 3, 4]) yields Poly<F, 1, 3>: n=4 evaluations
    // uniquely determine a polynomial of max degree 3 (4 coefficients
    // under the m+1 convention). coef(Poly<F, 1, 3>) then yields [F; 4].
    let eval1 = coef(interpolate_grid(vec(vec![
        varstr("f1"),
        lit(2),
        lit(3),
        lit(4),
    ])));

    assert_eq!(
        eval1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), 4))
    );

    let eval_bad = evaluate_grid(vec(vec![varstr("f1")]));

    assert!(eval_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_phase14_coef_poly_roundtrip() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // For every k in {1, 2, 3, 5, 7}: coef(poly(v : [F; k])) : [F; k].
    for k in [1usize, 2, 3, 5, 7] {
        let v = vec((0..k).map(|_| varstr("f1")).collect());
        let e = coef(poly(v));
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), k)),
            "roundtrip failed for k = {k}"
        );
    }
}

// Test for function application
#[test]
fn test_app() {
    let fctx = Set::singleton(Sig {
        name: Spanned::dummy(Vid::from("fun")),
        typevars: Spanned::dummy(TypeVars::from([
            Spanned::dummy(TypeVar::new_str("F", Kind::Field)),
            Spanned::dummy(TypeVar::new_str("G", Kind::Group)),
        ])),
        args: Spanned::dummy(Args::from([
            Spanned::dummy(CArg::instance("a", CTyp::Base(Tid::from("F")))),
            Spanned::dummy(CArg::instance("b", CTyp::Base(Tid::from("F")))),
            Spanned::dummy(CArg::instance("c", CTyp::Base(Tid::from("G")))),
        ])),
        ret: Some(Spanned::dummy(CTyp::Base(Tid::from("G")))),
    });

    let vctx = VAR_CTX.clone();

    // Create a function application fun(2, f1, g1)
    let app1 = app(
        "fun".into(),
        Exps::from([lit(2), varstr("f1"), varstr("g1")]),
    );

    assert!(app1.infer(&KIND_CTX, &Set::new(), &vctx).is_err());
    assert_eq!(
        app1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("G")))
    );

    // Create a function application fun(1, 2)
    let app2 = app("fun".into(), Exps::from([lit(1), lit(2)]));
    assert!(app2.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // A polynomial application to scalar
    let uni_app = app("p".into(), Exps::from([lit(1)]));
    assert_eq!(
        uni_app.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    let uni_app_vec = app("p".into(), Exps::from([varstr("v1")]));
    assert!(uni_app_vec.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // A MLE application to scalar and vector of scalars
    let mle_app = app("m".into(), Exps::from([lit(1)]));
    assert_eq!(
        mle_app.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 7, 1))
    );

    let mle_app_vec = app("m".into(), Exps::from([varstr("v1")]));
    assert_eq!(
        mle_app_vec.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 3, 1))
    );
}

// Test for random access
#[test]
fn test_ram() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Create a random access expression v1[2]
    let ram1 = ram(varstr("v1"), lit(2));

    assert_eq!(
        ram1.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    // Create a random access expression v1[0..4]
    let ram2 = ram(varstr("v1"), range(CRange::from_raw(0, 1, 4)));

    assert_eq!(
        ram2.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), 4))
    );
}

// ----------------------------------------------------------------------
// Phase-14 m+1 convention regressions for CExp::infer() on polynomial
// expressions. These pin observable shapes so any drift between the
// declared "max-degree m" parameter and the implied "m+1 coefficients"
// length is caught at the type-inference layer.
// ----------------------------------------------------------------------

/// `poly([F; k])` produces `Poly<F, 1, k - 1>` for every legal `k ≥ 1`
/// under the m+1 convention.
#[test]
fn test_phase14_poly_shape_sweep() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    for k in [1usize, 2, 3, 4, 5] {
        let v = vec((0..k).map(|_| varstr("f1")).collect());
        let e = poly(v);
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, k - 1)),
            "poly([F; {k}]) should yield Poly<F, 1, {}>",
            k - 1,
        );
    }
}

/// `coef(p : Poly<F, 1, m>)` produces a vector of `m + 1` field elements
/// for every legal `m`.
#[test]
fn test_phase14_coef_shape_sweep() {
    let fctx = Set::new();

    for m in [0usize, 1, 2, 3, 4, 7] {
        let mut vctx = VAR_CTX.clone();
        let pname = format!("p_{m}");
        vctx.insert(
            &Vid::from(pname.as_str()),
            &CTyp::Poly(Tid::from("F"), 1, m),
        );
        let e = coef(varstr(pname.as_str()));
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), m + 1)),
            "coef(Poly<F, 1, {m}>) should yield [F; {}]",
            m + 1,
        );
    }
}

/// `mle([F; 2^n])` produces `Mle<F, n>` for every legal `n`. The MLE
/// length is the evaluation-vector length (2^n), so the "n vs n+1"
/// distinction here is whether the bound is on the *number of variables*
/// or on the *number of evaluations*. Pin the variable count.
#[test]
fn test_phase14_mle_pow2_sweep() {
    let fctx = Set::new();

    for n in 0usize..=4 {
        let len = 1usize << n;
        let mut vctx = VAR_CTX.clone();
        let vname = format!("vec_{len}");
        vctx.insert(
            &Vid::from(vname.as_str()),
            &CTyp::vec(&CTyp::Base(Tid::from("F")), len),
        );
        let e = mle(varstr(vname.as_str()));
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), n, 1)),
            "mle([F; {len}]) should yield Mle<F, {n}>",
        );
    }
}

/// `mle([F; k])` for non-power-of-two `k` is rejected by infer.
#[test]
fn test_phase14_mle_rejects_non_pow2_sweep() {
    let fctx = Set::new();

    for k in [3usize, 5, 6, 7] {
        let mut vctx = VAR_CTX.clone();
        let vname = format!("vec_{k}");
        vctx.insert(
            &Vid::from(vname.as_str()),
            &CTyp::vec(&CTyp::Base(Tid::from("F")), k),
        );
        let e = mle(varstr(vname.as_str()));
        let result = e.infer(&KIND_CTX, &fctx, &vctx);
        assert!(
            matches!(result, Err(TypeError::Mle(_, _, _))),
            "mle([F; {k}]) (non-pow2) must be rejected with TypeError::Mle. \
                 Got: {result:?}",
        );
    }
}

/// Unary `eval(p)` (FFT-grid evaluation) accepts `Poly<F, 1, m>` iff
/// `(m + 1).is_power_of_two()` — i.e., the *coefficient count* is pow2,
/// not the max degree. Sweeps both accept and reject cases.
#[test]
fn test_phase14_evaluate_grid_accept_sweep() {
    let fctx = Set::new();

    // m+1 is power of two: 1, 2, 4, 8.
    for m in [0usize, 1, 3, 7] {
        let mut vctx = VAR_CTX.clone();
        let pname = format!("p_{m}");
        vctx.insert(
            &Vid::from(pname.as_str()),
            &CTyp::Poly(Tid::from("F"), 1, m),
        );
        let e = evaluate_grid(varstr(pname.as_str()));
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), m + 1)),
            "eval(Poly<F, 1, {m}>) has {} coefficients (pow2); infer() \
                 must accept and return [F; {}]",
            m + 1,
            m + 1,
        );
    }
}

#[test]
fn test_phase14_evaluate_grid_reject_sweep() {
    let fctx = Set::new();

    // m+1 not power of two: 3, 5, 6.
    for m in [2usize, 4, 5] {
        let mut vctx = VAR_CTX.clone();
        let pname = format!("p_{m}");
        vctx.insert(
            &Vid::from(pname.as_str()),
            &CTyp::Poly(Tid::from("F"), 1, m),
        );
        let e = evaluate_grid(varstr(pname.as_str()));
        let result = e.infer(&KIND_CTX, &fctx, &vctx);
        assert!(
            matches!(result, Err(TypeError::EvaluateGridNotPow2(_, _, _, _, _))),
            "eval(Poly<F, 1, {m}>) has {} coefficients (not pow2); infer() \
                 must reject with EvaluateGridNotPow2. Got: {result:?}",
            m + 1,
        );
    }
}

/// Unary `interpolate(evals)` accepts only pow2-length input and returns
/// `Poly<F, 1, n - 1>` (n evaluations → max degree n-1, n coefficients).
#[test]
fn test_phase14_interpolate_unary_accept_sweep() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    for n in [1usize, 2, 4, 8] {
        let v = vec((0..n).map(|_| varstr("f1")).collect());
        let e = interpolate_grid(v);
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, n - 1)),
            "interpolate([F; {n}]) should yield Poly<F, 1, {}>",
            n - 1,
        );
    }
}

#[test]
fn test_phase14_interpolate_unary_reject_sweep() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Non-pow2 lengths must be rejected with InterpolateUnaryNotPow2.
    for n in [3usize, 5, 7] {
        let v = vec((0..n).map(|_| varstr("f1")).collect());
        let e = interpolate_grid(v);
        let result = e.infer(&KIND_CTX, &fctx, &vctx);
        assert!(
            matches!(result, Err(TypeError::InterpolateUnaryNotPow2(_, _, _, _))),
            "interpolate([F; {n}]) (non-pow2) must be rejected with \
                 InterpolateUnaryNotPow2. Got: {result:?}",
        );
    }
}

/// Binary `interpolate(points, evals)` is Lagrange interpolation: no
/// power-of-two constraint, just `|points| == |evals| = n`. Returns
/// `Poly<F, 1, n - 1>`.
#[test]
fn test_phase14_interpolate_binary_shape_sweep() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    for n in [1usize, 2, 3, 4, 5] {
        let pts = vec((0..n).map(|_| varstr("f1")).collect());
        let evs = vec((0..n).map(|_| varstr("f2")).collect());
        let e = interpolate_at(pts, evs);
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Poly(Tid::from("F"), 1, n - 1)),
            "interpolate(pts: [F; {n}], evs: [F; {n}]) should yield \
                 Poly<F, 1, {}>",
            n - 1,
        );
    }
}

/// Random-access into the coefficient vector of a univariate polynomial. Under the m+1 convention,
/// `Poly<F, 1, m>` has m+1 coefficients indexed 0..m+1. The previous
/// code rejected the legal upper-boundary index `m` because it tested
/// `r.end <= m` instead of `r.end <= m + 1`. This is the off-by-one
/// this PR fixes (`CExp::Ram` scalar-index arm and vector-index arm).
#[test]
fn test_phase14_ram_uni_scalar_index_boundary() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    // p3 : Poly<F, 1, 3>  --  max degree 3, 4 coefficients (indices 0..4).
    vctx.insert(&Vid::from("p3"), &CTyp::Poly(Tid::from("F"), 1, 3));

    // Indexing at 0, 1, 2 was already accepted under the old bound.
    for i in 0usize..=2 {
        let e = ram(coef(varstr("p3")), lit(i));
        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(CTyp::Base(Tid::from("F"))),
            "coef(p3)[{i}] must typecheck",
        );
    }

    // The boundary case `p3[3]` is the regression: it was rejected by
    // the old `r.end <= n` check (r.end = 4 > n = 3), but must be
    // accepted under the m+1 convention (r.end = 4 <= n + 1 = 4).
    let e_boundary = ram(coef(varstr("p3")), lit(3));
    assert_eq!(
        e_boundary.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F"))),
        "coef(p3)[3] is the highest legal coefficient index and must typecheck",
    );

    // True overflow: index 4 is out of bounds (only 4 coefficients exist).
    let e_overflow = ram(coef(varstr("p3")), lit(4));
    assert!(
        matches!(
            e_overflow.infer(&KIND_CTX, &fctx, &vctx),
            Err(TypeError::Ram(_, _, _, _, _, _))
        ),
        "coef(p3)[4] is out of bounds (only 4 coefficients) and must be rejected",
    );
}

/// Vector-index variant of `CExp::Ram` on the coefficient vector of a univariate polynomial. Must
/// behave the same as the scalar-index variant: the legal upper bound
/// on the index range is `n + 1` (the coefficient count), not `n`.
#[test]
fn test_phase14_ram_uni_vector_index_boundary() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    vctx.insert(&Vid::from("p3"), &CTyp::Poly(Tid::from("F"), 1, 3));

    // Slicing all 4 coefficient indices (range 0..4) must typecheck under
    // the m+1 convention (r.end = 4 <= n + 1 = 4). Was rejected before.
    let e_boundary = ram(coef(varstr("p3")), range(CRange::from_raw(0, 1, 4)));
    let boundary_result = e_boundary.infer(&KIND_CTX, &fctx, &vctx);
    assert!(
        boundary_result.is_ok(),
        "coef(p3)[0..4] is the maximal legal slice and must typecheck. Got: {boundary_result:?}",
    );

    // True overflow: range 0..5 reaches index 4, which is past the last
    // coefficient (index 3); must be rejected.
    let e_overflow = ram(coef(varstr("p3")), range(CRange::from_raw(0, 1, 5)));
    assert!(
        matches!(
            e_overflow.infer(&KIND_CTX, &fctx, &vctx),
            Err(TypeError::Ram(_, _, _, _, _, _))
        ),
        "coef(p3)[0..5] reaches an out-of-bounds index and must be rejected",
    );
}

/// `CExp::Map(f, v : [Poly<F, 1, 3>; 4])` over a vector of polynomials.
/// The result vector's element type is whatever the inner expression
/// `f` returns when the bound variable has the per-element type
/// (`Poly<F, 1, 3>` here). Pin two cases:
///   - `f = x` (identity)    → result `[Poly<F, 1, 3>; 4]`
///   - `f = coef(x)[0]`      → result `[F; 4]`
///
/// (`coef(Poly<F, 1, 3>)` yields `[F; 4]`, and `[F; 4][0] : F`.)
#[test]
fn test_phase14_map_over_poly_vector() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    // pv : [Poly<F, 1, 3>; 4]
    let poly_t = CTyp::Poly(Tid::from("F"), 1, 3);
    vctx.insert(&Vid::from("pv"), &CTyp::vec(&poly_t, 4));

    // map x in pv => x       -- the result element type matches the
    //                          binder type Poly<F, 1, 3>.
    let map_id = map(varstr("x"), Vid::from("x"), varstr("pv"));
    assert_eq!(
        map_id.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&poly_t, 4)),
        "map x => x over [Poly<F, 1, 3>; 4] preserves the element type",
    );

    // map x in pv => coef(x)[0]  -- result element type is F.
    let coef_zero = ram(coef(varstr("x")), lit(0));
    let map_coef = map(coef_zero, Vid::from("x"), varstr("pv"));
    assert_eq!(
        map_coef.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::vec(&CTyp::Base(Tid::from("F")), 4)),
        "map x => coef(x)[0] over [Poly<F, 1, 3>; 4] yields [F; 4]",
    );
}

/// `CExp::Reduce(BinOp::Add, v : [Poly<F, 1, 3>; 4])` — summing a vector
/// of equal-shaped polynomials preserves the polynomial shape via
/// `lub_op(Add, Poly, Poly)`. Pin the result as `Poly<F, 1, 3>`.
#[test]
fn test_phase14_reduce_add_over_poly_vector() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    let poly_t = CTyp::Poly(Tid::from("F"), 1, 3);
    vctx.insert(&Vid::from("pv"), &CTyp::vec(&poly_t, 4));

    let e = reduce(BinOp::Add, varstr("pv"));
    assert_eq!(
        e.infer(&KIND_CTX, &fctx, &vctx),
        Ok(poly_t),
        "reduce(+, [Poly<F, 1, 3>; 4]) must yield Poly<F, 1, 3>",
    );
}

/// `reduce(dot, [Vec(F,2); 3])` must be rejected: dot produces a scalar F,
/// but F is not a valid left operand for dot with Vec(F,2).
#[test]
fn test_reduce_dot_nested_vec_rejected() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    let vec_t = CTyp::vec(&CTyp::Base(Tid::from("F")), 2);
    vctx.insert(&Vid::from("vv"), &CTyp::vec(&vec_t, 3));

    let e = reduce(BinOp::Dot, varstr("vv"));
    let result = e.infer(&KIND_CTX, &fctx, &vctx);
    assert!(
            result.is_err(),
            "reduce(dot, [Vec(F,2); 3]) should be rejected — dot produces F, but F . Vec(F,2) is ill-typed; got {:?}",
            result
        );
}

#[test]
fn test_reduce_mul_poly_invalid_coeff_kind() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    // Poly with group coefficients G
    let poly_t = CTyp::Poly(Tid::from("G"), 1, 3);
    vctx.insert(&Vid::from("pv_g"), &CTyp::vec(&poly_t, 4));

    let e = reduce(BinOp::Mul, varstr("pv_g"));
    // This must fail because group types cannot be multiplied
    assert!(e.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_reduce_mul_poly_overflow() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    // Poly with field coefficients F but extremely large degree to trigger overflow
    let poly_t = CTyp::Poly(Tid::from("F"), 1, usize::MAX / 2);
    vctx.insert(&Vid::from("pv_overflow"), &CTyp::vec(&poly_t, 4));

    let e = reduce(BinOp::Mul, varstr("pv_overflow"));
    // This must fail because of degree overflow
    assert!(e.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

/// Property-based test to verify the correctness of type inference for
/// `reduce(*, vector_of_polys)`. It verifies that the degree of the
/// product polynomial matches `degree * vector_len`.
#[test]
fn test_reduce_mul_poly_pbt() {
    let fctx = Set::new();

    arbtest::arbtest(|u| {
        let num_vars = u.int_in_range(1..=4)?;
        let degree = u.int_in_range(0..=4)?;
        let vector_len = u.int_in_range(1..=4)?;

        let poly_t = CTyp::Poly(Tid::from("F"), num_vars, degree);
        let vec_poly_t = CTyp::vec(&poly_t, vector_len);

        let mut vctx = Ctx::new();
        vctx.insert(&Vid::from("pv"), &vec_poly_t);

        let e = reduce(BinOp::Mul, varstr("pv"));
        let expected_deg = degree * vector_len;
        let expected_t = CTyp::Poly(Tid::from("F"), num_vars, expected_deg);

        assert_eq!(
            e.infer(&KIND_CTX, &fctx, &vctx),
            Ok(expected_t),
            "reduce(*, [Poly<F, {}, {}>; {}]) should yield Poly<F, {}, {}>",
            num_vars,
            degree,
            vector_len,
            num_vars,
            expected_deg
        );
        Ok(())
    });
}

#[test]
fn test_record_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    let mut fields = Ctx::new();
    fields.insert(&"x".to_string(), &lit(1));
    fields.insert(&"y".to_string(), &varstr("f1"));
    let record_exp = record(fields);

    let mut expected_fields = Ctx::new();
    expected_fields.insert(
        &"x".to_string(),
        &Spanned::dummy(CTyp::Fin(Range::singleton(1))),
    );
    expected_fields.insert(
        &"y".to_string(),
        &Spanned::dummy(CTyp::Base(Tid::from("F"))),
    );
    let expected_typ = CTyp::Record(expected_fields);

    assert_eq!(record_exp.infer(&KIND_CTX, &fctx, &vctx), Ok(expected_typ));
}

#[test]
fn test_proj_inference() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();

    let mut fields = Ctx::new();
    fields.insert(
        &"x".to_string(),
        &Spanned::dummy(CTyp::Base(Tid::from("F"))),
    );
    vctx.insert(&Vid::from("r"), &CTyp::Record(fields));

    let proj_exp = proj(varstr("r"), "x".to_string());
    assert_eq!(
        proj_exp.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );

    let proj_bad = proj(varstr("r"), "y".to_string());
    assert!(proj_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_set_record_inference() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();

    let mut fields = Ctx::new();
    fields.insert(
        &"x".to_string(),
        &Spanned::dummy(CTyp::Base(Tid::from("F"))),
    );
    vctx.insert(&Vid::from("r"), &CTyp::Record(fields));

    let set_exp = set_record(varstr("r"), "x".to_string(), varstr("f2"));

    let mut expected_fields = Ctx::new();
    expected_fields.insert(
        &"x".to_string(),
        &Spanned::dummy(CTyp::Base(Tid::from("F"))),
    );
    let expected_typ = CTyp::Record(expected_fields);

    assert_eq!(set_exp.infer(&KIND_CTX, &fctx, &vctx), Ok(expected_typ));
}

#[test]
fn test_let_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    let let_exp = letx(Vid::from("x"), varstr("f1"), add(varstr("x"), varstr("f2")));

    assert_eq!(
        let_exp.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );
}

#[test]
fn test_log_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    let log_exp = logx(Vid::from("x"), varstr("f1"), add(varstr("x"), varstr("f2")));

    assert_eq!(
        log_exp.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );
}

#[test]
fn test_assert_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // assert_eq returns Unit
    let assert_exp = assert_eq(varstr("f1"), varstr("f2"));

    assert_eq!(assert_exp.infer(&KIND_CTX, &fctx, &vctx), Ok(CTyp::Unit));

    // assert_eq with mismatched operand types should fail
    let assert_bad = assert_eq(varstr("f1"), varstr("g1"));
    assert!(assert_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // seq(assert, cont) returns cont's type
    let seq_exp = seq(assert_eq(varstr("f1"), varstr("f2")), varstr("f1"));
    assert_eq!(
        seq_exp.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );
}

#[test]
fn test_verify_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // verify_eq returns Unit
    let verify_exp = verify_eq(varstr("f1"), varstr("f2"));

    assert_eq!(verify_exp.infer(&KIND_CTX, &fctx, &vctx), Ok(CTyp::Unit));

    // verify_eq with mismatched operand types should fail
    let verify_bad = verify_eq(varstr("f1"), varstr("g1"));
    assert!(verify_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // seq(verify, cont) returns cont's type
    let seq_exp = seq(verify_eq(varstr("f1"), varstr("f2")), varstr("f1"));
    assert_eq!(
        seq_exp.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );
}

#[test]
fn test_record_nested_inference() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // {| a: {| b: 1 |}, c: f1 |}
    let mut inner_fields = Ctx::new();
    inner_fields.insert(&"b".to_string(), &lit(1));

    let mut fields = Ctx::new();
    fields.insert(&"a".to_string(), &record(inner_fields));
    fields.insert(&"c".to_string(), &varstr("f1"));

    let record_exp = record(fields);

    let mut expected_inner = Ctx::new();
    expected_inner.insert(
        &"b".to_string(),
        &Spanned::dummy(CTyp::Fin(Range::singleton(1))),
    );

    let mut expected_fields = Ctx::new();
    expected_fields.insert(
        &"a".to_string(),
        &Spanned::dummy(CTyp::Record(expected_inner)),
    );
    expected_fields.insert(
        &"c".to_string(),
        &Spanned::dummy(CTyp::Base(Tid::from("F"))),
    );
    let expected_typ = CTyp::Record(expected_fields);

    assert_eq!(record_exp.infer(&KIND_CTX, &fctx, &vctx), Ok(expected_typ));
}

#[test]
fn test_record_set_type_mismatch() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();

    let mut fields = Ctx::new();
    fields.insert(
        &"x".to_string(),
        &Spanned::dummy(CTyp::Base(Tid::from("F"))),
    );
    vctx.insert(&Vid::from("r"), &CTyp::Record(fields));

    // setting x to g1 (G type, mismatch with F) should fail
    let set_bad = set_record(varstr("r"), "x".to_string(), varstr("g1"));
    assert!(set_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_record_proj_non_record() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // Projecting from a non-record (e.g. f1.x) should fail
    let proj_bad = proj(varstr("f1"), "x".to_string());
    assert!(proj_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_mle_typecheck_rejection() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // mle on empty vector (size 0) should fail typecheck (not panic!)
    let mle_empty = mle(vec(vec![]));
    assert!(mle_empty.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // mle on non-power-of-two size vector (size 3) should fail typecheck
    let mle_non_pow2 = mle(vec(vec![varstr("f1"), varstr("f1"), varstr("f1")]));
    assert!(mle_non_pow2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_mle_eval_inference() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();

    // Add variable "m3" of type Mle<F, 3> -> Poly(F, 3, 1)
    vctx.insert(&Vid::from("m3"), &CTyp::Poly(Tid::from("F"), 3, 1));
    // Add variable "v3" of type [F; 3]
    vctx.insert(
        &Vid::from("v3"),
        &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 3),
    );
    // Add variable "v2" of type [F; 2]
    vctx.insert(
        &Vid::from("v2"),
        &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 2),
    );

    // eval(m3, v2) -> Mle<F, 1> -> Poly(F, 1, 1)
    let eval_v2 = evaluate_at(varstr("m3"), varstr("v2"));
    assert_eq!(
        eval_v2.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 1, 1))
    );

    // eval(m3, v3) -> F -> Base(F)
    let eval_v3 = evaluate_at(varstr("m3"), varstr("v3"));
    assert_eq!(
        eval_v3.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );
}

#[test]
fn test_mle_eval_out_of_bounds() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();

    vctx.insert(&Vid::from("m3"), &CTyp::Poly(Tid::from("F"), 3, 1));
    // v1 has length 5, which is > 3
    let eval_bad = evaluate_at(varstr("m3"), varstr("v1"));
    assert!(eval_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_eval_univariate_vector_rejected() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // eval(p, v1): a univariate Poly<F,1,_> at a vector of points is a hard
    // type error (evaluate at a single scalar via p(x), or comprehend with
    // [p(x) for x in points]).
    let banned = evaluate_at(varstr("p"), varstr("v1"));
    assert!(
        matches!(
            banned.infer(&KIND_CTX, &fctx, &vctx),
            Err(TypeError::EvaluateUnivariateVector(_, _, _, _))
        ),
        "eval(Poly<F,1,_>, [F; k]) must be rejected with EvaluateUnivariateVector, got {:?}",
        banned.infer(&KIND_CTX, &fctx, &vctx)
    );

    // eval(p, f1): a univariate poly at a single scalar still yields a scalar.
    let scalar_eval = evaluate_at(varstr("p"), varstr("f1"));
    assert_eq!(
        scalar_eval.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("F")))
    );
}

#[test]
fn test_selected_eval_inference() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    vctx.insert(&Vid::from("m3"), &CTyp::Poly(Tid::from("F"), 3, 4));
    vctx.insert(
        &Vid::from("fixed1"),
        &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 1),
    );
    vctx.insert(
        &Vid::from("fixed2"),
        &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 2),
    );

    let unit = evaluate_selected(Range::singleton(1), varstr("m3"), varstr("fixed2"));
    assert_eq!(
        unit.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 1, 4))
    );

    let normalized_unit =
        evaluate_selected(CRange::from_raw(1, 1, 2), varstr("m3"), varstr("fixed2"));
    assert_eq!(
        normalized_unit.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 1, 4))
    );

    let wide_range = evaluate_selected(CRange::from_raw(1, 1, 3), varstr("m3"), varstr("fixed1"));
    assert_eq!(
        wide_range.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Poly(Tid::from("F"), 2, 4))
    );
}

#[test]
fn test_selected_eval_rejects_invalid_ranges_and_arity() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();
    vctx.insert(&Vid::from("m3"), &CTyp::Poly(Tid::from("F"), 3, 4));
    vctx.insert(
        &Vid::from("fixed2"),
        &CTyp::Vec(Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))), 2),
    );

    let empty = evaluate_selected(CRange::from_raw(1, 1, 1), varstr("m3"), varstr("fixed2"));
    assert!(empty.infer(&KIND_CTX, &fctx, &vctx).is_err());

    let out_of_bounds =
        evaluate_selected(CRange::from_raw(2, 1, 4), varstr("m3"), varstr("fixed2"));
    assert!(out_of_bounds.infer(&KIND_CTX, &fctx, &vctx).is_err());

    let wrong_arity = evaluate_selected(Range::singleton(1), varstr("m3"), varstr("v1"));
    assert!(wrong_arity.infer(&KIND_CTX, &fctx, &vctx).is_err());

    let wide_wrong_arity =
        evaluate_selected(CRange::from_raw(1, 1, 3), varstr("m3"), varstr("fixed2"));
    assert!(wide_wrong_arity.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_let_shadowing() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // let x = f1; let x = g1; x -- should return type G
    let let_shadow = letx(
        Vid::from("x"),
        varstr("f1"),
        letx(Vid::from("x"), varstr("g1"), varstr("x")),
    );

    assert_eq!(
        let_shadow.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Base(Tid::from("G")))
    );
}

#[test]
fn test_mle_eval_pbt() {
    let fctx = Set::new();
    arbtest::arbtest(|u| {
        let num_vars = u.int_in_range(2..=10)?;
        let eval_len = u.int_in_range(1..=num_vars)?;

        let mle_t = CTyp::Poly(Tid::from("F"), num_vars, 1);
        let vec_t = CTyp::Vec(
            Box::new(Spanned::dummy(CTyp::Base(Tid::from("F")))),
            eval_len,
        );

        let mut vctx = VAR_CTX.clone();
        vctx.insert(&Vid::from("m_rand"), &mle_t);
        vctx.insert(&Vid::from("v_rand"), &vec_t);

        let e = evaluate_at(varstr("m_rand"), varstr("v_rand"));
        let res = e.infer(&KIND_CTX, &fctx, &vctx);

        if eval_len == num_vars {
            assert_eq!(
                res,
                Ok(CTyp::Base(Tid::from("F"))),
                "evaluating MLE with all variables should yield base type"
            );
        } else {
            assert_eq!(
                res,
                Ok(CTyp::Poly(Tid::from("F"), num_vars - eval_len, 1)),
                "evaluating MLE with M variables should yield MLE with N-M variables"
            );
        }
        Ok(())
    });
}

#[test]
fn test_range_rejection() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // start > end
    let bad_range1 = CExp::Range(CRange::from_raw(5, 1, 1));
    assert!(bad_range1.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // step == 0
    let bad_range2 = CExp::Range(CRange::from_raw(0, 0, 5));
    assert!(bad_range2.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // step does not cleanly divide distance
    let bad_range3 = CExp::Range(CRange::from_raw(0, 3, 5));
    assert!(bad_range3.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_map_rejection() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // mapping over f1 (which is field element, not vector/range) should fail
    let map_bad = map(varstr("x"), Vid::from("x"), varstr("f1"));
    assert!(map_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_poly_rejection() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // poly on non-vector should fail
    let poly_bad1 = poly(varstr("f1"));
    assert!(poly_bad1.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // poly on empty vector should fail
    let poly_bad2 = poly(vec(vec![]));
    assert!(poly_bad2.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_coef_rejection() {
    let fctx = Set::new();
    let mut vctx = VAR_CTX.clone();

    // coef on non-polynomial should fail
    let coef_bad1 = coef(varstr("f1"));
    assert!(coef_bad1.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // coef on multivariate polynomial (MLE) with too many variables to shift (e.g. 128) should fail typecheck (not panic)
    vctx.insert(&Vid::from("m_large"), &CTyp::Poly(Tid::from("F"), 128, 1));
    let coef_overflow = coef(varstr("m_large"));
    assert!(coef_overflow.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_coef_mle() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // coef on multivariate polynomial (MLE) should succeed (returns 2^n elements)
    let coef_mle = coef(varstr("m"));
    let inferred = coef_mle.infer(&KIND_CTX, &fctx, &vctx).unwrap();
    assert_eq!(inferred, CTyp::vec(&CTyp::Base(Tid::from("F")), 256));
}

#[test]
fn test_random_challenge_rejection() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // challenge on non-existent kind "X" should fail
    let challenge_bad = challenge(Tid::from("X"));
    assert!(challenge_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // random on non-existent kind "X" should fail
    let random_bad = random(Tid::from("X"));
    assert!(random_bad.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // challenge on non-scalar kind "G" (Group) should fail
    let challenge_group = challenge(Tid::from("G"));
    assert!(challenge_group.infer(&KIND_CTX, &fctx, &vctx).is_err());

    // random on non-scalar kind "G" (Group) should fail
    let random_group = random(Tid::from("G"));
    assert!(random_group.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

#[test]
fn test_record_lub_vector_subtyping() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();

    // r1 = {| x: 1 |}
    let mut r1_fields = Ctx::new();
    r1_fields.insert(&"x".to_string(), &lit(1));
    let r1 = record(r1_fields);

    // r2 = {| x: 1, y: 2 |}
    let mut r2_fields = Ctx::new();
    r2_fields.insert(&"x".to_string(), &lit(1));
    r2_fields.insert(&"y".to_string(), &lit(2));
    let r2 = record(r2_fields);

    // v = [r1, r2]
    // Under intersection LUB: LUB({x}, {x, y}) = {x}
    let v = vec(vec![r1, r2]);

    // Accessing common field "x" via ram(v, 0).x is correct and should succeed
    let proj_x = proj(ram(v.clone(), lit(0)), "x".to_string());
    assert_eq!(
        proj_x.infer(&KIND_CTX, &fctx, &vctx),
        Ok(CTyp::Fin(CRange::from_raw(1, 1, 2)))
    );

    // Accessing extra field "y" via ram(v, 0).y is incorrect and must fail typechecking
    let proj_y = proj(ram(v, lit(0)), "y".to_string());
    assert!(proj_y.infer(&KIND_CTX, &fctx, &vctx).is_err());
}

fn gen_arbitrary_cexp(u: &mut arbitrary::Unstructured, depth: usize) -> arbitrary::Result<CExp> {
    if depth == 0 {
        let choice = u.int_in_range(0..=1)?;
        match choice {
            0 => Ok(CExp::Lit(u.arbitrary()?)),
            1 => {
                let vars = ["f1", "f2", "v1", "v2", "g1", "g2", "s1", "s2", "p", "m"];
                let var = u.choose(&vars)?;
                Ok(CExp::Var(Vid::from(*var)))
            }
            _ => unreachable!(),
        }
    } else {
        let choice = u.int_in_range(0..=12)?;
        match choice {
            0..=2 => gen_arbitrary_cexp(u, 0),
            3 => {
                let inner = gen_arbitrary_cexp(u, depth - 1)?;
                Ok(CExp::Poly(Box::new(Spanned::dummy(inner))))
            }
            4 => {
                let inner = gen_arbitrary_cexp(u, depth - 1)?;
                Ok(CExp::Coef(Box::new(Spanned::dummy(inner))))
            }
            5 => {
                let inner = gen_arbitrary_cexp(u, depth - 1)?;
                Ok(CExp::Mle(Box::new(Spanned::dummy(inner))))
            }
            6 => {
                let len = u.int_in_range(0..=4)?;
                let mut elms = Vec::new();
                for _ in 0..len {
                    elms.push(Spanned::dummy(gen_arbitrary_cexp(u, depth - 1)?));
                }
                Ok(CExp::Vec(Exps(elms)))
            }
            7 => {
                let a = gen_arbitrary_cexp(u, depth - 1)?;
                let b = gen_arbitrary_cexp(u, depth - 1)?;
                let op = u.choose(&[
                    BinOp::Add,
                    BinOp::Sub,
                    BinOp::Mul,
                    BinOp::Div,
                    BinOp::Pow,
                    BinOp::Dot,
                    BinOp::Rem,
                    BinOp::Concat,
                ])?;
                Ok(CExp::Bin(
                    *op,
                    Box::new(Spanned::dummy(a)),
                    Box::new(Spanned::dummy(b)),
                ))
            }
            8 => {
                let a = gen_arbitrary_cexp(u, depth - 1)?;
                let b = gen_arbitrary_cexp(u, depth - 1)?;
                Ok(CExp::Ram(
                    Box::new(Spanned::dummy(a)),
                    Box::new(Spanned::dummy(b)),
                ))
            }
            9 => {
                let tids = ["F", "G", "S", "X"];
                let tid = u.choose(&tids)?;
                Ok(CExp::Challenge(Tid::from(*tid), u.arbitrary()?))
            }
            10 => {
                let tids = ["F", "G", "S", "X"];
                let tid = u.choose(&tids)?;
                Ok(CExp::Random(Tid::from(*tid), u.arbitrary()?))
            }
            11 => {
                let inner = gen_arbitrary_cexp(u, depth - 1)?;
                let range = CRange::from_raw(u.int_in_range(0..=5)?, 1, u.int_in_range(0..=5)?);
                let has_range = u.arbitrary()?;
                let has_point = u.arbitrary()?;
                let opt_range = if has_range { Some(range) } else { None };
                let opt_point = if has_point {
                    Some(Box::new(Spanned::dummy(gen_arbitrary_cexp(u, depth - 1)?)))
                } else {
                    None
                };
                Ok(CExp::Evaluate(
                    Box::new(Spanned::dummy(inner)),
                    opt_range,
                    opt_point,
                ))
            }
            12 => {
                let start = u.int_in_range(0..=5)?;
                let end = u.int_in_range(0..=5)?;
                Ok(CExp::Range(CRange::from_raw(start, 1, end)))
            }
            _ => unreachable!(),
        }
    }
}

#[test]
fn test_no_panic_compiler_fuzzer() {
    let fctx = Set::new();
    let vctx = VAR_CTX.clone();
    arbtest::arbtest(|u| {
        let e = gen_arbitrary_cexp(u, 3)?;
        // We only assert that inference does not panic (crash)
        let _ = e.infer(&KIND_CTX, &fctx, &vctx);
        Ok(())
    });
}

#[test]
fn test_proto_body_blames_body_not_relation() {
    let name = Vid::from("my_proto");
    let sig = crate::ast::CSig {
        name: Spanned::dummy(name.clone()),
        typevars: Spanned::dummy(TypeVars(vec![])),
        args: Spanned::dummy(crate::ast::Args(vec![])),
        ret: Some(Spanned::dummy(CTyp::Unit)),
    };
    let fctx = Set::new();
    let body = crate::ast::CBody::Proto {
        relation: Spanned::dummy(CExp::Unit), // no constraints — the body is what fails
        body: Some(lit(5)),                   // body has type Fin (invalid, expected Unit)
    };
    let res = body.typecheck(sig, &fctx);
    let err = res.unwrap_err();
    // Under correct behavior, this should wrap the offending body expression CExp::Lit(5)
    assert!(matches!(
        err,
        TypeError::Decl(_, box TypeError::Unit(_, _, CExp::Lit(5)))
    ));
}

#[test]
fn test_unify_err_identifies_missing_variable() {
    let mut ctx = Ctx::new();
    ctx.insert(&Tid::from("a"), &Kind::<usize>::Field);
    let mut subs = crate::typ::AliasSubsts::new();
    let res = crate::typ::unify::Unify::unify(&Tid::from("a"), &Tid::from("b"), &ctx, &mut subs);
    // Under correct behavior, this should fail with KindNotFound(b) since b is missing.
    assert_eq!(
        res,
        Err(crate::typ::unify::UnifyError::KindNotFound(Tid::from("b")))
    );
}

#[test]
fn test_fin_coercion_avoids_fragile_alphabetical_fallback() {
    let mut ctx = Ctx::new();
    ctx.insert(&Tid::from("F"), &Kind::<usize>::Field);
    ctx.insert(&Tid::from("E"), &Kind::<usize>::Field);
    let typ = CTyp::Fin(Range::singleton(0));
    // Under correct behavior, we shouldn't arbitrarily fallback to "E".
    // We expect it to either return None (ambiguity) or a specific resolved field type if annotated,
    // but definitely not just "E" alphabetically.
    assert_eq!(typ.to_scalar(&ctx), None);
}

#[test]
fn test_lub_concat_appends_vector_element() {
    let mut ctx = Ctx::new();
    ctx.insert(&Tid::from("F"), &Kind::<usize>::Field);
    let inner_t = CTyp::Base(Tid::from("F"));
    let tb = CTyp::Vec(Box::new(Spanned::dummy(inner_t.clone())), 3); // Vec<F, 3>
    let ta = CTyp::Vec(Box::new(Spanned::dummy(tb.clone())), 2); // Vec<Vec<F, 3>, 2>

    let res = CTyp::lub_concat(&ta, &tb, &ctx);
    // Under correct behavior, appending a vector elements (tb) to a vector of vectors (ta)
    // should succeed and return Vec<Vec<F, 3>, 3>.
    assert_eq!(res, Ok(CTyp::Vec(Box::new(Spanned::dummy(tb)), 3)));
}

#[test]
fn test_type_alias_cycle_returns_error_instead_of_overflow() {
    let ex = concat!(
        "type A = B;\n",
        "type B = A;\n",
        "fn f<F: Field>(instance a: A) -> F {\n",
        "    a\n",
        "}\n"
    );
    // Under correct behavior, this should return an Err containing a cycle/malformed conversion error,
    // rather than stack-overflowing and crashing.
    let res = crate::ast::UModule::from_str(ex);
    assert!(res.is_err());
}
