pub mod groebner;

use groebner::{Monomial, VecField, SparsePolynomial};

use crate::{GOp, Op, Ref, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::{id::{Fresh, Vid}, typ::Range};
use lang::ast::{BinOp, CArg};
use lang::typ::CRange;
use crate::analyses::principal::Principal;
use crate::analyses::TransClos;
use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::{Value, ATyp, ArkConfig, ArkScalarOps};
use std::hash::{DefaultHasher, Hash};
use std::fmt;
use itertools::Itertools;
use std::cmp::Ordering;
use std::ops::{Mul, Div, MulAssign, Neg};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, Zero, BigInteger, PrimeField};

/// A variable in the Groebner basis
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PRef {
    pub reference: Ref,
    pub range: CRange,
    pub typ: ATyp,
    pub principal: Principal,
}

impl PRef {
    pub fn new(reference: Ref, typ: ATyp, principal: Principal) -> Self {
        PRef { reference, range: Range::new(0, typ.size()), typ, principal }
    }
    pub fn is_prover(&self) -> bool {
        self.principal == Principal::Prover
    }
    pub fn is_verifier(&self) -> bool {
        self.principal == Principal::Verifier
    }
}

impl fmt::Display for PRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.reference)
    }
}

/// A monomial term in the Groebner basis
#[derive(Clone, PartialEq, Eq, PartialOrd, Debug)]
pub struct LexDegTerm {
    pub vars: Ctx<PRef, usize>, // (var index, power)
}

impl LexDegTerm {
    pub fn new(term: Ctx<PRef, usize>) -> Self {
        LexDegTerm { vars: term }
    }
}

/// Multiplies two terms. (var, power) pairs are combined by adding powers
/// for common variables.
impl MulAssign for LexDegTerm {
    fn mul_assign(&mut self, other: Self) {
        for (var, power) in other.vars.iter() {
            *self.vars.entry(var.clone()).or_insert(0) += power;
        }
    }
}

impl Mul for LexDegTerm {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<'a> Mul for &'a LexDegTerm {
    type Output = LexDegTerm;

    fn mul(self, other: &'a LexDegTerm) -> LexDegTerm {
        self.clone() * other.clone()
    }
}

impl fmt::Display for LexDegTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_constant() {
            write!(f, "1")
        } else {
            let mut terms: Vec<String> = Vec::new();
            for (var, power) in self.vars.iter() {
                if *power > 0 {
                    terms.push(format!("{}^{}", var, power));
                }
            }
            write!(f, "{}", terms.join(" * "))
        }
    }
}

impl Div for LexDegTerm {
    type Output = Option<Self>;

    fn div(self, other: Self) -> Option<Self> {
        if !self.is_divided(&other) {
            return None;
        }

        let mut powers1 = self.vars.iter().map(|(v, p)| (v.clone(), *p)).collect::<Vec<_>>();
        for (var, power2) in other.vars.iter() {
            // We know var is in powers1 with sufficient power because term_is_divided was true
            if let Some(power1) = powers1.iter_mut().find(|(v, _)| v == var) {
                power1.1 -= power2;
            }
        }

        Some(Self::new(powers1.into_iter().filter(|(_, p)| *p > 0).collect()))
    }
}

impl<'a> Div for &'a LexDegTerm {
    type Output = Option<LexDegTerm>;

    fn div(self, other: &'a LexDegTerm) -> Option<LexDegTerm> {
        self.clone() / other.clone()
    }
}

impl From<Vec<(PRef, usize)>> for LexDegTerm {
    fn from(vars: Vec<(PRef, usize)>) -> Self {
        LexDegTerm::new(vars.into_iter().collect())
    }
}


impl Monomial<PRef> for LexDegTerm {
    fn vars(&self) -> Vec<PRef> {
        self.vars.iter().map(|(v, _)| v.clone()).collect()
    }
    fn powers(&self) -> Vec<usize> {
        self.vars.iter().map(|(_, p)| *p).collect()
    }
    fn is_constant(&self) -> bool {
        self.vars.iter().next().is_none() // Empty vec means the term is 1 (constant)
    }

    fn evaluate<F: Field>(&self, p: &Ctx<PRef, F>) -> F {
        let mut result = F::one();
        for (var, power) in self.vars.iter() {
            if let Some(value) = p.get(&var) {
                for _ in 0..*power {
                    result *= value;
                }
            } else {
                // Variable not found in context, assume it evaluates to 1
            }
        }
        result
    }
    fn is_divided(&self, other: &Self) -> bool {
        for (var, power2) in other.vars.iter() {
            match self.vars.get(var) {
                Some(power1) => {
                    if power1 < power2 {
                        return false;
                    }
                }
                None => return false, // other has a variable self doesn't have
            }
        }
        true // All variables in other are in self with sufficient power
    }

    fn lcm(&self, other: &Self) -> Self {
        let mut lcm_powers: Vec<(PRef, usize)> = self.vars.iter().map(|(v, p)| (v.clone(), *p)).collect();
        for (var, power2) in other.vars.iter() {
            match lcm_powers.iter_mut().find(|(v, _)| v == var) {
                Some((_, power1)) => *power1 = (*power1).max(*power2),
                None => lcm_powers.push((var.clone(), *power2)),
            }
        }
        Self::new(lcm_powers.into_iter().collect())
    }

    // Ignore principals, we only care about the powers for comparison
    fn grevlex(&self, other: &Self) -> Ordering {
        match other.degree().cmp(&self.degree()) {
            Ordering::Equal => {},
            order => return order,
        };

        // Compare powers in reverse lexicographic order
        for ((v1, p1), (v2, p2)) in self.vars.iter().zip(other.vars.iter()).rev() {
            match (v1.cmp(v2), p1.cmp(p2)) {
                (Ordering::Equal, Ordering::Equal) => continue,
                (order, Ordering::Equal) => return order,
                (_, order) => return order,
            }
        }
        Ordering::Equal
    }
}

/// Define elimination order comparison. First, we compare principals such that if any variable has
/// Principal::Any > Principal::Verifier and Principal::Any > Principal::Prover, then the same is true for LexDegTerm.
/// If the principals are equal, then perform a grevlex comparison on the powers of the variables (graded, reverse lexicographic order).
impl Ord for LexDegTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        let any_self = LexDegTerm {
            vars: self.vars.iter()
                .filter(|(var, _)| var.principal == Principal::Any)
                .map(|(var, power)| (var.clone(), *power))
                .collect()
        };

        let any_other = LexDegTerm {
            vars: other.vars.iter()
                .filter(|(var, _)| var.principal == Principal::Any)
                .map(|(var, power)| (var.clone(), *power))
                .collect()
        };

        // Compare the Principal::Any variables first using grevlex
        match any_self.grevlex(&any_other) {
            Ordering::Equal => {},
            order => return order,
        };

        // If they are equal, compare the remaining variables
        let other_self = LexDegTerm {
            vars: self.vars.iter()
                .filter(|(var, _)| var.principal != Principal::Any)
                .map(|(var, power)| (var.clone(), *power))
                .collect()
        };
        let other_other = LexDegTerm {
            vars: other.vars.iter()
                .filter(|(var, _)| var.principal != Principal::Any)
                .map(|(var, power)| (var.clone(), *power))
                .collect()
        };

        // If they are equal, compare the remaining variables
        other_self.grevlex(&other_other)
    }
}

/// This is used to construct a Groebner basis from the ideals corresponding to
/// each one of groups G1, G2, GT and the scalar ring F.
/// Construct a Groebner basis from a graph, by first taking the transitive
/// closure of the graph, building a set of equations of polynomials. Non-polynomial
/// terms are replaced with variables in [npterms].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GroebnerBasis<C: ArkConfig> {
    equ: Vec<SparsePolynomial<C::F, PRef, LexDegTerm>>,
    vars: Set<PRef>,
    npterms: Ctx<usize, GOp<C>>,
}

impl<C: ArkConfig> GroebnerBasis<C> {
    pub fn new<A: Clone>(tc: TransClos<C, A>) -> Self {
        let mut s = GroebnerBasis {
            equ: Vec::new(),
            vars: tc.public.into_iter()
                .map(|(n, t)| PRef::new(n, t, Principal::Verifier))
                .chain(tc.private.into_iter()
                    .map(|(n, t)| PRef::new(n, t, Principal::Prover)))
                .collect(),
            npterms: Ctx::new(),
        };

        for (i, op) in tc.clos.into_iter() {
            s.from_op(i, op)
        }
        s
    }

    pub fn find_ref(&self, r: &Ref) -> Option<PRef> {
        self.vars.iter().find(|v| v.reference == *r).cloned()
    }

    pub fn max_node(&self) -> NodeIndex {
        self.vars.iter().filter_map(|i|
            match i.reference {
                Ref::Node(n) => Some(n),
                _ => None
            }).max().unwrap_or(NodeIndex::new(0))
    }

    pub fn private(&self) -> Vec<PRef> {
        self.vars.iter().filter(|v| v.is_prover()).cloned().collect()
    }

    pub fn public(&self) -> Vec<PRef> {
        self.vars.iter().filter(|v| v.is_verifier()).cloned().collect()
    }

    pub fn compute(&mut self) {
        self.equ = groebner::buchberger(self.equ.clone());
        // Remove dangling variables
        self.vars.retain(|v| self.equ.iter().any(|p| p.contains(v)));
    }

    pub fn get_leaks(&self) -> Vec<SparsePolynomial<C::F, PRef, LexDegTerm>> {
        // Create a set of polynomials that leak information
        self.equ.iter().filter(|p| {
                let vars = p.vars();
                // Contains both secret and public variables, and at least one secret!
                vars.iter().all(|v| v.is_prover() || v.is_verifier())
                && vars.iter().any(|v| v.is_prover())
        }).cloned().collect()
    }

    pub fn print_leaks(&self) {
        // Create a set of polynomials that leak information
        let leaks = self.get_leaks();

        let msg =
            if leaks.is_empty() {
                format!(" No leaks found in Groebner basis ")
            } else {
                format!(" Found leaks in the Groebner basis: \n{}", leaks.into_iter().map(|v| format!("{}", v)).join("\n"))
            };
        println!("================================================");
        println!(" {} ", msg);
        println!("================================================");
        println!("{}", self);
    }

    /// This function converts an operation to a vector of sparse polynomial expressions
    /// with vector coefficients. This means all vector values have a natural representation
    /// as the constant polynomials with degree 0.
    fn to_poly(&mut self, op: GOp<C>) -> Vec<SparsePolynomial<C::F, PRef, LexDegTerm>> {
        match op {
            Op::Ref(v, _) =>
                vec![SparsePolynomial::var(&self.find_ref(&v).unwrap())],
            Op::Value(v) =>
                match v {
                    Value::Scalar(s) => vec![SparsePolynomial::lit(&s.into())],
                    Value::Bool(b) => vec![SparsePolynomial::lit(&if b { VecField::one() } else { VecField::zero() })],
                    Value::Index(i) => vec![SparsePolynomial::lit(&C::FOps::from_usize(i).into())],
                    Value::VecBool(v) =>
                        vec![SparsePolynomial::lit(
                            &v.into_iter()
                            .map(|b| if b { C::F::one() } else { C::F::zero() })
                            .collect::<Vec<_>>()
                            .into())],
                    Value::VecScalar(v) =>
                        vec![SparsePolynomial::lit(&v.into())],
                    Value::VecIndex(v) =>
                        vec![SparsePolynomial::lit(&v.into_iter().map(|i| C::FOps::from_usize(i)).collect::<Vec<_>>().into())],
                    Value::Range(r) =>
                        vec![SparsePolynomial::lit(&r.into_iter().map(|i| C::FOps::from_usize(i)).collect::<Vec<_>>().into())],
                    Value::Vec(v) => v.into_iter().flat_map(|v| self.to_poly(Op::Value(v))).collect(),
                    _ => unreachable!("Unsupported value: {}", v),
                },
            Op::Vec(v) =>
                v.into_iter().flat_map(|v| self.to_poly(v)).collect(),
            Op::Ram(box Op::Ref(n, _), box Op::Value(v)) => {
                let mut pf = self.find_ref(&n).unwrap();
                match v {
                    Value::Range(r) => {
                        pf.range = r;
                        vec![SparsePolynomial::var(&pf)]
                    },
                    Value::Index(i) => {
                        pf.range = Range::singleton(i);
                        vec![SparsePolynomial::var(&pf)]
                    },
                    _ => vec![SparsePolynomial::var(&self.find_ref(&n).unwrap())],
                }
            },
            Op::Ram(box a, _) => self.to_poly(a),
            _ => unreachable!("Unsupported operation: {}", op),
        }
    }

    fn from_op(&mut self, i: NodeIndex, op: GOp<C>) {
        let pf = self.find_ref(&Ref::Node(i)).unwrap();
        match op {
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut pf = pf.clone();
                        pf.range = Range::singleton(i);
                        self.equ.push(a + b - SparsePolynomial::var(&pf))
                    }),
            Op::Bin(BinOp::Sub, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut pf = pf.clone();
                        pf.range = Range::singleton(i);
                        self.equ.push(a - b - SparsePolynomial::var(&pf))
                    }),
            Op::Bin(BinOp::Mul | BinOp::Or | BinOp::Dot, box a, box b, _) => {
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut pf = pf.clone();
                        pf.range = Range::singleton(i);
                        self.equ.push(a * b - SparsePolynomial::var(&pf))
                    })
            },
            Op::Bin(BinOp::Div, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut pf = pf.clone();
                        pf.range = Range::singleton(i);
                        // Add v * ob = oa
                        self.equ.push(a - b * SparsePolynomial::var(&pf))
                    }),
            Op::Bin(BinOp::Equ, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut pf = pf.clone();
                        pf.range = Range::singleton(i);
                        // Add v * ob = oa
                        self.equ.push(a - b)
                    }),
            // Unsure what to do with these, I think from the view of information
            // theory those are identities?
            Op::Coef(box a) | Op::Eval(box a) | Op::Check(box a) => self.from_op(i, a),
            Op::Ref(_, _) => {},
            op => {
                // Create a new variable for an NP term
                self.npterms.insert(&i.index(), &op);
            }
        }
    }
}

impl<'a, D, A> Pretty<'a, D, A> for PRef
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        if self.range.len() == 1 {
            allocator.text(format!("{}[{}]", self.reference, self.range.start))
        } else {
            allocator.text(format!("{}[{}]", self.reference, self.range))
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, C, D, A> Pretty<'a, D, A> for GroebnerBasis<C>
where
    C: ArkConfig,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("#### Equations:"),
            allocator.hardline(),
            allocator.intersperse(
                self.equ.into_iter().map(|p| p.pretty(allocator)),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.text("#### Non-polynomial terms:"),
            allocator.hardline(),
            allocator.intersperse(
                self.npterms.into_iter().map(|(i, op)|
                    allocator.text(format!("{}: ", i))
                        .append(op.pretty(allocator))),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.text("#### Variables:"),
            allocator.hardline(),
            allocator.intersperse(
                self.vars.into_iter().map(|v| v.pretty(allocator)),
                allocator.hardline(),
            ),
        ])
    }

    fn is_nil(&self) -> bool {
        self.equ.is_empty() && self.npterms.is_empty()
    }
}

impl<C: ArkConfig> fmt::Display for GroebnerBasis<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerBasis<C> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[test]
fn groebner_foo() {

    let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r  + c + s;
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBasis::new(tc);

    // Compute the Groebner basis
    groebner.compute();

    // Compute the Groebner basis and print leaks
    groebner.print_leaks();
}

#[test]
fn groebner_bar() {

    let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            a <- r * s;
            b <- r * s';
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_bar").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBasis::new(tc);

    // Compute the Groebner basis
    groebner.compute();

    // Compute the Groebner basis and print leaks
    groebner.print_leaks();
}

#[test]
fn groebner_baz() {

    let ex = r#"
        proto foo<F: Field>(private s: [F; 5], private s': F) where s[3] == s' {
            let r = random<F>;
            a <- r * s[3];
            b <- r * s';
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_baz").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBasis::new(tc);

    // Compute the Groebner basis
    groebner.compute();

    // Compute the Groebner basis and print leaks
    groebner.print_leaks();
}

/// This example is somewhat contrived. Here is how we leak s = s'.
/// 1. We have two private inputs s and s'.
/// 2. a - b = s - s'
/// 3. g*a = g*b from [verify]
/// 4. g*(a - b) = g *(s - s') = 0 from [2]
/// 5. s = s' if g != 0.
#[test]
fn zk_ex3() {
    let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(private s: F, private s': F) where s == s {
            let r = random<F>;
            let a = r + s;
            let b = r + s';
            let g = gen<G>;
            c <- g * a;
            d <- g * b;
            verify(c == d);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc);
    for (_, op) in tc.clos.iter() {
        assert!(! matches!(op, Op::Bin(_, box Op::Bin(_, _, _, _), _, _)));
        assert!(! matches!(op, Op::Bin(_, _, box Op::Bin(_, _, _, _), _)));
    }
    println!("Public nodes: {}", tc.public);
}
