pub mod sparsepoly;
pub mod groebner;

use groebner::GroebnerBasis;
use sparsepoly::{LexDegTerm, VecField, Var, SparsePolynomial};

use crate::{GOp, Op, Ref};
use petgraph::graph::NodeIndex;
use lang::{id::Vid, typ::Range};
use lang::ast::BinOp;
use lang::typ::{Qualifier, CRange};
use crate::analyses::principal::Principal;
use crate::analyses::TransClos;
use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::{Value, ATyp, ArkConfig, ArkScalarOps};
use std::fmt;
use ark_ff::{One, Zero};

/// A variable in the Groebner basis
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PRef {
    pub reference: Ref,
    pub range: CRange,
    pub typ: ATyp,
    pub principal: Principal,
}

impl PRef {
    pub fn new(reference: &Ref, typ: &ATyp, principal: Principal) -> Self {
        PRef { reference: reference.clone(), range: Range::new(0, typ.size()), typ: typ.clone(), principal }
    }
    pub fn node(node: NodeIndex, typ: ATyp, principal: Principal) -> Self {
        PRef { reference: Ref::Node(node), range: Range::new(0, typ.size()), typ, principal }
    }
    pub fn var(v: Vid, typ: ATyp, principal: Principal) -> Self {
        PRef { reference: Ref::Var(v, NodeIndex::new(0)), range: Range::new(0, typ.size()), typ, principal }
    }

    pub fn is_prover(&self) -> bool {
        self.principal == Principal::Prover
    }
    pub fn is_verifier(&self) -> bool {
        self.principal == Principal::Verifier
    }
    pub fn is_any(&self) -> bool {
        self.principal == Principal::Any
    }
}

impl fmt::Display for PRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.reference)
    }
}

impl Var for PRef {
    fn eliminate(&self) -> bool {
        matches!(self.principal, Principal::Any)
    }
}

/// A monomial in the Groebner basis polynomials
pub type LexTerm = LexDegTerm<PRef>;

/// The solution to a groebner basis knowledge problem
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GroebnerLeak<C: ArkConfig> {
    args: Set<PRef>,
    equ: Vec<Vec<(GOp<C>, usize)>>,
}



/// Pretty-printer for a Groebner Extractor solution
impl<'a, D, C, A> Pretty<'a, D, A> for GroebnerLeak<C>
where
    D: DocAllocator<'a, A>,
    C: ArkConfig,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("GroebnerLeak("),
            allocator.intersperse(
                self.args.into_iter().map(|arg|
                    allocator.concat([
                        arg.principal.pretty(allocator),
                        allocator.space(),
                        arg.reference.pretty(allocator),
                        allocator.text(": "),
                        arg.typ.pretty(allocator)
                    ])), ", "),
            allocator.text(") {"),
            allocator.hardline(),
            allocator.concat([
                allocator.text("verify("),
                allocator.intersperse(
                    self.equ.into_iter().map(|terms|
                        allocator.intersperse(
                            terms.into_iter().map(|(op, p)|
                                if p == 1 {
                                    op.pretty(allocator)
                                } else {
                                    op.pretty(allocator)
                                        .append(allocator.text(format!("^{}", p)))
                                }
                            ), "*")), " + "),
                allocator.text(" == 0)"),
            ]).indent(2),
            allocator.hardline(),
            allocator.text("}")
        ])
    }

    fn is_nil(&self) -> bool {
        self.equ.is_empty()
    }
}

impl<'a, C: ArkConfig> fmt::Display for GroebnerLeak<C>{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerLeak<C> as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}


/// This is used to construct a Groebner basis from the ideals corresponding to
/// each one of groups G1, G2, GT and the scalar ring F.
/// Construct a Groebner basis from a graph, by first taking the transitive
/// closure of the graph, building a set of equations of polynomials. Non-polynomial
/// terms are replaced with variables in [npterms].
#[derive(Clone)]
pub struct GroebnerBuilder<C: ArkConfig, A> {
    equ: GroebnerBasis<C::F, PRef, LexTerm>,
    vars: Set<PRef>,
    npterms: Ctx<NodeIndex, GOp<C>>,
    tc: TransClos<C, A>
}

impl<C: ArkConfig, A> GroebnerBuilder<C, A> {
    pub fn new(tc: TransClos<C, A>) -> Self where A: Clone {
        let mut s = GroebnerBuilder {
            equ: GroebnerBasis::empty(tc.types.len()),
            vars: tc.types.iter()
                .map(|(n, t)|
                    match tc.visibility.get(n) {
                        Some(Qualifier::Public) => PRef::new(n, t, Principal::Verifier),
                        Some(Qualifier::Private) => PRef::new(n, t, Principal::Prover),
                        None => PRef::new(n, t, Principal::Any),
                    })
                .collect(),
            npterms: Ctx::new(),
            tc
        };

        for (i, op) in s.tc.clone().clos.into_iter() {
            s.from_op(i, op);
        }

        s
    }

    pub fn find_ref(&self, r: &Ref) -> Option<PRef> {
        self.vars.iter().find(|v| v.reference == *r).cloned()
    }

    pub fn private(&self) -> Vec<PRef> {
        self.vars.iter().filter(|v| v.is_prover()).cloned().collect()
    }

    pub fn public(&self) -> Vec<PRef> {
        self.vars.iter().filter(|v| v.is_verifier()).cloned().collect()
    }

    /// Compute Groebner basis using Buchberger algorithm, the LexDeg variant
    /// for elimination order.
    pub fn run(&mut self) -> Vec<GroebnerLeak<C>> {
        // Compute the Groebner basis using Buchberger algorithm
        // and minimize it
        let groeb_equ = GroebnerBasis::from(self.equ.clone());

        // Run the Buchberger algorithm and the reduction
        self.equ = groeb_equ.buchberger_and_reduce();

        // Remove dangling variables
        self.vars.retain(|v| self.equ.iter().any(|p| p.contains(v)));

        // Create a set of polynomials that leak information
        self.get_leaks()
    }

    pub fn get_leaks(&self) -> Vec<GroebnerLeak<C>> {
        // Create a set of polynomials that leak information
        let poly_leaks : Vec<SparsePolynomial<C::F, PRef, LexTerm>> =
            self.equ.iter().filter(|p| {
                let vars = p.vars();
                // Contains both secret and public variables, and at least one secret!
                vars.iter().all(|v| !v.is_any())
                && vars.iter().any(|v| v.is_prover())
                && vars.iter().any(|v| v.is_verifier())
            }).cloned().collect();

        // Translate from polynomials to Groebner solutions
        // using the transitive closure operations
        // Need to get :     terms: Vec<(C::F, Vec<(GOp<C>, usize)>)>
        poly_leaks.into_iter()
            .map(|p| self.leak_from_sparse(p))
            .collect()
    }

    fn leak_from_sparse(&self, poly: SparsePolynomial<C::F, PRef, LexTerm>) -> GroebnerLeak<C> {
        // We need to recontruct the original arguments
        let mut args = Set::new();

        // Node references to not inline, first non-polynomial terms, then Principal::Any terms
        let except = |n: NodeIndex, op: &GOp<C>| {
            self.npterms.contains(&n) || op.references().iter().filter_map(|r| self.find_ref(r)).any(|pf| pf.is_any())
        };

        // Finally reconstruct the verifier's leaked relation from a Groebner polynomial
        let mut equ = Vec::new();

        // We ignore coefficients; reduced Groebner basis are monic
        // Use TransClos::inline to recreate an expression, without np-terms
        for (mono, _) in poly.terms.into_iter() {
            let m: Vec<(GOp<C>, usize)> = mono.vars.into_iter()
                .map(|(v, p)| (self.tc.inline(&Op::Ref(v.reference.clone(), v.typ.clone()), &except), p))
                .collect();

            // Gather all variable references, their types and principals
            let refs = m.iter()
                .flat_map(|(op, _)| op.references())
                .filter_map(|r| self.find_ref(&r));

            // Add arguments found
            args.append(refs);

            // Add equation
            equ.push(m);
        }

        GroebnerLeak {
            args,
            equ
        }
    }

    /// This function converts an operation to a vector of sparse polynomial expressions
    /// with vector coefficients. This means all vector values have a natural representation
    /// as the constant polynomials with degree 0.
    fn to_poly(&mut self, op: GOp<C>) -> Vec<SparsePolynomial<C::F, PRef, LexTerm>> {
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
        let pf = self.find_ref(&i.into()).unwrap_or_else(|| PRef::node(i, op.typ(), Principal::Any));
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
                self.npterms.insert(&i, &op);
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
        if self.range.len() == 1 && self.range.start == 0 {
            allocator.text(format!("{}", self.reference))
        } else if self.range.len() == 1 {
            allocator.text(format!("{}[{}]", self.reference, self.range.start))
        } else {
            allocator.text(format!("{}[{}]", self.reference, self.range))
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a, C, D, A, X> Pretty<'a, D, A> for GroebnerBuilder<C, X>
where
    C: ArkConfig,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("####### Equations: ########"),
            allocator.hardline(),
            allocator.intersperse(
                self.equ.into_iter().map(|p| p.pretty(allocator).indent(8)),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.hardline(),
            allocator.text("#######  Non-polynomial terms: #######"),
            allocator.hardline(),
            allocator.intersperse(
                self.npterms.into_iter().map(|(i, op)|
                    allocator.text(format!("{}: ", i.index()))
                        .append(op.pretty(allocator)).indent(8)),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.hardline(),
            allocator.text("#######  Variables: #######"),
            allocator.hardline(),
            allocator.intersperse(
                self.vars.into_iter().map(|v| {
                    let typ = v.typ.clone();
                    let prin = v.principal.clone();
                    allocator.concat([
                        v.pretty(allocator),
                        allocator.text(format!(": {} ", prin)),
                        typ.pretty(allocator),
                    ]).indent(8)
                }),
                allocator.hardline(),
            ),
            allocator.hardline(),
        ])
    }

    fn is_nil(&self) -> bool {
        self.equ.is_empty() && self.npterms.is_empty()
    }
}

impl<C: ArkConfig, A: Clone> fmt::Display for GroebnerBuilder<C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerBuilder<C, A> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::UDag;
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

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);
    println!("PRE-GROEBNER");
    println!("{}", groebner);
    // Compute the Groebner basis
    let leaks = groebner.run();

    println!("POST-GROEBNER");
    println!("{}", groebner);
    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }
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

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);
    // Compute the Groebner basis
    let leaks = groebner.run();

    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }
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

    println!("{}", tc);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);

    // Compute the Groebner basis
    let leaks = groebner.run();

    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }
}

/// This example is somewhat contrived. Here is how we leak s = s'.
/// 1. We have two private inputs s and s'.
/// 2. a - b = s - s'
/// 3. g*a = g*b from [verify]
/// 4. g*(a - b) = g *(s - s') = 0 from [2]
/// 5. s = s' if g != 0.
#[test]
fn groebner_ex3() {
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

    println!("{}", tc);
    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);

    // Compute the Groebner basis
    let leaks = groebner.run();

    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("\t{}", leak);
        }
    }
}
