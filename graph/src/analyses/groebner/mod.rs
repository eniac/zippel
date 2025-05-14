pub mod buchberger;
pub use buchberger::GroebnerBasis;

pub mod sparsepoly;
pub use sparsepoly::{LexDegTerm, SparsePolynomial};

use crate::{GOp, Op, Ref};
use lang::typ::{Distribution, Qualifier, Range};
use lang::ast::BinOp;
use crate::DQDag;
use crate::{analyses::TransClos, StaticAnalysis};
use crate::pref::{PRef, LexTerm};

use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::{Value, ATyp, ArkConfig, ArkScalarOps};
use std::fmt;
use ark_ff::{One, Zero};

/// This is used to construct a Groebner basis from the ideals corresponding to
/// each one of groups G1, G2, GT and the scalar ring F.
/// Construct a Groebner basis from a graph, by first taking the transitive
/// closure of the graph, building a set of equations of polynomials. Non-polynomial
/// terms are replaced with variables in [npterms].
#[derive(Clone)]
pub struct GroebnerBuilder<C: ArkConfig> {
    equ: GroebnerBasis<C::F, PRef, LexTerm>,
    vars: Ctx<PRef, GOp<C>>,
    args: Set<PRef>,
}

impl<C: ArkConfig> GroebnerBuilder<C> {
    pub fn new() -> Self {
        Self {
            equ: GroebnerBasis::empty(0),
            vars: Ctx::new(),
            args: Set::new(),
        }
    }

    pub fn from_input(g: &DQDag<C>) -> Self {
        let tc = TransClos::from_input(g);
        let mut s = Self::new();
        s.add_tc(tc);
        s
    }

    pub fn from_relation(g: &DQDag<C>) -> Self {
        let tc = TransClos::from_relation(g);
        let mut s = Self::new();
        s.add_tc(tc);
        s
    }

    pub fn add_input(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_input(g);
        self.add_tc(tc);
    }

    pub fn add_relation(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_relation(g);
        self.add_tc(tc);
    }

    fn add_tc(&mut self, tc: TransClos<C>) {
        self.vars.append(&tc.clos.clone().into_iter().collect());
        self.args.append(tc.args.clone().into_iter());
        
        for (i, op) in tc.clos.into_iter() {
            self.vars.insert(&i, &op);
            self.add_poly(i, op);
        }
    }

    pub fn find_ref(&self, r: &Ref) -> PRef {
        self.vars.iter()
        .find(|v| v.0.reference == *r)
        .map(|(v, _)| v.clone())
        .or_else(|| self.args.iter()
            .find(|v| v.var() == r.var() && v.is_var())
            .cloned())
        .unwrap_or_else(|| {
            panic!("Reference {} not found in context \n{}", r, self);
        })
    }

    pub fn private(&self) -> Vec<PRef> {
        self.vars.iter()
        .filter(|(v, _)| v.is_private()).map(|(v, _)| v.clone())
        .collect()
    }

    pub fn public(&self) -> Vec<PRef> {
        self.vars.iter()
        .filter(|(v, _)| v.is_public()).map(|(v, _)| v.clone())
        .collect()
    }

    pub fn is_leak(p: &SparsePolynomial<C::F, PRef, LexDegTerm<PRef>>) -> bool {
        let vars = p.vars();
        // Contains both secret and public variables, and the secret values are non-uniform random
        vars.iter().all(|v| !v.is_uniform())
        && vars.iter().any(|v| v.is_public())
        && vars.iter().any(|v| v.is_private())
    }

    pub fn basis(&self) -> GroebnerBasis<C::F, PRef, LexTerm> {
        self.equ.clone()
    }

    /// Compute Groebner basis using Buchberger algorithm, the LexDeg variant
    /// for elimination order. Return the set of polynomials that leak information.
    pub fn run(&mut self) -> Vec<GOp<C>> {
        // Compute the Groebner basis using Buchberger algorithm
        self.equ = self.equ.clone().buchberger_and_reduce();

        // Eliminate intermediate variables
        self.equ.eliminate();

        // Remove dangling variables
        self.vars.retain(|v, _| self.equ.iter().any(|p| p.contains(v)));

        // Inline all polynomials except for public variables and terms with uniform random references
        let except = |r: &Ref, op: &GOp<C>| {
            let v = self.find_ref(r);
            v.is_public() || op.references().iter().any(|r| self.find_ref(r).is_uniform())
        };

        // Build inline context
        let ref_vars: Ctx<Ref, GOp<C>> = 
            self.vars.iter().map(|(v, op)| (v.reference.clone(), op.clone())).collect();

        // Inline inline GOp<C> in the polynomial
        self.equ.iter()
            .filter(|p| Self::is_leak(p)) 
            // 1. Create a set of polynomials that leak information
            .map(|poly| {           
                // 2. Translate from polynomials to readable programs by inlining GOp<C>
                let gpoly = 
                    poly.clone().map_vars(&|v: PRef| v.into_op().inline(&ref_vars, &except));
                let gop: GOp<C> = gpoly.into();
                GOp::equ(gop, 0.into())
            })
            .collect()
    }

    /// This function converts an operation to a vector of sparse polynomial expressions
    /// with vector coefficients. This means all vector values have a natural representation
    /// as the constant polynomials with degree 0.
    fn to_poly(&mut self, op: GOp<C>) -> Vec<SparsePolynomial<C::F, PRef, LexTerm>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = self.find_ref(&v);
                match typ {
                    ATyp::Vec(box t, n) =>
                        (0..n).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = t.clone();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    ATyp::Uni(n) =>
                        (0..n).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = ATyp::scalar();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    _ => vec![SparsePolynomial::var(&pf)]
                }
            },
            Op::Value(v) =>
                match v {
                    Value::Scalar(s) => vec![SparsePolynomial::lit(&s)],
                    Value::Bool(b) => vec![SparsePolynomial::lit(&if b { C::F::one() } else { C::F::zero() })],
                    Value::Index(i) => vec![SparsePolynomial::lit(&C::FOps::from_usize(i))],
                    Value::VecBool(v) =>
                            v.into_iter()
                            .map(|b| SparsePolynomial::lit(&if b { C::F::one() } else { C::F::zero() }))
                            .collect::<Vec<_>>(),
                    Value::VecScalar(v) =>
                        v.into_iter()
                            .map(|s| SparsePolynomial::lit(&s))
                            .collect::<Vec<_>>(),
                    Value::VecIndex(v) =>
                        v.into_iter()
                            .map(|i| SparsePolynomial::lit(&C::FOps::from_usize(i)))
                            .collect::<Vec<_>>(),
                    Value::Range(r) =>
                        r.into_iter()
                            .map(|i| SparsePolynomial::lit(&C::FOps::from_usize(i)))
                            .collect::<Vec<_>>(),
                    Value::Vec(v) => v.into_iter().flat_map(|v| self.to_poly(Op::Value(v))).collect(),
                    _ => unreachable!("Unsupported value: {}", v),
                },
            Op::Vec(v) =>
                v.into_iter().flat_map(|v| self.to_poly(v)).collect(),
            Op::Ram(box Op::Ref(n, _), box Op::Value(v)) => {
                let pf = self.find_ref(&n);
                match v {
                    Value::Range(r) =>
                        r.into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    Value::Index(i) => vec![SparsePolynomial::var(&pf.with_index(i))],
                    _ => vec![SparsePolynomial::var(&pf)],
                }
            },
            // Dynamic indexing, overapproximate
            Op::Ram(box a, _) => self.to_poly(a),
            _ => unreachable!("Unsupported operation: {}", op),
        }
    }

    fn add_poly(&mut self, pr: PRef, op: GOp<C>) {
        match op {
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))|
                 self.equ.push(a + b - SparsePolynomial::var(&pr.clone().with_index(i)))),
            Op::Bin(BinOp::Sub, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))|
                        self.equ.push(a - b - SparsePolynomial::var(&pr.clone().with_index(i)))),
            Op::Bin(BinOp::Mul, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))|
                        self.equ.push(a * b - SparsePolynomial::var(&pr.clone().with_index(i)))),
            Op::Bin(BinOp::Dot, box a, box b, _) => {
                let mut sum = SparsePolynomial::zero();
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .for_each(|(a, b)| sum += a * b);
                self.equ.push(sum - SparsePolynomial::var(&pr.clone()))
            },
            Op::Bin(BinOp::Div, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))|
                        // Add v * ob = oa
                        self.equ.push(a - b * SparsePolynomial::var(&pr.clone().with_index(i)))),
            Op::Bin(BinOp::Equ, box a, box b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .for_each(|(a, b)|
                        // Add a == b
                        self.equ.push(a - b)),
            Op::Check(box a) => self.add_poly(pr, a),
            _ => {}
        }
    }
}

impl<'a, C, D, A> Pretty<'a, D, A> for GroebnerBuilder<C>
where
    C: ArkConfig,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.concat([
            allocator.text("Arguments: "),
            allocator.hardline(),
            allocator.intersperse(
                self.args.into_iter().map(|n| n.pretty(allocator)), ", "
            ),
            allocator.hardline(),
            allocator.text("Equations: "),
            allocator.hardline(),
            allocator.intersperse(
                self.equ.into_iter().map(|p| p.pretty(allocator).indent(8)),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.hardline(),
            allocator.text("Variable definitions: "),
            allocator.hardline(),
            allocator.intersperse(
                self.vars.into_iter().map(|(r, op)|
                    allocator.text(r.verbose())
                        .append(allocator.text(": "))
                        .append(op.pretty(allocator)).indent(8)),
                allocator.hardline(),
            )
        ])
    }

    fn is_nil(&self) -> bool {
        self.equ.is_empty() && self.vars.is_empty()
    }
}

impl<C: ArkConfig> fmt::Display for GroebnerBuilder<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerBuilder<C> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

impl<C: ArkConfig> StaticAnalysis<C, (Qualifier, Distribution)> for GroebnerBuilder<C> {
    type Args = ();
    type Output = Vec<GOp<C>>;

    fn new(g: &DQDag<C>) -> Self {
        Self::from_input(g)
    }

    fn run(&mut self, _: ()) -> Vec<GOp<C>> {
        self.run()
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::analyses::{UniformityPropagation, QualifierPropagation};
#[cfg(test)] use crate::UDags;
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
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);
    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);


    // Compute Groebner basis for the implementation
    let mut groebner = GroebnerBuilder::from_input(&g);

    // Compute the Groebner bases
    let leaks = groebner.run();

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
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_bar").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);
    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::from_input(&g);

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
        proto baz<F: Field, N: 4..8>(private s: [F; N], private s': F) where s[3] == s' {
            let r = random<F>;
            a <- r * s[3];
            b <- r * s';
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_baz").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);
    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::from_input(&g);

    // Compute the Groebner basis
    let leaks = groebner.run();

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
fn groebner_schnorr() {

    let ex = r#"
        proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F>;
            z <- r + x*c;
            verify(g*z == u + h*c);
        }"#;

    println!("Parsing Schnorr example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_schnorr").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::from_input(&g);

    // Compute the Groebner basis
    let leaks = groebner.run();

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

#[cfg(test)] use crate::WritePdf;
/// This example is somewhat contrived. Here is how we leak s = s'.
/// 1. We have two private inputs s and s'.
/// 2. a - b = s - s'
/// 3. g*a = g*b from [verify]
/// 4. g*(a - b) = g *(s - s') = 0 from [2]
/// 5. s = s' if g != 0.
#[test]
fn groebner_ex3() {
    let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(private s: F, private s': F, public g: G) where s == s {
            let r = random<F>;
            let a = r + s;
            let b = r + s';
            c <- g * a;
            d <- g * b;
            verify(c == d);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_ex3").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::from_input(&g);


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
fn groebner_zerocheck() {
    let ex = r#"
        proto zerocheck<F: Field>(private p: Uni<F, 16>, public q: Uni<F, 16>) where p == q {
            let r = random<F>;
            verify(p(r) == q(r))
        }"#;

    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    let g_inp = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);

    let mut groebner = GroebnerBuilder::from_input(&g);
    let leaks = groebner.run();

    println!("Groebner basis:\n{}", groebner);
    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }
}
