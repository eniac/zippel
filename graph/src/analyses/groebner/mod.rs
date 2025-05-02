pub mod buchberger;

use buchberger::GroebnerBasis;

use crate::{GOp, Op, Ref};
use petgraph::graph::NodeIndex;
use lang::typ::{Qualifier, Range};
use lang::ast::BinOp;
use crate::analyses::{Principal, PRef, LexTerm, TransClos, LexDegTerm, VecField, Var, SparsePolynomial};

use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::{Value, ArkConfig, ArkScalarOps};
use std::fmt;
use ark_ff::{One, Zero};

/// A variable in the Groebner basis
/// The solution to a groebner basis knowledge problem
/// Is two polynomials, the [lhs] contains Prover Variables
/// and the [rhs] contains Verifier variables. We use [Gop<C>]
/// as the variable representation to recover the program structure.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GroebnerLeak<C: ArkConfig> {
    args: Set<PRef>,
    lhs: SparsePolynomial<C::F, GOp<C>, LexDegTerm<GOp<C>>>,
    rhs: SparsePolynomial<C::F, GOp<C>, LexDegTerm<GOp<C>>>,
    constraints: Set<GOp<C>>
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
                self.lhs.pretty(allocator),
                allocator.text(" == "),
                self.rhs.pretty(allocator),
            ]).indent(2),
            allocator.hardline(),
            allocator.text("}"),
            if self.constraints.is_empty() {
                allocator.nil()
            } else {
                allocator.text(" when ")
            },
            allocator.hardline(),
            allocator.intersperse(
                self.constraints.into_iter().map(|c|
                    c.pretty(allocator).append(allocator.text("!= 0"))),
                allocator.hardline(),
            ).indent(2),
        ])
    }

    fn is_nil(&self) -> bool {
        self.lhs.is_constant() && self.rhs.is_constant()
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
    npterms: Ctx<Ref, GOp<C>>,
    tc: TransClos<C, A>
}

impl<C: ArkConfig, A: Clone> GroebnerBuilder<C, A> {
    pub fn new(tc: TransClos<C, A>) -> Self {
        let mut s = GroebnerBuilder {
            equ: GroebnerBasis::empty(tc.clos.len()),
            vars: tc.types().iter()
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
    pub fn run(&mut self) {
        // Compute the Groebner basis using Buchberger algorithm
        let groeb_equ = GroebnerBasis::from(self.equ.clone());

        // Run the Buchberger algorithm and the reduction
        self.equ = groeb_equ.buchberger_and_reduce();

        // Remove dangling variables
        self.vars.retain(|v| self.equ.iter().any(|p| p.contains(v)));
    }

    pub fn get_leaks(&self) -> Vec<GroebnerLeak<C>> {

        // Node references to not inline, first non-polynomial terms, then Principal::Any terms
        let except = |r: &Ref, op: &GOp<C>| {
            self.npterms.contains(r) || op.references().iter().filter_map(|r| self.find_ref(r)).any(|pf| pf.is_any())
        };
        // 1. Create a set of polynomials that leak information
        self.equ.iter()
            .filter(|p| {
                let vars = p.vars();
                // Contains both secret and public variables, and at least one secret!
                vars.iter().all(|v| !v.is_any())
                && vars.iter().any(|v| v.is_prover())
                && vars.iter().any(|v| v.is_verifier())
            }).cloned()         // 2. Translate from polynomials to Groebner solutions, by isolating variables.
            .map(|p| // Isolate private variables on the lhs
                p.isolate_elimination_vars(&|pf| pf.is_prover()))
            .map(|(lhs, rhs, constr)| {
                let n_lhs = lhs.map_vars(&|v: PRef| self.tc.inline(&v.into_op(), &except));
                let n_rhs = rhs.map_vars(&|v: PRef| self.tc.inline(&v.into_op(), &except));
                let args = n_lhs.vars().iter()
                    .flat_map(|v| v.references())
                    .filter_map(|r| self.find_ref(&r))
                    .chain(
                        n_rhs.vars().iter()
                            .flat_map(|v| v.references())
                            .filter_map(|r| self.find_ref(&r))
                    ).collect::<Set<_>>();

                GroebnerLeak {
                    args,
                    lhs: n_lhs,
                    rhs: n_rhs,
                    constraints: constr.into_iter()
                        .map(|c| self.tc.inline(&Op::Ref(c.reference.clone(), c.typ.clone()), &except))
                        .collect()
                }
            })
            .collect()
    }

    /// This function converts an operation to a vector of sparse polynomial expressions
    /// with vector coefficients. This means all vector values have a natural representation
    /// as the constant polynomials with degree 0.
    fn to_poly(&mut self, op: GOp<C>) -> Vec<SparsePolynomial<C::F, PRef, LexTerm>> {
        match op {
            Op::Ref(v, _) => {
                println!("\nREF: {:?}, VARS: {:?}", v, self.vars);
                vec![SparsePolynomial::var(&self.find_ref(&v).unwrap())]
            },
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

    fn from_op(&mut self, r: Ref, op: GOp<C>) {
        let pf = self.find_ref(&r).unwrap_or_else(|| PRef::new(&r, &op.typ(), Principal::Any));
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
            Op::Coef(box a) | Op::Eval(box a) | Op::Check(box a) => self.from_op(r, a),
            Op::Ref(_, _) => {},
            op => {
                // Create a new variable for an NP term
                self.npterms.insert(&r, &op);
            }
        }
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
                self.npterms.into_iter().map(|(r, op)|
                    r.pretty(allocator)
                        .append(allocator.text(": "))
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
    let tc = TransClos::new(g, 0);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);
    // Compute the Groebner basis
    groebner.run();
    let leaks = groebner.get_leaks();

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
    let tc = TransClos::new(g, 0);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);
    // Compute the Groebner basis
    groebner.run();
    let leaks = groebner.get_leaks();

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
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_baz").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g, 3);

    println!("{}", tc);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);

    // Compute the Groebner basis
    groebner.run();
    let leaks = groebner.get_leaks();

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
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_schnorr").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g, 0);

    println!("{}", tc);

    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);

    // Compute the Groebner basis
    groebner.run();
    let leaks = groebner.get_leaks();

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
            g <- gen<G>;
            c <- g * a;
            d <- g * b;
            verify(c == d);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    // Compute transitive closure
    let tc = TransClos::new(g, 0);

    println!("{}", tc);
    // Create an object computing the Groebner basis
    let mut groebner = GroebnerBuilder::new(tc);

    // Compute the Groebner basis
    groebner.run();
    let leaks = groebner.get_leaks();

    if leaks.is_empty() {
        println!("No leaks found");
    } else {
        println!("Leaks found:\n");
        for leak in leaks.iter() {
            println!("{}", leak);
        }
    }
}
