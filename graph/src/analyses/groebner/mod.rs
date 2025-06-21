pub mod buchberger;
pub use buchberger::GroebnerBasis;

pub mod monomial;
pub use monomial::{Monomial, ElimTerm, GrevLexTerm};
pub mod sparsepoly;
pub use sparsepoly::SparsePolynomial;

use crate::{GOp, Op, Ref};
use lang::typ::{Distribution, Qualifier, Range};
use lang::ast::BinOp;
use crate::DQDag;
use crate::{analyses::TransClos, StaticAnalysis};
use crate::pref::PRef;

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
pub struct GroebnerBuilder<C: ArkConfig, T: Monomial> {
    pub basis: GroebnerBasis<C::F, T>,
    pub np: Ctx<PRef, GOp<C>>,
    pub pl: Ctx<PRef, SparsePolynomial<C::F, T>>,
    pub args: Set<PRef>,
}

impl<C: ArkConfig, T: Monomial> GroebnerBuilder<C, T> {
    pub fn new() -> Self {
        Self {
            basis: GroebnerBasis::empty(0),
            np: Ctx::new(),
            pl: Ctx::new(),
            args: Set::new(),
        }
    }

    pub fn add_input(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_input(g);
        self.add_tc(tc);
    }

    pub fn add_relation(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_relation(g);
        self.add_tc(tc);
    }

    pub fn vars(&self) -> Set<PRef> {
        self.np.keys().union(self.pl.keys())
    }

    fn add_tc(&mut self, tc: TransClos<C>) {
        self.args.append(tc.args.clone().into_iter());
        
        for (i, op) in tc.clos.into_iter() {
            self.add_op(i, op);
        }
    }

    pub fn find_ref(&self, r: &Ref) -> PRef {
        self.vars()
        .into_iter()
        .find(|v| v.reference == *r)
        .or_else(|| self.args.iter()
            .find(|v| v.var() == r.var() && v.is_var())
            .cloned())
        .unwrap_or_else(|| {
            panic!("Reference {} not found in context \n{}", r, self);
        })
    }

    /// Filter out variables that satisfy the predicate
    pub fn eliminate_var<F: Fn(&PRef) -> bool>(&mut self, f: &F) {
        self.basis.eliminate_var(f);
        self.pl.retain(|p, _| !f(p));
        self.np.retain(|p, _| !f(p));
    }

    pub fn eliminate_monomial<F: Fn(&T) -> bool>(&mut self, f: &F) {
        self.basis.eliminate_monomial(f);
        let vars = self.basis.vars();
        self.pl.retain(|p, _| vars.contains(p));
        self.np.retain(|p, _| vars.contains(p));
    }

    pub fn inline<F: Fn(&PRef) -> bool>(&mut self, f: F) {
        for p in self.basis.iter_mut() {
            *p = p.clone().flat_map_vars(&|v|
                if f(&v) || !self.pl.contains(&v) {
                    SparsePolynomial::var(&v)
                } else {
                    self.pl[v].clone()
                }
            );
        }
    }

    /// Compute Groebner basis using Buchberger algorithm,
    pub fn run(&mut self) {
        // Compute the Groebner basis using Buchberger algorithm
        self.basis = self.basis.clone().buchberger_and_reduce();
    }

    /// This function converts an operation to a vector of sparse polynomial expressions,
    /// exploding vectors where possible.
    fn to_poly(&mut self, op: &GOp<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match op {
            Op::Ref(v, typ) => {
                let pf = self.find_ref(&v);
                match typ {
                    ATyp::Vec(box t, n) =>
                        (0..*n).into_iter()
                            .map(|i| {
                                let mut pf = pf.clone();
                                pf.index = i;
                                pf.typ = t.clone();
                                SparsePolynomial::var(&pf)
                            })
                            .collect::<Vec<_>>(),
                    ATyp::Uni(n) =>
                        (0..*n).into_iter()
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
                    Value::Bool(b) => vec![SparsePolynomial::lit(&if *b { C::F::one() } else { C::F::zero() })],
                    Value::Index(i) => vec![SparsePolynomial::lit(&C::FOps::from_usize(*i))],
                    Value::VecBool(v) =>
                        v.into_iter()
                        .map(|b| SparsePolynomial::lit(&if *b { C::F::one() } else { C::F::zero() }))
                        .collect::<Vec<_>>(),
                    Value::VecScalar(v) =>
                        v.into_iter()
                        .map(|s| SparsePolynomial::lit(s))
                        .collect::<Vec<_>>(),
                    Value::VecIndex(v) =>
                        v.into_iter()
                        .map(|i| SparsePolynomial::lit(&C::FOps::from_usize(*i)))
                        .collect::<Vec<_>>(),
                    Value::Range(r) =>
                        r.into_iter()
                        .map(|i| SparsePolynomial::lit(&C::FOps::from_usize(i)))
                        .collect::<Vec<_>>(),
                    Value::Vec(v) => 
                        v.into_iter()
                        .flat_map(|v| self.to_poly(&Op::value(v)))
                        .collect(),
                    _ => vec![]
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
                    Value::Index(i) => vec![SparsePolynomial::var(&pf.with_index(*i))],
                    _ => vec![SparsePolynomial::var(&pf)],
                }
            },
            // Dynamic indexing, overapproximate
            Op::Ram(box a, _) => self.to_poly(a),
            Op::Bin(BinOp::Add | BinOp::And, box a, box b, _) =>
                self.to_poly(a).into_iter()
                .zip(self.to_poly(b).into_iter())
                .map(|(a, b)| a + b)
                .collect(),
            Op::Bin(BinOp::Sub, box a, box b, _) =>
                self.to_poly(a).into_iter()
                .zip(self.to_poly(b).into_iter())
                .map(|(a, b)| a - b)
                .collect(),
            Op::Bin(BinOp::Mul, box a, box b, _) =>
                self.to_poly(a).into_iter()
                .zip(self.to_poly(b).into_iter())
                .map(|(a, b)| a * b)
                .collect(),
            Op::Bin(BinOp::Dot, box a, box b, _) => {
                vec![self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .map(|(a, b)| a * b)
                    .sum()
                ]
            },
            _ => vec![]
        }
    }

    /// Convert an operation to a polynomial and add it to the context
    fn add_op(&mut self, pr: PRef, op: GOp<C>) {
        match op {
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, box a, box b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a + &b));
                        self.basis.push(a + b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Sub, box a, box b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a - &b));
                        self.basis.push(a - b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Mul, box a, box b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a * &b));
                        self.basis.push(a * b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Dot, box a, box b, _) => {
                let sum = self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .map(|(a, b)| a * b)
                    .sum();
                self.pl.insert(&pr, &sum);
                self.basis.push(sum - SparsePolynomial::var(&pr))
            },
            Op::Bin(BinOp::Div, box ref a, box ref b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.np.insert(&pf, &Op::ram(op.clone(), Op::index(i)));
                        self.basis.push(a - b * SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Equ, box a, box b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .for_each(|(a, b)| {
                        self.pl.insert(&pr, &(&a - &b));
                        self.pl.insert(&pr, &SparsePolynomial::lit(&C::F::zero()));
                        self.basis.push(a - b);
                        self.basis.push(SparsePolynomial::var(&pr));
                    }),
            Op::Check(box a) => self.add_op(pr, a),
            Op::Challenge(_, _) => { self.np.insert(&pr, &op); },
            Op::Random(_, _) => { self.np.insert(&pr, &op); },
            Op::Coef(_) => { self.np.insert(&pr, &op); },
            Op::Eval(_) => { self.np.insert(&pr, &op); },
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pf = pr.with_index(i);
                    self.add_op(pf, v);
                }
            },
            op => { self.np.insert(&pr, &op); },
        }
    }
}

impl<'a, C, D, A, T> Pretty<'a, D, A> for GroebnerBuilder<C, T>
where
    C: ArkConfig,
    T: Monomial,
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
            allocator.text("Basis: "),
            allocator.hardline(),
            allocator.intersperse(
                self.basis.into_iter().map(|p| p.pretty(allocator).indent(8)),
                allocator.hardline(),
            ),
            allocator.hardline(),
            allocator.hardline(),
            allocator.text("NP definitions: "),
            allocator.hardline(),
            allocator.intersperse(
                self.np.into_iter().map(|(r, op)|
                    allocator.text(r.verbose())
                        .append(allocator.text(": "))
                        .append(op.pretty(allocator)).indent(8)),
                allocator.hardline(),
            )
        ])
    }

    fn is_nil(&self) -> bool {
        self.basis.is_empty() && self.np.is_empty()
    }
}

impl<C: ArkConfig, T: Monomial> fmt::Display for GroebnerBuilder<C, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <GroebnerBuilder<C, T> as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
