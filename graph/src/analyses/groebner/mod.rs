pub mod buchberger;
pub use buchberger::GroebnerBasis;

pub mod monomial;
pub use monomial::{Monomial, ElimTerm, GrevLexTerm};
pub mod sparsepoly;
pub use sparsepoly::SparsePolynomial;

use crate::{GOp, Op, Ref};
use lang::ast::BinOp;
use crate::DQDag;
use crate::analyses::TransClos;
use crate::pref::PRef;

use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::{Value, ATyp, ArkConfig, ArkScalarOps};
use backend::op::HasOpFactory;
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

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    pub fn new() -> Self {
        Self {
            basis: GroebnerBasis::empty(0),
            np: Ctx::new(),
            pl: Ctx::new(),
            args: Set::new(),
        }
    }

    pub fn vars(&self) -> Set<PRef> {
        self.np.keys().union(self.pl.keys())
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

    #[allow(dead_code)]
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

    /// Remap all PRef variables in the basis, pl, np, and args using a mapping function.
    /// Used when combining Gröbner bases from different subgraphs that have
    /// different node index namespaces.
    pub fn remap_vars<F: Fn(&PRef) -> PRef>(&mut self, f: &F) {
        // Remap basis polynomials
        self.basis.basis = self.basis.basis.iter().map(|p|
            p.clone().flat_map_vars(&|v| SparsePolynomial::var(&f(&v)))
        ).collect();

        // Remap pl context
        self.pl = self.pl.iter().map(|(k, v)| {
            let new_k = f(k);
            let new_v = v.clone().flat_map_vars(&|v| SparsePolynomial::var(&f(&v)));
            (new_k, new_v)
        }).collect();

        // Remap np context
        self.np = self.np.iter().map(|(k, v)| (f(k), v.clone())).collect();

        // Remap args
        self.args = self.args.iter().map(f).collect();
    }

    /// Merge another builder's basis, polynomial definitions, and non-polynomial
    /// definitions into this builder.
    pub fn merge(&mut self, other: &Self) {
        for p in other.basis.iter() {
            self.basis.push(p.clone());
        }
        for (k, v) in other.pl.iter() {
            self.pl.insert(k, v);
        }
        for (k, v) in other.np.iter() {
            self.np.insert(k, v);
        }
    }

    fn to_poly_value(&mut self, v: &Value<C>) -> Vec<SparsePolynomial<C::F, T>> {
        match v {
            Value::Scalar(s) => vec![SparsePolynomial::lit(&s)],
            Value::Bool(b) =>
                vec![SparsePolynomial::lit(&if *b { C::F::one() } else { C::F::zero() })],
            Value::Index(i) => vec![SparsePolynomial::lit(&C::FOps::from_usize(*i))],
            Value::Vec(v) => 
                v.into_iter()
                .flat_map(|v| self.to_poly_value(v)).collect(),
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
            _ => unreachable!("Unsupported value: {}", v),
        }
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
            Op::Value(v) => self.to_poly_value(v),
            Op::Vec(v) =>
                v.into_iter().flat_map(|v| self.to_poly(v)).collect(),
            Op::Ram(a, b) => {
                match (a.get(), b.get()) {
                    (Op::Ref(n, _), Op::Value(v)) => {
                        let pf = self.find_ref(&n);
                        match v {
                            Value::Index(i) =>
                                vec![SparsePolynomial::var(&pf.with_index(*i))],
                            _ => vec![SparsePolynomial::var(&pf)],
                        }
                    },
                    // Dynamic indexing, overapproximate
                    (a, _) => self.to_poly(a),
                }
            },
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) =>
                self.to_poly(a).into_iter()
                .zip(self.to_poly(b).into_iter())
                .map(|(a, b)| a + b)
                .collect(),
            Op::Bin(BinOp::Sub, a, b, _) =>
                self.to_poly(a).into_iter()
                .zip(self.to_poly(b).into_iter())
                .map(|(a, b)| a - b)
                .collect(),
            Op::Bin(BinOp::Mul, a, b, _) =>
                self.to_poly(a).into_iter()
                .zip(self.to_poly(b).into_iter())
                .map(|(a, b)| a * b)
                .collect(),
            Op::Bin(BinOp::Dot, a, b, _) => {
                vec![self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .map(|(a, b)| a * b)
                    .sum()
                ]
            },
            Op::Reduce(BinOp::Add, v) => {
                vec![self.to_poly(v).into_iter().sum()]
            },
            Op::Reduce(BinOp::Mul, v) => {
                let polys = self.to_poly(v);
                let mut iter = polys.into_iter();
                if let Some(first) = iter.next() {
                    vec![iter.fold(first, |acc, p| acc * p)]
                } else {
                    vec![]
                }
            },
            _ => vec![]
        }
    }
}

impl<C: ArkConfig + HasOpFactory, T: Monomial> GroebnerBuilder<C, T> {
    pub fn add_input(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_input(g);
        self.add_tc(tc);
    }

    pub fn add_relation(&mut self, g: &DQDag<C>) {
        let tc = TransClos::from_relation(g);
        self.add_tc(tc);
    }

    fn add_tc(&mut self, tc: TransClos<C>) {
        self.args.append(tc.args.clone().into_iter());

        for (i, op) in tc.clos.into_iter() {
            self.add_op(i, op);
        }
    }

    /// Convert an operation to a polynomial and add it to the context
    fn add_op(&mut self, pr: PRef, op: GOp<C>) {
        let op_for_div = op.clone(); // needed for Div arm which references the whole op
        match op {
            Op::Ref(r, typ) => {
                let ref_poly = self.to_poly(&Op::Ref(r, typ));
                for (i, p) in ref_poly.into_iter().enumerate() {
                    let pf = pr.clone().with_index(i);
                    self.pl.insert(&pf, &p);
                    self.basis.push(p - SparsePolynomial::var(&pf));
                }
            }
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, a, b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a + &b));
                        self.basis.push(a + b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Sub, a, b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a - &b));
                        self.basis.push(a - b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Mul, a, b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.pl.insert(&pf, &(&a * &b));
                        self.basis.push(a * b - SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Dot, a, b, _) => {
                let sum = self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .map(|(a, b)| a * b)
                    .sum();
                self.pl.insert(&pr, &sum);
                self.basis.push(sum - SparsePolynomial::var(&pr))
            },
            Op::Bin(BinOp::Div, ref a, ref b, _) =>
                self.to_poly(a).into_iter()
                    .zip(self.to_poly(b).into_iter())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let pf = pr.clone().with_index(i);
                        self.np.insert(&pf, &Op::ram(op_for_div.clone(), Op::index(i)));
                        self.basis.push(a - b * SparsePolynomial::var(&pf));
                    }),
            Op::Bin(BinOp::Equ, a, b, _) =>
                self.to_poly(&a).into_iter()
                    .zip(self.to_poly(&b).into_iter())
                    .for_each(|(a, b)| {
                        self.pl.insert(&pr, &(&a - &b));
                        self.pl.insert(&pr, &SparsePolynomial::lit(&C::F::zero()));
                        self.basis.push(a - b);
                        self.basis.push(SparsePolynomial::var(&pr));
                    }),
            Op::Check(a) => self.add_op(pr, a.get().clone()),
            Op::Challenge(t, b) => { let op = Op::Challenge(t, b); self.np.insert(&pr, &op); },
            Op::Random(t, b) => { let op = Op::Random(t, b); self.np.insert(&pr, &op); },
            Op::Ifft(a) => { let op = Op::Ifft(a); self.np.insert(&pr, &op); },
            Op::Fft(a) => { let op = Op::Fft(a); self.np.insert(&pr, &op); },
            Op::Vec(vs) => {
                for (i, v) in vs.into_iter().enumerate() {
                    let pf = pr.with_index(i);
                    self.add_op(pf, v.get().clone());
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

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBls12_381;
    use backend::op::mk;

    #[test]
    fn test_groebner_builder_new() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        assert_eq!(builder.basis.len(), 0);
        assert_eq!(builder.np.len(), 0);
        assert_eq!(builder.pl.len(), 0);
        assert_eq!(builder.args.len(), 0);
    }

    #[test]
    fn test_groebner_builder_vars_empty() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let vars = builder.vars();
        assert_eq!(vars.len(), 0);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_scalar() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        use ark_bls12_381::Fr;
        
        let val = Value::Scalar(Fr::from(42u64));
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_true() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        
        let val = Value::Bool(true);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_bool_false() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        
        let val = Value::Bool(false);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_index() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        
        let val = Value::Index(5);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_scalar() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        use ark_bls12_381::Fr;
        
        let val = Value::VecScalar(vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_bool() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        
        let val = Value::VecBool(vec![true, false, true]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value_vec_index() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        
        let val = Value::VecIndex(vec![0, 1, 2]);
        let poly = builder.to_poly_value(&val);
        assert_eq!(poly.len(), 3);
    }

    #[test]
    fn test_groebner_builder_to_poly_value() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        use ark_bls12_381::Fr;
        
        let val = Value::Scalar(Fr::from(10u64));
        let result = builder.to_poly(&Op::Value(val));
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_groebner_builder_to_poly_vec() {
        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        use backend::Value;
        use ark_bls12_381::Fr;
        
        let ops = vec![
            mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(1u64)))),
            mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(2u64)))),
        ];
        let result = builder.to_poly(&Op::Vec(ops));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_groebner_builder_display_empty() {
        let builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let s = format!("{}", builder);
        assert!(!s.is_empty());
    }

    #[test]
    fn test_remap_vars_identity() {
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use backend::ATyp;
        use petgraph::graph::NodeIndex;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(NodeIndex::new(0), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());
        let pref_b = PRef::from_node(NodeIndex::new(1), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());

        // a + b - 0
        let poly = SparsePolynomial::var(&pref_a) + SparsePolynomial::var(&pref_b);
        builder.basis.push(poly.clone());
        builder.args.insert(pref_a.clone());
        builder.args.insert(pref_b.clone());

        // Identity remap should be a no-op
        builder.remap_vars(&|p| p.clone());
        assert_eq!(builder.basis.basis.len(), 1);
        assert_eq!(builder.basis.basis[0], poly);
    }

    #[test]
    fn test_remap_vars_rename() {
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use backend::ATyp;
        use petgraph::graph::NodeIndex;
        use lang::id::Vid;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_n0 = PRef::from_node(NodeIndex::new(0), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());
        let pref_n1 = PRef::from_node(NodeIndex::new(1), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());
        let pref_x = PRef::from_var(Vid("x".into()), NodeIndex::new(10), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());
        let pref_y = PRef::from_var(Vid("y".into()), NodeIndex::new(11), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());

        // poly: n0 + n1
        let poly = SparsePolynomial::var(&pref_n0) + SparsePolynomial::var(&pref_n1);
        builder.basis.push(poly);
        builder.pl.insert(&pref_n0, &SparsePolynomial::var(&pref_n0));
        builder.args.insert(pref_n0.clone());
        builder.args.insert(pref_n1.clone());

        // Remap n0→x, n1→y
        builder.remap_vars(&|p| {
            if p.node() == NodeIndex::new(0) { pref_x.clone() }
            else if p.node() == NodeIndex::new(1) { pref_y.clone() }
            else { p.clone() }
        });

        // Basis should now use x + y
        let expected = SparsePolynomial::var(&pref_x) + SparsePolynomial::var(&pref_y);
        assert_eq!(builder.basis.basis[0], expected);
        // pl should be remapped
        assert!(builder.pl.contains(&pref_x));
        assert!(!builder.pl.contains(&pref_n0));
        // args should be remapped
        assert!(builder.args.contains(&pref_x));
        assert!(builder.args.contains(&pref_y));
    }

    #[test]
    fn test_remap_vars_preserves_polynomial_count() {
        use crate::PRef;
        use lang::typ::{Qualifier, Distribution};
        use backend::ATyp;
        use petgraph::graph::NodeIndex;
        use lang::id::Vid;

        let mut builder = GroebnerBuilder::<ArkBls12_381, GrevLexTerm>::new();
        let pref_a = PRef::from_node(NodeIndex::new(0), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());
        let pref_b = PRef::from_node(NodeIndex::new(1), ATyp::scalar(), 0, Qualifier::Private, Distribution::default());

        builder.basis.push(SparsePolynomial::var(&pref_a) + SparsePolynomial::var(&pref_b));
        builder.basis.push(SparsePolynomial::var(&pref_a) * SparsePolynomial::var(&pref_b));

        let pref_c = PRef::from_var(Vid("c".into()), NodeIndex::new(5), ATyp::scalar(), 0, Qualifier::Public, Distribution::default());

        builder.remap_vars(&|p| {
            if p.node() == NodeIndex::new(0) { pref_c.clone() } else { p.clone() }
        });

        assert_eq!(builder.basis.basis.len(), 2);
        // First poly: c + b, second: c * b
        assert!(builder.basis.basis[0].contains(&pref_c));
        assert!(builder.basis.basis[1].contains(&pref_c));
        assert!(!builder.basis.basis[0].contains(&pref_a));
    }
}
