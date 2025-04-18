use crate::{Op, Node, Dag, UDag, Dep};
use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::EdgeRef,
    Graph,
    Direction,
};
use lang::id::{Fresh, Vid};
use lang::ast::{BinOp, CArg};
use crate::analyses::{TransClos, Principal};
use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use backend::{Value, ATyp, ArkConfig};
use std::hash::{DefaultHasher, Hash};
use std::fmt;
use std::ops::Neg;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Zero, BigInteger, PrimeField};

use symbolica::{
    atom::{Atom, AtomCore, Num, Symbol},
    coefficient::Coefficient,
    domains::{finite_field::Z2, finite_field::Zp64, Ring},
    parse,
    poly::{groebner::GroebnerBasis, polynomial::MultivariatePolynomial, LexOrder},
    symbol
};

/// Abstract interpretation of each Zippel expression into the boolean field (F2).
/// If v = 0 -> bit(v) = false, otherwise bit(v) = true
/// This is used to construct a Groebner basis from the graph as polynomials over
/// the boolean field.
/// Construct a Groebner basis from a graph, by first taking the transitive
/// closure of the graph, building a set of equations of polynomials. Non-polynomial
/// terms are replaced with variables in [npterms].
pub struct Groebner<C: ArkConfig> {
    equ: Vec<MultivariatePolynomial<Z2, u8>>,
    z2: Z2,
    npterms: Ctx<usize, Op<C>>,
    vctx: Ctx<Vid, ATyp>,
    uctx: Set<usize>,
}

impl<C: ArkConfig> Groebner<C> {
    pub fn new<A: Clone>(tc: TransClos<C, A>) -> Self {
        let mut s = Groebner {
            equ: Vec::new(),
            z2: Z2::new(),
            npterms: Ctx::new(),
            vctx: Ctx::new(),
            uctx: tc.closure().iter().map(|(i, _)| *i).collect(),
        };

        for (i, op) in tc.closure().iter() {
            s.from_op(*i, op.clone());
        }
        s
    }

    pub fn compute(&self, print_stats: bool) -> GroebnerBasis<Z2, u8, LexOrder> {
        GroebnerBasis::new(&self.equ, print_stats)
    }

    fn to_z2(&self, value: &Value<C>) -> Atom {
        if value.is_zero() {
            parse!("0").unwrap()
        } else {
            parse!("1").unwrap()
        }
    }

    fn new_uvar(&mut self) -> Atom {
        if let Some(i) = self.uctx.clone().last() {
            self.uctx.insert(i + 1);
            symbol!(format!("#{}", i + 1)).into()
        } else {
            self.uctx.insert(0);
            symbol!(format!("#{}", 0)).into()
        }
    }

    fn to_atom(&mut self, i: usize, op: Op<C>) -> Atom {
        match &op {
            Op::Var(v, _, t) => {
                self.vctx.insert(v, t);
                symbol!(v.to_string()).into()
            },
            Op::Underscore(n, _) => {
                self.uctx.insert(n.index());
                symbol!(format!("#{}", n.index())).into()
            },
            Op::Range(r) =>
                if r.len() == 1 && r.contains(0) {
                    parse!("0").unwrap()
                } else {
                    parse!("1").unwrap()
                },
            Op::Value(v) =>
                self.to_z2(v),
            _ => unreachable!("Unsupported operation: {}", op),
        }
    }

    fn add_equ(&mut self, a: Atom, b: Atom) {
        // Add the equation to the set
        let pa = a.to_polynomial(&Z2::new(), None);
        let pb = b.to_polynomial(&Z2::new(), None).neg();
        self.equ.push(pa + pb);
    }

    fn from_op(&mut self, i: usize, op: Op<C>) {
        match op {
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, box a, box b, _) => {
                let oa = self.to_atom(i, a);
                let ob = self.to_atom(i, b);
                let v: Atom = symbol!(format!("#{}", i)).into();
                self.add_equ(v, oa + ob);
            },
            Op::Bin(BinOp::Sub, box a, box b, _) => {
                let oa = self.to_atom(i, a);
                let ob = self.to_atom(i, b);
                let v: Atom = symbol!(format!("#{}", i)).into();
                self.add_equ(v, oa - ob);
            },
            Op::Bin(BinOp::Mul | BinOp::Or | BinOp::Dot, box a, box b, _) => {
                let oa = self.to_atom(i, a);
                let ob = self.to_atom(i, b);
                let v: Atom = symbol!(format!("#{}", i)).into();
                self.add_equ(v, oa * ob);
            },
            Op::Bin(BinOp::Div, box a, box b, _) => {
                let oa = self.to_atom(i, a);
                let ob = self.to_atom(i, b);
                // Create a new variable
                let v = self.new_uvar();
                // Add v * ob = oa
                self.add_equ(v * ob, oa);
            },
            Op::Bin(BinOp::Rem, box a, box b, _) => {
                let oa = self.to_atom(i, a);
                let ob = self.to_atom(i, b);
                // Create a new variables
                let vq = self.new_uvar();
                let vr = self.new_uvar();
                // Add vq * ob + vr = oa
                self.add_equ(vq * ob + vr, oa);
            },
            Op::Bin(BinOp::Equ, box a, box b, _) => {
                let oa = self.to_atom(i, a);
                let ob = self.to_atom(i, b);
                // Add oa = ob
                self.add_equ(oa, ob);
            },
            // Unsure what to do with these, I think from the view of information
            // theory those are identities?
            Op::Coef(box a) | Op::Eval(box a) | Op::Check(box a) => self.from_op(i, a),
            Op::Not(box a) => {
                let oa = self.to_atom(i, a);
                let v = self.new_uvar();
                let one = parse!("1").unwrap();
                // v = 1 - a;
                self.add_equ(v, one - oa);
            },
            op => {
                // Create a new variable for an NP term
                self.npterms.insert(&i, &op);
            }
        }
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
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_poly").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc.closure());
    println!("Public nodes: {}", tc.public());

    // Create an object computing the Groebner basis
    let groebner = Groebner::new(tc);

    // Compute the Groebner basis
    let basis = groebner.compute(true);

    println!("Polynomial equations: ");
    for eq in groebner.equ.iter() {
        println!("\t{}", eq);
    }

    println!("Groebner basis: ");
    for eq in basis.system {
        println!("\t{}", eq);
    }

    println!("NP Variables: ");
    for (i, op) in groebner.npterms.iter() {
        println!("\t#{} = {}", i, op);
    }
}

