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
pub struct GroebnerBuilder<C: ArkConfig> {
    equ: Vec<MultivariatePolynomial<Z2, u8>>,
    npterms: Ctx<usize, Op<C>>,
    vars: Set<Vid>,
    uctx: Set<usize>,
    public: Set<String>,
    private: Set<String>,
}

impl<C: ArkConfig> GroebnerBuilder<C> {
    pub fn new<A: Clone>(tc: TransClos<C, A>) -> Self {
        unsafe {
            std::env::set_var("SYMBOLICA_HIDE_BANNER", "1");
        }
        let mut s = GroebnerBuilder {
            equ: Vec::new(),
            npterms: Ctx::new(),
            vars: Set::new(),
            uctx: tc.closure().iter().map(|(i, _)| *i).collect(),
            public: tc.public,
            private: tc.private,
        };

        for (i, op) in tc.clos.iter() {
            s.from_op(*i, op.clone());
        }
        s
    }

    pub fn max_node(&self) -> usize {
        self.uctx.iter().map(|i| *i).max().unwrap_or(0)
    }

    pub fn compute(&self, print_stats: bool) -> GroebnerBasis<Z2, u8, LexOrder> {
        GroebnerBasis::new(&self.equ, print_stats)
    }

    pub fn print_leaks(&self) {
        let groebner = self.compute(false);

        let npterms_str =
            self.npterms.iter().map(|(i, v)| (format!("#{}", i), v.clone())).collect::<Ctx<_, _>>();

        for p in groebner.system.iter() {
            println!("{} = 0", p);
        }

        // Create a set of polynomials that leak information
        let leaks =
            groebner.system.into_iter().filter(|p| {
                // find the non-zero exponent variables
                let vars = p.get_vars_ref();
                let mut non_zero_vars = Set::new();
                for m in p.into_iter() {
                    vars.iter().zip(m.exponents)
                        .filter(|(_, e)| **e != 0)
                        .for_each(|(v, _)| {
                            non_zero_vars.insert(v.to_string());
                        });
                }

                // Check if the polynomial contains both public and private variables
                non_zero_vars.iter().all(|v|
                    self.public.contains(&v.to_string())
                    || self.private.contains(&v.to_string().into()) // contain private variables
                    || npterms_str.get(v).map(|op|      // or NP terms that leak private variables
                        self.private.iter().any(|p| op.leaks(&p.clone().into()))).unwrap_or(false)
                )
                && (non_zero_vars.iter().any(|v|
                    self.private.contains(&v.to_string())           // contain private variables
                    || npterms_str.get(v).map(|op|      // or NP terms that leak private variables
                        self.private.iter().any(|p| op.leaks(&p.clone().into()))).unwrap_or(false)
                ))
            }).collect::<Vec<_>>();


        let msg =
            if leaks.is_empty() {
                " No leaks found in Groebner basis "
            } else {
                " Found leaks in the Groebner basis "
            };

        let private_str = self.private.iter().cloned().collect::<Vec<_>>().join(", ");
        let public_str = self.public.iter().cloned().collect::<Vec<_>>().join(", ");

        println!("================================================");
        println!(" {} ", msg);
        println!("================================================");
        println!("Public variables: {}", public_str);
        println!("Private variables: {}", private_str);
        println!("NP variables: {}", npterms_str);
        println!("================================================");
        for p in leaks {
            println!("R({}): {} = 0", private_str, p);
        }
        println!("================================================");
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

    fn to_atom(&mut self, op: Op<C>) -> Atom {
        match &op {
            Op::Var(v, _, _) => {
                self.vars.insert(v.clone());
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
            Op::Ram(_, _) => {
                let n = self.max_node() + 1;
                self.uctx.insert(n);
                self.npterms.insert(&n, &op);
                symbol!(format!("#{}", n)).into()
            },
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
                let oa = self.to_atom(a);
                let ob = self.to_atom(b);
                let v: Atom = symbol!(format!("#{}", i)).into();
                self.add_equ(v, oa + ob);
            },
            Op::Bin(BinOp::Sub, box a, box b, _) => {
                let oa = self.to_atom(a);
                let ob = self.to_atom(b);
                let v: Atom = symbol!(format!("#{}", i)).into();
                self.add_equ(v, oa - ob);
            },
            Op::Bin(BinOp::Mul | BinOp::Or | BinOp::Dot, box a, box b, _) => {
                let oa = self.to_atom(a);
                let ob = self.to_atom(b);
                let v: Atom = symbol!(format!("#{}", i)).into();
                self.add_equ(v, oa * ob);
            },
            Op::Bin(BinOp::Div, box a, box b, _) => {
                let oa = self.to_atom(a);
                let ob = self.to_atom(b);
                // Create a new variable
                let v = self.new_uvar();
                // Add v * ob = oa
                self.add_equ(v * ob, oa);
            },
            Op::Bin(BinOp::Rem, box a, box b, _) => {
                let oa = self.to_atom(a);
                let ob = self.to_atom(b);
                // Create a new variables
                let vq = self.new_uvar();
                let vr = self.new_uvar();
                // Add vq * ob + vr = oa
                self.add_equ(vq * ob + vr, oa);
            },
            Op::Bin(BinOp::Equ, box a, box b, _) => {
                let oa = self.to_atom(a);
                let ob = self.to_atom(b);
                // Add oa = ob
                self.add_equ(oa, ob);
            },
            // Unsure what to do with these, I think from the view of information
            // theory those are identities?
            Op::Coef(box a) | Op::Eval(box a) | Op::Check(box a) => self.from_op(i, a),
            Op::Not(box a) => {
                let oa = self.to_atom(a);
                let v = self.new_uvar();
                let one = parse!("1").unwrap();
                // v = 1 - a;
                self.add_equ(v, one - oa);
            },
            Op::Underscore(_, _) => {},
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

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let g = unwrap!(UDag::<ArkBls12_381>::from_module(m));

    g.write_pdf("groebner_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });
    // Compute transitive closure
    let tc = TransClos::new(g);

    println!("Transitive closure: {}", tc.closure());

    // Create an object computing the Groebner basis
    let groebner = GroebnerBuilder::new(tc);

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

    println!("Transitive closure: {}", tc.closure());

    // Create an object computing the Groebner basis
    let groebner = GroebnerBuilder::new(tc);

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

    println!("Transitive closure: {}", tc.closure());

    // Create an object computing the Groebner basis
    let groebner = GroebnerBuilder::new(tc);

    // Compute the Groebner basis and print leaks
    groebner.print_leaks();
}
