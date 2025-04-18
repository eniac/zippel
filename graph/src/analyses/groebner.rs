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
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Zero, BigInteger, PrimeField};

/// Abstract interpretation of each Zippel expression into the boolean field.
/// If we know an Bit we can also know something about the underlying value.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Bit {
    Value(bool),
    Vec(Vec<Bit>),
    Add(Box<Bit>, Box<Bit>),
    Mul(Box<Bit>, Box<Bit>),
    Neg(Box<Bit>),
    Var(Vid),
    Underscore(usize),
}

impl Bit {
    pub fn vec(v: Vec<Bit>) -> Self {
        Bit::Vec(v.iter().map(|v| v.clone()).collect())
    }
    pub fn add(a: Bit, b: Bit) -> Self {
        Bit::Add(Box::new(a), Box::new(b))
    }
    pub fn sub(a: Bit, b: Bit) -> Self {
        Bit::Add(Box::new(a), Box::new(b.neg()))
    }
    pub fn mul(a: Bit, b: Bit) -> Self {
        Bit::Mul(Box::new(a), Box::new(b))
    }
    pub fn var(v: Vid) -> Self {
        Bit::Var(v.clone())
    }
    pub fn underscore(n: usize) -> Self {
        Bit::Underscore(n)
    }
    pub fn neg(self) -> Self {
        match self {
            Bit::Value(b) => Bit::Value(!b),
            Bit::Vec(v) => Bit::Vec(v.into_iter().map(|v| v.neg()).collect()),
            Bit::Add(box a, box b) => Bit::add(a.neg(), b.neg()),
            Bit::Neg(box a) => a,
            op => Bit::Neg(Box::new(op)),
        }
    }
}

/// Abstract interpretation of each Zippel value into the boolean field.
impl<C: ArkConfig> From<Value<C>> for Bit {
    fn from(value: Value<C>) -> Self {
        match value {
            Value::Bool(b) => Bit::Value(b),
            Value::Index(i) => Bit::Value(!i == 0),
            Value::Scalar(s) =>
                Bit::Value(!s.is_zero()),
            Value::G1(g) => Bit::Value(!g.into_affine().is_zero()),
            Value::G2(g) => Bit::Value(!g.into_affine().is_zero()),
            Value::G1Affine(g) => Bit::Value(!g.is_zero()),
            Value::G2Affine(g) => Bit::Value(!g.is_zero()),
            Value::GT(g) => Bit::Value(!g.is_zero()),
            v => {
                let mut v = v;
                Bit::Vec(v.into_vec_mut().iter().map(|v| v.clone().into()).collect())
            }
        }
    }
}

/// Construct a Groebner basis from a graph, by first taking the transitive
/// closure of the graph, building a set of equations, and then computing the Groebner basis. Non-polynomial
/// terms are replaced with variables.
pub struct Groebner<C: ArkConfig> {
    equ: Vec<Bit>,
    npterms: Ctx<usize, Op<C>>,
    vars: Set<Vid>
}

impl<C: ArkConfig> Groebner<C> {
    pub fn new() -> Self {
        Groebner {
            equ: Vec::new(),
            npterms: Ctx::new(),
            vars: Set::new(),
        }
    }

    pub fn from_dag<A: Clone>(dag: Dag<C, A>) -> Self {
        let mut groebner = Groebner::new();

        // Transitive closure
        let clos = TransClos::new(dag).clos();

        for (v, op) in clos.into_iter() {
            // Make an op out of the variable [v]
            let ov = Op::Underscore(NodeIndex::new(v), op.typ());

            groebner.add_equ(ov, op);
        }
    }

    /// Add an equation to the system
    pub fn add_equ(&mut self, l: Bit, r: Bit) {
        self.equ.push(Bit::sub(l, r));
    }

    pub fn add_def(&mut self, def: Bit) {
        let v = Vid::fresh("v", &mut self.vars);
        // Add the definition to the set of equations
        self.npterms.insert(&, &def);
        self.max_node += 1;
    }

    pub fn from_op(&mut self, op: Op<C>) -> Bit {
        match op {
            // Polynomial operations
            Op::Bin(BinOp::Add | BinOp::And, box a, box b, typ) => {
                let oa = self.from_op(a)?;
                let ob = self.from_op(b)?;
                self.add_def(Bit::add(oa, ob));
            },
            Op::Bin(BinOp::Sub, box a, box b, typ) => {
                let oa = self.from_op(a)?;
                let ob = self.from_op(b)?;
                Some(Bit::sub(oa, ob))
            },
            Op::Bin(BinOp::Mul | BinOp::Or, box a, box b, typ) => {
                let oa = self.from_op(a)?;
                let ob = self.from_op(b)?;
                Some(Bit::mul(oa, ob))
            },
            Op::Bin(BinOp::Div, box a, box b, typ) => {
                let oa = self.from_op(a)?;
                let ob = self.from_op(b)?;
                self.max_node += 1;
                // Create a new variable
                let ov = Bit::underscore(self.max_node);
                // Add ov * ob = oa
                self.add_equ(Bit::mul(ov, ob), oa);
                None
            },
            Op::Bin(BinOp::Rem, box a, box b, typ) => {
                let oa = self.from_op(a);
                let ob = self.from_op(b);
                // Create a two new variables, the remainder and quotient
                let or = Bit::Var(Vid::fresh("r", &mut self.vars));
                let oq = Bit::Var(Vid::fresh("q", &mut self.vars));
                // Add oq * ob + or = oa
                self.add_equ(Bit::add(Bit::mul(oq, ob), or), oa);
                oa
            },
            Op::Bin(BinOp::Equ, box a, box b, typ) => {
                let oa = self.from_op(a);
                let ob = self.from_op(b);
                self.add_equ(oa, ob);
                Bit::Value(true) // ???
            },
            Op::Bin(op @ (BinOp::Pow | BinOp::Dot), box a, box b, typ) => {
                self.max_node += 1;
                self.npterms.insert(&self.max_node, &Op::bin(op, a, b, typ));
                // Create a new variable
                let ov = Bit::underscore(self.max_node);
                // Add to non-polymomial terms
                ov
            },
            // Unsure what to do with these, I think from the view of information
            // theory those are identities?
            Op::Coef(box a) | Op::Eval(box a) => self.from_op(a),
            Op::Not(box a) => self.from_op(a).neg(),
            Op::Ram(box a, _) => self.from_op(a),
            Op::Vec(vs) =>
                Bit::Vec(vs.into_iter().map(|v| self.from_op(v)).collect()),
            Op::Underscore(n, _) => Bit::Underscore(n),
            Op::Var(v, n, _) => Bit::Var(v),
            Op::Value(v) => v.into(),
            Op::Range(r) => Bit::Vec(r.into_iter().map(|v| Bit::Value(v.is_zero())).collect()),
            Op::Check(box op) => self.from_op(op),
        }
    }
}


