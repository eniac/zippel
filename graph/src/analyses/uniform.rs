#[cfg(test)]
use log::debug;
use crate::{GOp, Op, Ref, Node, Dag, QDag, DQDag};
use petgraph::{
    graph::NodeIndex,
    visit::EdgeRef,
    Direction,
};
use std::fmt;
use share::{Set, Ctx};
use lang::typ::Distribution;
use lang::ast::BinOp;
use backend::ArkConfig;

/// Which nodes are uniform random distributions
/// Sometimes this is allowed under constraints, for example:
/// a: F, b: F and uniform random means (a*b) is uniform Random
/// iff a != 0, and b != 0 and a \independent b
#[derive(Clone)]
pub struct UniformityPropagation{
    pub ancestors: Ctx<NodeIndex, Set<NodeIndex>>,
    pub distributions: Ctx<Ref, Distribution>,
}

/// Propagate qualifiers [private, public] through the DAG
impl UniformityPropagation {
    fn is_independent<C: ArkConfig>(&self, a: &GOp<C>, b: &GOp<C>) -> bool {
        let a_ancestors = self.op_ancestors(a);
        let b_ancestors = self.op_ancestors(b);
        a_ancestors.is_disjoint(&b_ancestors)
    }

    fn op_ancestors<C: ArkConfig>(&self, op: &GOp<C>) -> Set<NodeIndex> {
        match op {
            Op::Ref(r, _) => self.ancestors.get(&r.node()).cloned().unwrap_or_default(),
            Op::Ram(a, _) => self.op_ancestors(a),
            Op::Value(_) => Set::new(),
            Op::Check(op) => self.op_ancestors(op),
            Op::Poly(op) => self.op_ancestors(op),
            Op::Coef(op) => self.op_ancestors(op),
            Op::Reduce(_, v) => self.op_ancestors(v),
            Op::Eval(p, x) => {
                let p_ancestors = self.op_ancestors(p);
                let x_ancestors = self.op_ancestors(x);
                p_ancestors.union(x_ancestors)
            },
            Op::Ifft(op) => self.op_ancestors(op),
            Op::Fft(op) => self.op_ancestors(op),
            Op::Mle(op) => self.op_ancestors(op),
            Op::Marginalize(op) => self.op_ancestors(op),
            Op::Interpolate0dEval(op, d) =>
                self.op_ancestors(op).union(self.op_ancestors(d)),
            Op::Proj(op, _, _) => self.op_ancestors(op),
            Op::Random(_, _) => Set::new(),
            Op::Challenge(_, _) => Set::new(),
            Op::Vec(vs) => vs.iter().flat_map(|v| self.op_ancestors(v)).collect(),
            Op::Record(fields) => fields.iter().flat_map(|(_, v)| self.op_ancestors(v)).collect(),
            Op::Pair(a, b, _)
            | Op::Bin(_, a, b, _) => {
                let a_ancestors = self.op_ancestors(a);
                let b_ancestors = self.op_ancestors(b);
                a_ancestors.union(b_ancestors)
            },
        }
    }

    fn from_op<C: ArkConfig>(&self, op: &GOp<C>) -> Option<Distribution> {
        let r = match op {
            Op::Value(_) => Some(Distribution::Nonuniform),
            Op::Check(op) => self.from_op(op),
            Op::Ref(r, _) => self.distributions.get(&r)
            .or(self.distributions.iter().find(|(dr, _)| dr.node() == r.node()).map(|dr| dr.1))
            .cloned(),
            Op::Ram(a, _) => self.from_op(a),
            Op::Poly(a) => self.from_op(a),
            Op::Coef(op) => self.from_op(op),
            Op::Eval(p, x) => {
                let _dist_p = self.from_op(p)?;
                let dist_x = self.from_op(x)?;
                if self.is_independent(p, x) {
                    Some(dist_x.mul(&dist_x.inv()))
                } else {
                    Some(Distribution::Nonuniform)
                }
            },
            Op::Ifft(a) => self.from_op(a),
            Op::Fft(a) => self.from_op(a),
            Op::Mle(a) => self.from_op(a),
            Op::Marginalize(a) => self.from_op(a),
            Op::Interpolate0dEval(a, d) => {
                let _ = self.from_op(d)?;
                self.from_op(a)
            },
            Op::Proj(a, _, _) => self.from_op(a),
            Op::Bin(BinOp::Add, a, b, _)
            | Op::Bin(BinOp::Concat, a, b, _) => {
                let dist_a = self.from_op(a)?;
                let dist_b = self.from_op(b)?;
                if self.is_independent(a, b) {
                    Some(dist_a.add(&dist_b))
                } else {
                    Some(Distribution::Nonuniform)
                }
            },
            Op::Bin(BinOp::Sub, a, b, _)
            | Op::Bin(BinOp::Equ, a, b, _) => {
                let dist_a = self.from_op(a)?;
                let dist_b = self.from_op(b)?;
                if self.is_independent(a, b) {
                    Some(dist_a.sub(&dist_b))
                } else {
                    Some(Distribution::Nonuniform)
                }
            },
            Op::Bin(BinOp::Mul, a, b, _)
            | Op::Bin(BinOp::And, a, b, _)
            | Op::Bin(BinOp::Dot, a, b, _)
            | Op::Pair(a, b, _) => {
                let dist_a = self.from_op(a)?;
                let dist_b = self.from_op(b)?;
                if self.is_independent(a, b) {
                    Some(dist_a.mul(&dist_b))
                } else {
                    Some(Distribution::Nonuniform)
                }
            },
            Op::Bin(BinOp::Div, a, b, _) => {
                let dist_a = self.from_op(a)?;
                let dist_b = self.from_op(b)?;
                if self.is_independent(a, b) {
                    Some(dist_a.mul(&dist_b.inv()))
                } else {
                    Some(Distribution::Nonuniform)
                }
            },
            Op::Bin(BinOp::Rem, _, _, _)
            | Op::Bin(BinOp::Pow, _, _, _) =>
                Some(Distribution::Nonuniform),
            Op::Vec(vs) => {
                let mut distr = self.from_op(vs.first().unwrap())?;
                for v in vs.iter().skip(1) {
                    let d = self.from_op(v)?;
                    distr = distr.add(&d);
                }
                Some(distr)
            },
            Op::Record(fields) => {
                if let Some((_, first_field)) = fields.iter().next() {
                    self.from_op(first_field)
                } else {
                    Some(Distribution::Nonuniform)
                }
            },
            Op::Random(_, b) =>
                Some(if *b { Distribution::UniformNonZero } else { Distribution::Uniform }),
            Op::Challenge(_, b) =>
                Some(if *b { Distribution::UniformNonZero } else { Distribution::Uniform }),
            Op::Reduce(op, v) => {
                let dist_v = self.from_op(v)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Concat => Some(dist_v),
                    BinOp::Mul | BinOp::And | BinOp::Dot => Some(dist_v),
                    _ => Some(Distribution::Nonuniform),
                }
            },
        };
        r
    }

    pub fn new() -> Self {
        Self { ancestors: Ctx::new(), distributions: Ctx::new() }
    }

    fn find_distribution(&self, r: NodeIndex) -> Distribution {
        self.distributions.iter()
        .find(|(dr, _)| dr.node() == r)
        .map(|(_, d)| *d)
        .unwrap_or_else(|| Distribution::Nonuniform)
    }

    pub fn from_dag<C: ArkConfig>(&mut self, dag: &QDag<C>) -> DQDag<C> {
        // Collect the ancestors of each node
        let mut ancestors: Ctx<NodeIndex, Set<NodeIndex>> =
            dag.node_indices()
            .map(|n| (n, dag.trc(n, Direction::Incoming)))
            .collect();

        // Challenge nodes are modeled as random oracle outputs —
        // they are independent of their DAG ancestors.
        for n in dag.node_indices() {
            if dag[n].is_challenge() {
                ancestors.insert(&n, &Set::from([n]));
            }
        }

        self.ancestors = ancestors;

        let inp = dag.input_node();
        let mut worklist = vec![inp];
        for n in dag.op_nodes() {
            if let Some(d) = self.from_op(&dag[n].clone().into_op()) {
                self.distributions.insert(&Ref::Node(n), &d);
                worklist.push(n.into());
            }
        }

        while let Some(n) = worklist.pop() {
            if self.distributions.iter().any(|(r, _)| r.node() == n) {
                continue;
            }

            match &dag[n] {
                Node::Inp(_, args) | Node::Rel(_, args) =>
                    for arg in args {
                        self.distributions.insert(&arg.reference, &arg.distribution);
                    },
                Node::Transcr(op, _)
                | Node::Op(op, _) => {
                    self.from_op(op)
                    .and_then(|d| self.distributions.insert(&Ref::Node(n), &d));
                }
            }

            // Add parent neighbors to worklist
            for e in dag.graph.edges_directed(n, Direction::Outgoing) {
                // Add neighbors to worklist
                worklist.push(e.target());
            }
        }

        Dag { graph: dag.graph.map(
            |i, node|
                node.add_annotation(self.find_distribution(i)),
            |_, e| e.clone()), vctx: dag.vctx.clone(), transcript_vars: dag.transcript_vars.clone() }
    }
}

impl fmt::Display for UniformityPropagation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UniformityPropagation\n")?;
        for (r, d) in self.distributions.iter() {
            write!(f, "\t{}: {}\n", r, d)?;
        }
        write!(f, "Ancestors\n")?;
        for (r, a) in self.ancestors.iter() {
            write!(f, "\t{}: {}\n", r.index(), a.iter().map(|i| i.index().to_string()).collect::<Vec<_>>().join(", "))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lang::ast::UModule;
    use backend::ArkBls12_381;
    use crate::analyses::QualifierPropagation;
    use crate::{UDags, mk};
    use share::unwrap;
    use petgraph::graph::NodeIndex;

    #[test]
    #[ignore]
    fn uniformity_prop() {
        let ex = r#"
            proto foo<F: Field>(private uniform* s: F, public x: F) where true {
                let r = random<F>;
                a <- r * s;
                b <- r * x;
                verify(a == b)
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let g = up.from_dag(&g);

        debug!("{}", up);
        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_uniformity_propagation_new() {
        let up = UniformityPropagation::new();
        assert_eq!(up.ancestors.len(), 0);
        assert_eq!(up.distributions.len(), 0);
    }

    #[test]
    fn test_uniformity_from_op_value() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(42u64)));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_random() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Uniform));
    }

    #[test]
    fn test_uniformity_from_op_random_nonzero() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), true);
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::UniformNonZero));
    }

    #[test]
    fn test_uniformity_from_op_challenge() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Challenge(backend::ATyp::scalar(), false);
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Uniform));
    }

    #[test]
    fn test_uniformity_from_op_challenge_nonzero() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Challenge(backend::ATyp::scalar(), true);
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::UniformNonZero));
    }

    #[test]
    fn test_uniformity_op_ancestors_value() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let ancestors = up.op_ancestors(&op);
        assert_eq!(ancestors.len(), 0);
    }

    #[test]
    fn test_uniformity_op_ancestors_random() {
        let up = UniformityPropagation::new();
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let ancestors = up.op_ancestors(&op);
        assert_eq!(ancestors.len(), 0);
    }

    #[test]
    fn test_uniformity_is_independent_disjoint() {
        let up = UniformityPropagation::new();
        let op1 = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let op2 = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        assert!(up.is_independent(&op1, &op2));
    }

    #[test]
    fn test_uniformity_from_op_poly() {
        let up = UniformityPropagation::new();
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Poly(mk::<ArkBls12_381>(inner));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_mle() {
        let up = UniformityPropagation::new();
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Mle(mk::<ArkBls12_381>(inner));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_coef() {
        let up = UniformityPropagation::new();
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Coef(mk::<ArkBls12_381>(inner));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_fft() {
        let up = UniformityPropagation::new();
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Fft(mk::<ArkBls12_381>(inner));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_ifft() {
        let up = UniformityPropagation::new();
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Ifft(mk::<ArkBls12_381>(inner));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_check() {
        let up = UniformityPropagation::new();
        let inner = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Check(mk::<ArkBls12_381>(inner));
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_rem() {
        let up = UniformityPropagation::new();
        let a = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(10u64)));
        let b = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(3u64)));
        let op = Op::Bin(BinOp::Rem, mk::<ArkBls12_381>(a), mk::<ArkBls12_381>(b), backend::ATyp::scalar());
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_pow() {
        let up = UniformityPropagation::new();
        let a = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(2u64)));
        let b = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(3u64)));
        let op = Op::Bin(BinOp::Pow, mk::<ArkBls12_381>(a), mk::<ArkBls12_381>(b), backend::ATyp::scalar());
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_from_op_vec() {
        let up = UniformityPropagation::new();
        let val1 = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let val2 = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(2u64)));
        let op = Op::Vec(vec![mk::<ArkBls12_381>(val1), mk::<ArkBls12_381>(val2)]);
        let dist = up.from_op(&op);
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_uniformity_find_distribution_default() {
        let up = UniformityPropagation::new();
        let node_idx = NodeIndex::new(0);
        let dist = up.find_distribution(node_idx);
        assert_eq!(dist, Distribution::Nonuniform);
    }

    #[test]
    fn test_uniformity_from_dag_simple() {
        let ex = r#"
            proto simple<F: Field>(private x: F) where true {
                verify(x == x)
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut up = UniformityPropagation::new();
        let result = up.from_dag(&g);

        assert!(result.node_count() > 0);
    }

    #[test]
    fn test_uniformity_display_empty() {
        let up = UniformityPropagation::new();
        let s = format!("{}", up);
        assert!(s.contains("UniformityPropagation"));
    }

    #[test]
    fn test_uniformity_from_dag_multiple_checks() {
        let ex = r#"
            proto two_checks<F: Field>(private x: F, private y: F) where true {
                let r = random<F>;
                a <- r * x;
                b <- r * y;
                verify(a == a);
                verify(b == b)
            }"#;
        let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let checks = g.find_check();
        assert_eq!(checks.len(), 2, "Protocol with two verify statements should have two check nodes");
        let mut up = UniformityPropagation::new();
        let result = up.from_dag(&g);

        assert!(result.node_count() > 0);
    }
}
