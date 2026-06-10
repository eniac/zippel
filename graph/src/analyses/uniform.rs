use crate::{DQDag, Dag, GOp, Node, Op, QDag, Ref};
use backend::ArkConfig;
use lang::ast::BinOp;
use lang::typ::Distribution;
#[cfg(test)]
use log::debug;
use petgraph::{Direction, graph::NodeIndex, visit::Topo};
use share::{Ctx, Set};
use std::fmt;

#[derive(Clone)]
pub struct UniformityPropagation {
    pub ancestors: Ctx<NodeIndex, Set<NodeIndex>>,
    pub distributions: Ctx<Ref, Distribution>,
}

fn op_ancestors_of<C: ArkConfig>(
    op: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
) -> Set<NodeIndex> {
    match op {
        Op::Ref(r, _) => ancestors.get(&r.node()).cloned().unwrap_or_default(),
        Op::Ram(a, _) => op_ancestors_of(a, ancestors),
        Op::Value(_) => Set::new(),
        Op::Check(op) => op_ancestors_of(op, ancestors),
        Op::Poly(op) => op_ancestors_of(op, ancestors),
        Op::Coef(op) => op_ancestors_of(op, ancestors),
        Op::Reduce(_, v) => op_ancestors_of(v, ancestors),
        Op::HypercubeReduceSelected(p, _, _) => op_ancestors_of(p, ancestors),
        Op::Evaluate(p, _, None) => op_ancestors_of(p, ancestors),
        Op::Evaluate(p, _, Some(x)) => {
            op_ancestors_of(p, ancestors).union(op_ancestors_of(x, ancestors))
        }
        Op::Interpolate(points, evals) => {
            op_ancestors_of(points, ancestors).union(op_ancestors_of(evals, ancestors))
        }
        Op::Ifft(op) => op_ancestors_of(op, ancestors),
        Op::Fft(op) => op_ancestors_of(op, ancestors),
        Op::Mle(op) => op_ancestors_of(op, ancestors),
        Op::Proj(op, _, _) => op_ancestors_of(op, ancestors),
        Op::Random(_, _) => Set::new(),
        Op::Challenge(_, _) => Set::new(),
        Op::Vec(vs) => vs
            .iter()
            .flat_map(|v| op_ancestors_of(v, ancestors))
            .collect(),
        Op::Record(fields) => fields
            .iter()
            .flat_map(|(_, v)| op_ancestors_of(v, ancestors))
            .collect(),
        Op::Pair(a, b, _) | Op::Bin(_, a, b, _) => {
            op_ancestors_of(a, ancestors).union(op_ancestors_of(b, ancestors))
        }
    }
}

fn is_independent<C: ArkConfig>(
    a: &GOp<C>,
    b: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
) -> bool {
    op_ancestors_of(a, ancestors).is_disjoint(&op_ancestors_of(b, ancestors))
}

fn compute_distribution<C: ArkConfig>(
    op: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
    distributions: &Ctx<Ref, Distribution>,
) -> Option<Distribution> {
    match op {
        Op::Value(_) => Some(Distribution::Nonuniform),
        Op::Check(op) => compute_distribution(op, ancestors, distributions),
        Op::Ref(r, _) => distributions.get(r).cloned(),
        Op::Ram(a, _) => compute_distribution(a, ancestors, distributions),
        Op::Poly(a) => compute_distribution(a, ancestors, distributions),
        Op::Coef(op) => compute_distribution(op, ancestors, distributions),
        Op::Evaluate(p, _, None) => compute_distribution(p, ancestors, distributions),
        Op::Evaluate(p, _, Some(x)) => {
            let _dist_p = compute_distribution(p, ancestors, distributions)?;
            let dist_x = compute_distribution(x, ancestors, distributions)?;
            if is_independent(p, x, ancestors) {
                Some(dist_x.mul(&dist_x.inv()))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::HypercubeReduceSelected(p, _, _) => compute_distribution(p, ancestors, distributions),
        Op::Interpolate(points, evals) => {
            let dist_evals = compute_distribution(evals, ancestors, distributions)?;
            let dist_points = compute_distribution(points, ancestors, distributions)?;
            if is_independent(points, evals, ancestors) {
                Some(dist_points.add(&dist_evals))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Ifft(a) => compute_distribution(a, ancestors, distributions),
        Op::Fft(a) => compute_distribution(a, ancestors, distributions),
        Op::Mle(a) => compute_distribution(a, ancestors, distributions),
        Op::Proj(a, _, _) => compute_distribution(a, ancestors, distributions),
        Op::Bin(BinOp::Add, a, b, _) | Op::Bin(BinOp::Concat, a, b, _) => {
            let dist_a = compute_distribution(a, ancestors, distributions)?;
            let dist_b = compute_distribution(b, ancestors, distributions)?;
            if is_independent(a, b, ancestors) {
                Some(dist_a.add(&dist_b))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Sub, a, b, _) | Op::Bin(BinOp::Equ, a, b, _) => {
            let dist_a = compute_distribution(a, ancestors, distributions)?;
            let dist_b = compute_distribution(b, ancestors, distributions)?;
            if is_independent(a, b, ancestors) {
                Some(dist_a.sub(&dist_b))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Mul, a, b, _)
        | Op::Bin(BinOp::And, a, b, _)
        | Op::Bin(BinOp::Dot, a, b, _)
        | Op::Pair(a, b, _) => {
            let dist_a = compute_distribution(a, ancestors, distributions)?;
            let dist_b = compute_distribution(b, ancestors, distributions)?;
            if is_independent(a, b, ancestors) {
                Some(dist_a.mul(&dist_b))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Div, a, b, _) => {
            let dist_a = compute_distribution(a, ancestors, distributions)?;
            let dist_b = compute_distribution(b, ancestors, distributions)?;
            if is_independent(a, b, ancestors) {
                Some(dist_a.mul(&dist_b.inv()))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Rem, _, _, _) | Op::Bin(BinOp::Pow, _, _, _) => {
            Some(Distribution::Nonuniform)
        }
        Op::Vec(vs) => {
            let mut distr = compute_distribution(vs.first().unwrap(), ancestors, distributions)?;
            for v in vs.iter().skip(1) {
                let d = compute_distribution(v, ancestors, distributions)?;
                distr = distr.add(&d);
            }
            Some(distr)
        }
        Op::Record(fields) => {
            if let Some((_, first_field)) = fields.iter().next() {
                compute_distribution(first_field, ancestors, distributions)
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Random(_, b) => Some(if *b {
            Distribution::UniformNonZero
        } else {
            Distribution::Uniform
        }),
        Op::Challenge(_, b) => Some(if *b {
            Distribution::UniformNonZero
        } else {
            Distribution::Uniform
        }),
        Op::Reduce(op, v) => {
            let dist_v = compute_distribution(v, ancestors, distributions)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Concat => Some(dist_v),
                BinOp::Mul | BinOp::And | BinOp::Dot => Some(dist_v),
                _ => Some(Distribution::Nonuniform),
            }
        }
    }
}

impl UniformityPropagation {
    pub fn from_dag<C: ArkConfig>(dag: &QDag<C>) -> Self {
        let mut ancestors: Ctx<NodeIndex, Set<NodeIndex>> = dag
            .node_indices()
            .map(|n| (n, dag.trc(n, Direction::Incoming)))
            .collect();

        for n in dag.node_indices() {
            if dag[n].is_challenge() {
                ancestors.insert(&n, &Set::from([n]));
            }
        }

        let mut distributions: Ctx<Ref, Distribution> = Ctx::new();

        let mut topo = Topo::new(&dag.graph);
        while let Some(n) = topo.next(&dag.graph) {
            match &dag[n] {
                Node::Inp(_) | Node::Rel(_) => {}
                Node::Arg(_, _, _, dist, _) => {
                    distributions.insert(&Ref(n), dist);
                }
                Node::Transcr(op, _) | Node::Op(op, _) => {
                    if let Some(d) = compute_distribution(op, &ancestors, &distributions) {
                        distributions.insert(&Ref(n), &d);
                    }
                }
            }
        }

        Self {
            ancestors,
            distributions,
        }
    }

    pub fn annotate_dag<C: ArkConfig>(&self, dag: &QDag<C>) -> DQDag<C> {
        Dag {
            graph: dag.graph.map(
                |i, node| node.add_annotation(self.find_distribution(i)),
                |_, e| *e,
            ),
            vctx: dag.vctx.clone(),
            transcript_vars: dag.transcript_vars.clone(),
        }
    }

    pub fn find_distribution(&self, r: NodeIndex) -> Distribution {
        self.distributions
            .get(&Ref(r))
            .copied()
            .unwrap_or(Distribution::Nonuniform)
    }
}

impl fmt::Display for UniformityPropagation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "UniformityPropagation")?;
        for (r, d) in self.distributions.iter() {
            writeln!(f, "\t{}: {}", r, d)?;
        }
        writeln!(f, "Ancestors")?;
        for (r, a) in self.ancestors.iter() {
            writeln!(
                f,
                "\t{}: {}",
                r.index(),
                a.iter()
                    .map(|i| i.index().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::UDags;
    use crate::analyses::QualifierPropagation;
    use backend::ArkBls12_381;
    use lang::ast::UModule;
    use petgraph::graph::NodeIndex;
    use share::unwrap;

    #[test]
    fn uniformity_prop() {
        let ex = r#"
            proto foo<F: Field>(private uniform* s: F, public x: F) where true {
                let r = random<F>;
                a <- r * s;
                b <- r * x;
                verify(a == b)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

        let g = QualifierPropagation::from_dag(&gs[0]);
        let up = UniformityPropagation::from_dag(&g);
        let g = up.annotate_dag(&g);

        debug!("{}", up);
        assert!(g.node_count() > 0);
    }

    #[test]
    fn test_uniformity_from_dag_simple() {
        let ex = r#"
            proto simple<F: Field>(private x: F) where true {
                verify(x == x)
            }"#;
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let result = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        assert!(result.node_count() > 0);
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
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let checks = g.find_check();
        assert_eq!(
            checks.len(),
            2,
            "Protocol with two verify statements should have two check nodes"
        );
        let result = UniformityPropagation::from_dag(&g).annotate_dag(&g);

        assert!(result.node_count() > 0);
    }

    #[test]
    fn test_compute_distribution_value() {
        let op = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(42u64)));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_random() {
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Uniform));
    }

    #[test]
    fn test_compute_distribution_random_nonzero() {
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), true);
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::UniformNonZero));
    }

    #[test]
    fn test_compute_distribution_challenge() {
        let op = GOp::<ArkBls12_381>::Challenge(backend::ATyp::scalar(), false);
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Uniform));
    }

    #[test]
    fn test_compute_distribution_challenge_nonzero() {
        let op = GOp::<ArkBls12_381>::Challenge(backend::ATyp::scalar(), true);
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::UniformNonZero));
    }

    #[test]
    fn test_op_ancestors_of_value() {
        let op = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let ancestors = op_ancestors_of(&op, &Ctx::new());
        assert_eq!(ancestors.len(), 0);
    }

    #[test]
    fn test_op_ancestors_of_random() {
        let op = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let ancestors = op_ancestors_of(&op, &Ctx::new());
        assert_eq!(ancestors.len(), 0);
    }

    #[test]
    fn test_is_independent_disjoint() {
        let op1 = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        let op2 = GOp::<ArkBls12_381>::Random(backend::ATyp::scalar(), false);
        assert!(is_independent(&op1, &op2, &Ctx::new()));
    }

    #[test]
    fn test_compute_distribution_poly() {
        use crate::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Poly(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_mle() {
        use crate::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Mle(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_coef() {
        use crate::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Coef(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_fft() {
        use crate::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Fft(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_interpolate() {
        use crate::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Interpolate(mk::<ArkBls12_381>(GOp::index(0)), mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_check() {
        use crate::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Check(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_rem() {
        use crate::mk;
        let a = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(10u64)));
        let b = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(3u64)));
        let op = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            backend::ATyp::scalar(),
        );
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_pow() {
        use crate::mk;
        let a = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(2u64)));
        let b = GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(3u64)));
        let op = Op::Bin(
            BinOp::Pow,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            backend::ATyp::scalar(),
        );
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_vec() {
        use crate::mk;
        let val1 =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let val2 =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(2u64)));
        let op = Op::Vec(vec![mk::<ArkBls12_381>(val1), mk::<ArkBls12_381>(val2)]);
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_find_distribution_default() {
        let up = UniformityPropagation {
            ancestors: Ctx::new(),
            distributions: Ctx::new(),
        };
        let node_idx = NodeIndex::new(0);
        let dist = up.find_distribution(node_idx);
        assert_eq!(dist, Distribution::Nonuniform);
    }

    #[test]
    fn test_uniformity_display_empty() {
        let up = UniformityPropagation {
            ancestors: Ctx::new(),
            distributions: Ctx::new(),
        };
        let s = format!("{}", up);
        assert!(s.contains("UniformityPropagation"));
    }
}
