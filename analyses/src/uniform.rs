use backend::ArkConfig;
use graph::{DQDag, Dag, GOp, Node, Op, QDag, Ref};
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

#[cfg(test)]
fn op_ancestors_of<C: ArkConfig>(
    op: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
) -> Set<NodeIndex> {
    op_ancestors_of_loops(op, ancestors, &[])
}

fn op_ancestors_of_loops<C: ArkConfig>(
    op: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
    loops: &[Set<NodeIndex>],
) -> Set<NodeIndex> {
    match op {
        Op::Ref(r, _) => ancestors.get(&r.node()).cloned().unwrap_or_default(),
        Op::Ram(a, _) => op_ancestors_of_loops(a, ancestors, loops),
        Op::Value(_) => Set::new(),
        Op::Check(op) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Poly(op) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Coef(op) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Reduce(_, v) => op_ancestors_of_loops(v, ancestors, loops),
        Op::LoopParam(i, _) => loops.get(*i).cloned().unwrap_or_default(),
        Op::Map(d, b) => {
            let dd = op_ancestors_of_loops(d, ancestors, loops);
            let mut next = loops.to_vec();
            next.push(dd);
            op_ancestors_of_loops(b, ancestors, &next)
        }
        Op::ReduceMap(_, d, b) => {
            let dd = op_ancestors_of_loops(d, ancestors, loops);
            let mut next = loops.to_vec();
            next.push(dd);
            op_ancestors_of_loops(b, ancestors, &next)
        }
        Op::Evaluate(p, _, None) => op_ancestors_of_loops(p, ancestors, loops),
        Op::Evaluate(p, _, Some(x)) => op_ancestors_of_loops(p, ancestors, loops)
            .union(op_ancestors_of_loops(x, ancestors, loops)),
        Op::Interpolate(points, evals) => op_ancestors_of_loops(points, ancestors, loops)
            .union(op_ancestors_of_loops(evals, ancestors, loops)),
        Op::Ifft(op) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Fft(op) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Mle(op) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Proj(op, _, _) => op_ancestors_of_loops(op, ancestors, loops),
        Op::Random(_, _) => Set::new(),
        Op::Challenge(_, _) => Set::new(),
        Op::Vec(vs) => vs
            .iter()
            .flat_map(|v| op_ancestors_of_loops(v, ancestors, loops))
            .collect(),
        Op::Record(fields) => fields
            .iter()
            .flat_map(|(_, v)| op_ancestors_of_loops(v, ancestors, loops))
            .collect(),
        Op::Pair(a, b, _) | Op::Bin(_, a, b, _) => op_ancestors_of_loops(a, ancestors, loops)
            .union(op_ancestors_of_loops(b, ancestors, loops)),
    }
}

#[cfg(test)]
fn is_independent<C: ArkConfig>(
    a: &GOp<C>,
    b: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
) -> bool {
    is_independent_loops(a, b, ancestors, &[])
}

fn is_independent_loops<C: ArkConfig>(
    a: &GOp<C>,
    b: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
    loops: &[Set<NodeIndex>],
) -> bool {
    op_ancestors_of_loops(a, ancestors, loops)
        .is_disjoint(&op_ancestors_of_loops(b, ancestors, loops))
}

fn compute_distribution<C: ArkConfig>(
    op: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
    distributions: &Ctx<Ref, Distribution>,
) -> Option<Distribution> {
    compute_distribution_loops(op, ancestors, distributions, &[], &[])
}

/// `dist_loops[i]` is the distribution of enclosing loop binder `i`;
/// `anc_loops[i]` its ancestor set (fed to `is_independent_loops`).
fn compute_distribution_loops<C: ArkConfig>(
    op: &GOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
    distributions: &Ctx<Ref, Distribution>,
    dist_loops: &[Distribution],
    anc_loops: &[Set<NodeIndex>],
) -> Option<Distribution> {
    match op {
        Op::Value(_) => Some(Distribution::Nonuniform),
        Op::Check(op) => {
            compute_distribution_loops(op, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Ref(r, _) => distributions.get(r).cloned(),
        Op::Ram(a, _) => {
            compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Poly(a) => {
            compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Coef(op) => {
            compute_distribution_loops(op, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::LoopParam(i, _) => Some(
            dist_loops
                .get(*i)
                .copied()
                .unwrap_or(Distribution::Nonuniform),
        ),
        Op::Map(d, b) => {
            let dd =
                compute_distribution_loops(d, ancestors, distributions, dist_loops, anc_loops)?;
            let da = op_ancestors_of_loops(d, ancestors, anc_loops);
            let mut next_dist = dist_loops.to_vec();
            next_dist.push(dd);
            let mut next_anc = anc_loops.to_vec();
            next_anc.push(da);
            compute_distribution_loops(b, ancestors, distributions, &next_dist, &next_anc)
        }
        Op::ReduceMap(_, d, b) => {
            compute_reduce_map_generic(d, b, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Evaluate(p, _, None) => {
            compute_distribution_loops(p, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Evaluate(p, _, Some(x)) => {
            let _dist_p =
                compute_distribution_loops(p, ancestors, distributions, dist_loops, anc_loops)?;
            let dist_x =
                compute_distribution_loops(x, ancestors, distributions, dist_loops, anc_loops)?;
            if is_independent_loops(p, x, ancestors, anc_loops) {
                Some(dist_x.mul(&dist_x.inv()))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Interpolate(points, evals) => {
            let dist_evals =
                compute_distribution_loops(evals, ancestors, distributions, dist_loops, anc_loops)?;
            let dist_points = compute_distribution_loops(
                points,
                ancestors,
                distributions,
                dist_loops,
                anc_loops,
            )?;
            if is_independent_loops(points, evals, ancestors, anc_loops) {
                Some(dist_points.add(&dist_evals))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Ifft(a) => {
            compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Fft(a) => {
            compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Mle(a) => {
            compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Proj(a, _, _) => {
            compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)
        }
        Op::Bin(BinOp::Add, a, b, _) | Op::Bin(BinOp::Concat, a, b, _) => {
            let dist_a =
                compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)?;
            let dist_b =
                compute_distribution_loops(b, ancestors, distributions, dist_loops, anc_loops)?;
            if is_independent_loops(a, b, ancestors, anc_loops) {
                Some(dist_a.add(&dist_b))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Sub, a, b, _) | Op::Bin(BinOp::Equ, a, b, _) => {
            let dist_a =
                compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)?;
            let dist_b =
                compute_distribution_loops(b, ancestors, distributions, dist_loops, anc_loops)?;
            if is_independent_loops(a, b, ancestors, anc_loops) {
                Some(dist_a.sub(&dist_b))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Mul, a, b, _)
        | Op::Bin(BinOp::And, a, b, _)
        | Op::Bin(BinOp::Dot, a, b, _)
        | Op::Pair(a, b, _) => {
            let dist_a =
                compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)?;
            let dist_b =
                compute_distribution_loops(b, ancestors, distributions, dist_loops, anc_loops)?;
            if is_independent_loops(a, b, ancestors, anc_loops) {
                Some(dist_a.mul(&dist_b))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Div, a, b, _) => {
            let dist_a =
                compute_distribution_loops(a, ancestors, distributions, dist_loops, anc_loops)?;
            let dist_b =
                compute_distribution_loops(b, ancestors, distributions, dist_loops, anc_loops)?;
            if is_independent_loops(a, b, ancestors, anc_loops) {
                Some(dist_a.mul(&dist_b.inv()))
            } else {
                Some(Distribution::Nonuniform)
            }
        }
        Op::Bin(BinOp::Rem, _, _, _) | Op::Bin(BinOp::Pow, _, _, _) => {
            Some(Distribution::Nonuniform)
        }
        Op::Vec(vs) => {
            let mut distr = compute_distribution_loops(
                vs.first().unwrap(),
                ancestors,
                distributions,
                dist_loops,
                anc_loops,
            )?;
            for v in vs.iter().skip(1) {
                let d =
                    compute_distribution_loops(v, ancestors, distributions, dist_loops, anc_loops)?;
                distr = distr.add(&d);
            }
            Some(distr)
        }
        Op::Record(fields) => {
            if let Some((_, first_field)) = fields.iter().next() {
                compute_distribution_loops(
                    first_field,
                    ancestors,
                    distributions,
                    dist_loops,
                    anc_loops,
                )
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
            let dist_v =
                compute_distribution_loops(v, ancestors, distributions, dist_loops, anc_loops)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Concat => Some(dist_v),
                BinOp::Mul | BinOp::And | BinOp::Dot => Some(dist_v),
                _ => Some(Distribution::Nonuniform),
            }
        }
    }
}

/// Generic (non-fast-path) reduce-map / map distribution: push the domain's
/// distribution and ancestor set as the loop binder, then analyze the body.
/// Mirrors the old unrolled `Vec`+`Reduce` where each element's
/// `Ram(domain, i)` carried the domain's distribution and ancestors.
fn compute_reduce_map_generic<C: ArkConfig>(
    d: &graph::HOp<C>,
    b: &graph::HOp<C>,
    ancestors: &Ctx<NodeIndex, Set<NodeIndex>>,
    distributions: &Ctx<Ref, Distribution>,
    dist_loops: &[Distribution],
    anc_loops: &[Set<NodeIndex>],
) -> Option<Distribution> {
    let dd = compute_distribution_loops(d, ancestors, distributions, dist_loops, anc_loops)?;
    let da = op_ancestors_of_loops(d, ancestors, anc_loops);
    let mut next_dist = dist_loops.to_vec();
    next_dist.push(dd);
    let mut next_anc = anc_loops.to_vec();
    next_anc.push(da);
    compute_distribution_loops(b, ancestors, distributions, &next_dist, &next_anc)
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
    use crate::QualifierPropagation;
    use backend::ArkBls12_381;
    use graph::UDags;
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
        use graph::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Poly(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_mle() {
        use graph::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Mle(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_coef() {
        use graph::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Coef(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_fft() {
        use graph::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Fft(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_interpolate() {
        use graph::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Interpolate(mk::<ArkBls12_381>(GOp::index(0)), mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_check() {
        use graph::mk;
        let inner =
            GOp::<ArkBls12_381>::Value(backend::Value::Scalar(ark_bls12_381::Fr::from(1u64)));
        let op = Op::Check(mk::<ArkBls12_381>(inner));
        let dist = compute_distribution(&op, &Ctx::new(), &Ctx::new());
        assert_eq!(dist, Some(Distribution::Nonuniform));
    }

    #[test]
    fn test_compute_distribution_rem() {
        use graph::mk;
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
        use graph::mk;
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
        use graph::mk;
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
