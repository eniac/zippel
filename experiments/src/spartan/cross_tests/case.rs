use crate::cross::{Challenges, Direction};
use lang::id::Vid;
use zippel::runtime::Challenger;

// ark-spartan's older PCS omits libspartan's random-base challenge. Its
// proof is the rho=1 specialization; do not consume a native draw for it.
struct SpartanChallenges {
    sequence: Challenges,
    draws: usize,
    pcs_batching_index: usize,
}
impl SpartanChallenges {
    fn new(m: usize) -> Self {
        Self {
            sequence: Challenges::default(),
            draws: 0,
            pcs_batching_index: 9 * m + 6,
        }
    }
}
impl Challenger<C> for SpartanChallenges {
    fn instance(&mut self, _: &V) {}
    fn message(&mut self, _: &V) {}
    fn challenge(&mut self) -> V {
        let index = self.draws;
        self.draws += 1;
        if !HAS_PCS_BATCHING && index == self.pcs_batching_index {
            Value::Scalar(<F as backend::Field>::one())
        } else {
            <Challenges as Challenger<C>>::challenge(&mut self.sequence)
        }
    }
}

fn group_values(values: Vec<V>) -> V {
    Value::vec_g1(
        values
            .into_iter()
            .map(|v| match v {
                Value::G1(g) => *g,
                _ => unreachable!("group conversion produces G1 values"),
            })
            .collect(),
    )
}

fn scalar_vec(fs: &[NativeScalar]) -> V {
    Value::vec_scalar(
        fs.iter()
            .map(|f| match scalar(f) {
                Value::Scalar(f) => f,
                _ => unreachable!(),
            })
            .collect(),
    )
}
fn group_vec(gs: &[NativeGroup]) -> V {
    group_values(gs.iter().map(group).collect())
}

fn append_sumcheck(out: &mut Vec<V>, sc: &SumcheckProof) {
    for i in 0..sc.proofs.len() {
        let p = &sc.proofs[i];
        out.extend([
            group(&sc.comm_polys[i]),
            group(&sc.comm_evals[i]),
            group(&p.delta),
            group(&p.beta),
            scalar_vec(&p.z),
            scalar(&p.z_delta),
            scalar(&p.z_beta),
        ]);
    }
}

fn as_zippel(p: &NativeNizk) -> Vec<V> {
    let p = &p.r1cs_sat_proof;
    let mut out = vec![group_vec(&p.comm_vars.C)];
    append_sumcheck(&mut out, &p.sc_proof_phase1);
    let (a, b, c, prod) = &p.claims_phase2;
    let (know, product) = &p.pok_claims_phase2;
    out.extend([
        group(c),
        group(&know.alpha),
        scalar(&know.z1),
        scalar(&know.z2),
        group(a),
        group(b),
        group(prod),
        group(&product.alpha),
        group(&product.beta),
        group(&product.delta),
    ]);
    out.extend(product.z.iter().map(scalar));
    out.extend([
        group(&p.proof_eq_sc_phase1.alpha),
        scalar(&p.proof_eq_sc_phase1.z),
    ]);
    append_sumcheck(&mut out, &p.sc_proof_phase2);
    out.push(group(&p.comm_vars_at_ry));
    let eval = &p.proof_eval_vars_at_ry.proof;
    let bullet = &eval.bullet_reduction_proof;
    for (l, r) in bullet.L_vec.iter().zip(&bullet.R_vec) {
        out.extend([group(l), group(r)]);
    }
    out.extend([
        group(&eval.delta),
        group(&eval.beta),
        scalar(&eval.z1),
        scalar(&eval.z2),
        group(&p.proof_eq_sc_phase2.alpha),
        scalar(&p.proof_eq_sc_phase2.z),
    ]);
    out
}

struct Messages<'a>(std::slice::Iter<'a, V>);
impl Messages<'_> {
    fn group(&mut self) -> NativeGroup {
        native_group(self.0.next().expect("group message"))
    }
    fn scalar(&mut self) -> NativeScalar {
        native_scalar(self.0.next().expect("scalar message"))
    }
    fn scalars(&mut self) -> Vec<NativeScalar> {
        match self.0.next().expect("scalar vector") {
            Value::VecScalar(fs) => fs
                .iter()
                .map(|f| native_scalar(&Value::Scalar(*f)))
                .collect(),
            v => panic!("expected scalar vector, got {v}"),
        }
    }
    fn groups(&mut self) -> Vec<NativeGroup> {
        match self.0.next().expect("group vector") {
            Value::Vec(vs) => vs.iter().map(native_group).collect(),
            Value::VecG1(gs) => gs.iter().map(|g| native_group(&Value::g1(*g))).collect(),
            Value::VecG1Affine(gs) => gs
                .iter()
                .map(|g| native_group(&Value::g1_affine(*g)))
                .collect(),
            v => panic!("expected group vector, got {v}"),
        }
    }
    fn sumcheck(&mut self, m: usize) -> SumcheckProof {
        let (mut comm_polys, mut comm_evals, mut proofs) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..m {
            comm_polys.push(self.group());
            comm_evals.push(self.group());
            proofs.push(DotProductProof {
                delta: self.group(),
                beta: self.group(),
                z: self.scalars(),
                z_delta: self.scalar(),
                z_beta: self.scalar(),
            });
        }
        SumcheckProof {
            comm_polys,
            comm_evals,
            proofs,
        }
    }
}

fn points(m: usize) -> (Vec<NativeScalar>, Vec<NativeScalar>) {
    let mut seq = Challenges::default();
    let mut next = || native_scalar(&<Challenges as Challenger<C>>::challenge(&mut seq));
    for _ in 0..m {
        next();
    }
    let rx = (0..m)
        .map(|_| {
            let r = next();
            for _ in 0..3 {
                next();
            }
            r
        })
        .collect();
    // Knowledge, product and equality proofs, then the A/B/C coefficients.
    for _ in 0..6 {
        next();
    }
    let ry = (0..m)
        .map(|_| {
            let r = next();
            for _ in 0..3 {
                next();
            }
            r
        })
        .collect();
    (rx, ry)
}

fn as_native(messages: &[V], m: usize) -> NativeNizk {
    let mut r = Messages(messages.iter());
    let comm_vars = PolyCommitment { C: r.groups() };
    let sc_proof_phase1 = r.sumcheck(m);
    let c = r.group();
    let know = KnowledgeProof {
        alpha: r.group(),
        z1: r.scalar(),
        z2: r.scalar(),
    };
    let (a, b, prod) = (r.group(), r.group(), r.group());
    let product = ProductProof {
        alpha: r.group(),
        beta: r.group(),
        delta: r.group(),
        z: std::array::from_fn(|_| r.scalar()),
    };
    let proof_eq_sc_phase1 = EqualityProof {
        alpha: r.group(),
        z: r.scalar(),
    };
    let sc_proof_phase2 = r.sumcheck(m);
    let comm_vars_at_ry = r.group();
    let (mut ls, mut rs) = (Vec::new(), Vec::new());
    for _ in 0..m - 1 - (m - 1) / 2 {
        ls.push(r.group());
        rs.push(r.group());
    }
    let proof_eval_vars_at_ry = PolyEvalProof {
        proof: DotProductProofLog {
            bullet_reduction_proof: BulletReductionProof {
                L_vec: ls,
                R_vec: rs,
            },
            delta: r.group(),
            beta: r.group(),
            z1: r.scalar(),
            z2: r.scalar(),
        },
    };
    let proof_eq_sc_phase2 = EqualityProof {
        alpha: r.group(),
        z: r.scalar(),
    };
    assert!(r.0.next().is_none(), "unconsumed Zippel proof messages");
    NativeNizk {
        r1cs_sat_proof: R1csProof {
            comm_vars,
            sc_proof_phase1,
            claims_phase2: (a, b, c, prod),
            pok_claims_phase2: (know, product),
            proof_eq_sc_phase1,
            sc_proof_phase2,
            comm_vars_at_ry,
            proof_eval_vars_at_ry,
            proof_eq_sc_phase2,
        },
        r: points(m),
    }
}

#[test]
fn native_prove_then_zippel_verify() {
    cross_verify(Direction::NativeToZippel);
}
#[test]
fn zippel_prove_then_native_verify() {
    cross_verify(Direction::ZippelToNative);
}

fn cross_verify(direction: Direction) {
    for m in [3usize, 4, 5] {
        let (mut inputs, products) = super::super::make_inputs::<C>(m);
        let (inst, gens, vars, io) = setup(m, &mut inputs, &products);
        let (prover, verifier) = crate::cross::compile::<C>("spartan", &[("M", m)]);
        let [az, bz, cz] = products.products();
        for (name, v) in [("az", az), ("bz", bz), ("cz", cz)] {
            inputs.insert(Vid::from(name), Value::vec_scalar(v));
        }
        match direction {
            Direction::NativeToZippel => {
                let native = NativeNizk::prove(&inst, vars, &io, &gens, &mut Challenges::default());
                assert!(
                    native
                        .verify(&inst, &io, &mut Challenges::default(), &gens)
                        .is_ok()
                );
                let proof = as_zippel(&native);
                assert!(
                    verifier
                        .verify_with(
                            proof.clone(),
                            crate::lend(&inputs),
                            &mut SpartanChallenges::new(m)
                        )
                        .unwrap(),
                    "M={m}: Zippel rejects native proof"
                );
                let mut wrong = proof;
                let last = wrong.len() - 1;
                wrong[last] = super::super::tests::tampered(&wrong[last]);
                assert!(
                    !verifier
                        .verify_with(wrong, crate::lend(&inputs), &mut SpartanChallenges::new(m))
                        .unwrap(),
                    "M={m}: Zippel accepts corrupted native proof"
                );
            }
            Direction::ZippelToNative => {
                let proof = prover
                    .prove_with(crate::lend(&inputs), &mut SpartanChallenges::new(m))
                    .unwrap();
                let native = as_native(&proof, m);
                assert!(
                    native
                        .verify(&inst, &io, &mut Challenges::default(), &gens)
                        .is_ok(),
                    "M={m}: native rejects Zippel proof"
                );
                let mut wrong = proof;
                let last = wrong.len() - 1;
                wrong[last] = super::super::tests::tampered(&wrong[last]);
                assert!(
                    as_native(&wrong, m)
                        .verify(&inst, &io, &mut Challenges::default(), &gens)
                        .is_err(),
                    "M={m}: native accepts corrupted Zippel proof"
                );
            }
        }
    }
}
