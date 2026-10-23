//! Both native Spartan implementations verify Zippel proofs and vice versa.

mod ark {
    const HAS_PCS_BATCHING: bool = false;
    use crate::ark_spartan_upstream as native;
    use backend::{ArkCurve25519 as C, Backend, Value};
    type G = <C as Backend>::G1;
    type F = <C as Backend>::F;
    type V = Value<C>;
    type NativeNizk = native::NIZK<G>;
    type NativeInstance = native::Instance<F>;
    type NativeGens = native::NIZKGens<G>;
    type NativeVars = native::VarsAssignment<F>;
    type NativeInputs = native::InputsAssignment<F>;
    type NativeGroup = G;
    type NativeScalar = F;
    type R1csProof = native::r1csproof::R1CSProof<G>;
    type SumcheckProof = native::sumcheck::ZKSumcheckInstanceProof<G>;
    type PolyCommitment = native::dense_mlpoly::PolyCommitment<G>;
    type PolyEvalProof = native::dense_mlpoly::PolyEvalProof<G>;
    type KnowledgeProof = native::nizk::KnowledgeProof<G>;
    type ProductProof = native::nizk::ProductProof<G>;
    type EqualityProof = native::nizk::EqualityProof<G>;
    type DotProductProof = native::nizk::DotProductProof<G>;
    type DotProductProofLog = native::nizk::DotProductProofLog<G>;
    type BulletReductionProof = native::nizk::bullet::BulletReductionProof<G>;

    fn group(g: &G) -> V {
        Value::g1(*g)
    }
    fn native_group(v: &V) -> G {
        match v {
            Value::G1(g) => **g,
            Value::G1Affine(g) => (**g).into(),
            _ => panic!("expected group element, got {v}"),
        }
    }
    fn scalar(f: &F) -> V {
        Value::Scalar(*f)
    }
    fn native_scalar(v: &V) -> F {
        match v {
            Value::Scalar(f) => *f,
            _ => panic!("expected scalar, got {v}"),
        }
    }

    fn setup(
        m: usize,
        inputs: &mut std::collections::HashMap<lang::id::Vid, V>,
        products: &super::super::MatVec<F>,
    ) -> (NativeInstance, NativeGens, NativeVars, NativeInputs) {
        let n = 1 << m;
        let nw = n / 2;
        let inst = NativeInstance::new(
            n,
            nw,
            nw - 1,
            &products.mats[0],
            &products.mats[1],
            &products.mats[2],
        )
        .unwrap();
        let vars = NativeVars::new(&products.z[..nw]).unwrap();
        let io = NativeInputs::new(&products.z[nw + 1..]).unwrap();
        assert!(inst.is_sat(&vars, &io).unwrap());
        let gens = NativeGens::new(n, nw, nw - 1);
        let pc = &gens.gens_r1cs_sat.gens_pc.gens;
        let sc = &gens.gens_r1cs_sat.gens_sc;
        inputs.extend(
            [
                (
                    "g_vec_w",
                    group_values(pc.gens_n.G.iter().map(group).collect()),
                ),
                ("g_1", group(&pc.gens_1.G[0])),
                ("h_1", group(&pc.gens_1.h)),
                ("g_3", group_values(sc.gens_3.G.iter().map(group).collect())),
                ("h_3", group(&sc.gens_3.h)),
                ("g_4", group_values(sc.gens_4.G.iter().map(group).collect())),
                ("h_4", group(&sc.gens_4.h)),
            ]
            .map(|(name, value)| (Vid::from(name), value)),
        );
        (inst, gens, vars, io)
    }

    include!("case.rs");
}

mod libspartan {
    const HAS_PCS_BATCHING: bool = true;
    use crate::libspartan_upstream as native;
    use backend::{Backend, DalekRistretto as C, Field, Group, Value};
    use curve25519_dalek::ristretto::CompressedRistretto;
    type F = <C as Backend>::F;
    type G = <C as Backend>::G1;
    type V = Value<C>;
    type NativeNizk = native::NIZK;
    type NativeInstance = native::Instance;
    type NativeGens = native::NIZKGens;
    type NativeVars = native::VarsAssignment;
    type NativeInputs = native::InputsAssignment;
    type NativeGroup = CompressedRistretto;
    type NativeScalar = native::scalar::Scalar;
    use native::dense_mlpoly::{PolyCommitment, PolyEvalProof};
    use native::nizk::bullet::BulletReductionProof;
    use native::nizk::{
        DotProductProof, DotProductProofLog, EqualityProof, KnowledgeProof, ProductProof,
    };
    use native::r1csproof::R1CSProof as R1csProof;
    use native::sumcheck::ZKSumcheckInstanceProof as SumcheckProof;

    fn group(g: &NativeGroup) -> V {
        let p = curve25519_dalek_5::ristretto::CompressedRistretto(g.to_bytes())
            .decompress()
            .unwrap();
        Value::g1(backend::ff_group::FfPoint::new(p))
    }
    fn native_group(v: &V) -> NativeGroup {
        let mut bytes = Vec::new();
        match v {
            Value::G1(g) => g.write_bytes(&mut bytes),
            Value::G1Affine(g) => G::write_affine_bytes(g, &mut bytes),
            _ => panic!("expected group element, got {v}"),
        }
        CompressedRistretto(bytes.try_into().unwrap())
    }
    fn scalar(f: &NativeScalar) -> V {
        Value::Scalar(F::from_le_bytes_mod_order(&f.to_bytes()))
    }
    fn native_scalar(v: &V) -> NativeScalar {
        let mut bytes = Vec::new();
        match v {
            Value::Scalar(f) => f.write_bytes(&mut bytes),
            _ => panic!("expected scalar, got {v}"),
        }
        NativeScalar::from_bytes(&bytes.try_into().unwrap()).unwrap()
    }
    fn bytes(f: &F) -> [u8; 32] {
        let mut bytes = Vec::new();
        f.write_bytes(&mut bytes);
        bytes.try_into().unwrap()
    }

    fn setup(
        m: usize,
        inputs: &mut std::collections::HashMap<lang::id::Vid, V>,
        products: &super::super::MatVec<F>,
    ) -> (NativeInstance, NativeGens, NativeVars, NativeInputs) {
        let n = 1 << m;
        let nw = n / 2;
        let mats = products.mats.each_ref().map(|mat| {
            mat.iter()
                .map(|&(r, c, f)| (r, c, bytes(&f)))
                .collect::<Vec<_>>()
        });
        let inst = NativeInstance::new(n, nw, nw - 1, &mats[0], &mats[1], &mats[2]).unwrap();
        let vars =
            NativeVars::new(&products.z[..nw].iter().map(bytes).collect::<Vec<_>>()).unwrap();
        let io =
            NativeInputs::new(&products.z[nw + 1..].iter().map(bytes).collect::<Vec<_>>()).unwrap();
        assert!(inst.is_sat(&vars, &io).unwrap());
        let gens = NativeGens::new(n, nw, nw - 1);
        let pc = &gens.gens_r1cs_sat.gens_pc.gens;
        let sc = &gens.gens_r1cs_sat.gens_sc;
        inputs.extend(
            [
                (
                    "g_vec_w",
                    group_values(pc.gens_n.G.iter().map(|g| group(&g.compress())).collect()),
                ),
                ("g_1", group(&pc.gens_1.G[0].compress())),
                ("h_1", group(&pc.gens_1.h.compress())),
                (
                    "g_3",
                    group_values(sc.gens_3.G.iter().map(|g| group(&g.compress())).collect()),
                ),
                ("h_3", group(&sc.gens_3.h.compress())),
                (
                    "g_4",
                    group_values(sc.gens_4.G.iter().map(|g| group(&g.compress())).collect()),
                ),
                ("h_4", group(&sc.gens_4.h.compress())),
            ]
            .map(|(name, value)| (Vid::from(name), value)),
        );
        (inst, gens, vars, io)
    }

    include!("case.rs");
}
