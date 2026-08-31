use ark_ec::{CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::SeedableRng;
// digest 0.10: `Input` → `Update`, `xof_result` → `finalize_xof`.
use digest::{ExtendableOutput, Update, XofReader};
use rand_chacha::ChaCha20Rng;
use sha3::Shake256;

#[derive(Debug)]
pub struct MultiCommitGens<G> {
  pub n: usize,
  pub G: Vec<G>,
  pub h: G,
}

impl<G: CurveGroup> MultiCommitGens<G> {
  pub fn new(n: usize, label: &[u8]) -> Self {
    // sha3 0.10: `Update::update` (not `.input`) and `finalize_xof`
    // (not `.xof_result`).
    let mut shake = Shake256::default();
    shake.update(label);
    let mut buf = vec![];
    // ark 0.6: `PrimeGroup::generator` (was `prime_subgroup_generator`);
    // CanonicalSerialize uses `serialize_compressed` shortcut.
    <G as PrimeGroup>::generator()
      .serialize_compressed(&mut buf)
      .unwrap();
    shake.update(&buf);

    let mut reader = shake.finalize_xof();
    let mut seed = [0u8; 32];
    reader.read(&mut seed);
    let mut rng = ChaCha20Rng::from_seed(seed);

    let mut gens: Vec<G> = Vec::new();
    for _ in 0..n + 1 {
      gens.push(G::rand(&mut rng));
    }

    MultiCommitGens {
      n,
      G: gens[..n].to_vec(),
      h: gens[n],
    }
  }

  pub fn clone(&self) -> Self {
    MultiCommitGens {
      n: self.n,
      h: self.h,
      G: self.G.clone(),
    }
  }

  pub fn split_at(&self, mid: usize) -> (Self, Self) {
    let (G1, G2) = self.G.split_at(mid);

    (
      MultiCommitGens {
        n: G1.len(),
        G: G1.to_vec(),
        h: self.h,
      },
      MultiCommitGens {
        n: G2.len(),
        G: G2.to_vec(),
        h: self.h,
      },
    )
  }
}

pub trait Commitments<G: CurveGroup>: Sized {
  fn commit(&self, blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G;
  fn batch_commit(inputs: &[Self], blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G;
}

impl<G: CurveGroup> Commitments<G> for G::ScalarField {
  fn commit(&self, blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, 1);
    // ark 0.6: scalar * group works directly; no need to go through BigInt.
    gens_n.G[0] * *self + gens_n.h * *blind
  }

  fn batch_commit(inputs: &[Self], blind: &G::ScalarField, gens_n: &MultiCommitGens<G>) -> G {
    assert_eq!(gens_n.n, inputs.len());

    // ark 0.6: `CurveGroup::normalize_batch` (was `batch_normalization_into_affine`),
    // `<G as VariableBaseMSM>::msm(...)` returns Result.
    let mut bases: Vec<G::Affine> = G::normalize_batch(gens_n.G.as_ref());
    let mut scalars: Vec<G::ScalarField> = inputs.to_vec();
    bases.push(gens_n.h.into_affine());
    scalars.push(*blind);

    <G as VariableBaseMSM>::msm(bases.as_ref(), scalars.as_ref()).expect("MSM: len mismatch")
  }
}
