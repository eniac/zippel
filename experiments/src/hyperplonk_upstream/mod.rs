//! HyperPlonk (Chen, Bünz, Boneh, Zhang 2022) vendored from
//! EspressoSystems/hyperplonk `main` (2a3b55c), ported to arkworks 0.6.
//!
//! The end-to-end SNARK: vanilla Plonk gate, gate-identity zerocheck,
//! permutation check (product check over `frac`/`prod` oracles), and the
//! deferred batch opening of every claim with multilinear KZG. The
//! sumcheck, `VirtualPolynomial` and transcript underneath are the ones
//! already vendored in `crate::sumcheck_upstream`.
//!
//! Changes from upstream, none of which touch the algorithms:
//!   - The `HyperPlonkSNARK`, `PermutationCheck`, `ProductCheck`,
//!     `ZeroCheck` and `PolynomialCommitmentScheme` traits are flattened into
//!     free functions, since only the multilinear-KZG instantiation is used.
//!   - Errors collapse into `PolyIOPErrors`; timers are dropped.
//!   - `prove`/`verify` take the transcript as an argument (upstream builds
//!     `IOPTranscript::new(b"hyperplonk")` inside), and the transcript has a
//!     test-only replay hook, so a proof can be recomputed under another
//!     implementation's challenges.
//!   - `MockCircuit::new` takes an rng instead of `test_rng()`.
//!   - SRS generation uses arkworks 0.6's `batch_mul` in place of 0.4's
//!     `FixedBase` tables.

pub mod pcs;
pub mod piop;
pub mod snark;

pub use crate::sumcheck_upstream::poly_iop::errors::PolyIOPErrors;
pub use crate::sumcheck_upstream::transcript::IOPTranscript;
pub use pcs::MultilinearUniversalParams;
pub use snark::{
    CustomizedGates, HyperPlonkProof, HyperPlonkProvingKey, HyperPlonkVerifyingKey, MockCircuit,
    preprocess, prove, verify,
};

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::One;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    #[test]
    fn vanilla_roundtrip() {
        let mut rng = StdRng::seed_from_u64(7);
        for nv in [2, 3, 5] {
            let srs = MultilinearUniversalParams::<Bls12_381>::gen_srs_for_testing(&mut rng, nv);
            let circuit =
                MockCircuit::<Fr>::new(1 << nv, &CustomizedGates::vanilla_plonk_gate(), &mut rng);
            let (pk, vk) = preprocess(&circuit.index, &srs).unwrap();
            let proof = prove(
                &pk,
                &circuit.public_inputs,
                &circuit.witnesses,
                &mut IOPTranscript::new(b"hyperplonk"),
            )
            .unwrap();
            let ok = verify(
                &vk,
                &circuit.public_inputs,
                &proof,
                &mut IOPTranscript::new(b"hyperplonk"),
            )
            .unwrap();
            assert!(ok, "nv = {nv}");

            let mut bad = circuit.public_inputs.clone();
            bad[0] += Fr::one();
            assert!(
                !verify(&vk, &bad, &proof, &mut IOPTranscript::new(b"hyperplonk")).unwrap_or(false),
                "nv = {nv}: wrong public input accepted"
            );
        }
    }
}
