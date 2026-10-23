//! Real Fiat–Shamir checks against the pinned spartan crate used by benchmarks.

use super::{InputsAssignment, Instance, NIZK, NIZKGens, VarsAssignment};

type Entry = (usize, usize, [u8; 32]);

fn statement(n: usize) -> (Vec<Entry>, Vec<Entry>, Vec<[u8; 32]>) {
    let bytes = |v: usize| {
        let mut bytes = [0; 32];
        bytes[..8].copy_from_slice(&(v as u64).to_le_bytes());
        bytes
    };
    // A and C are identity matrices; B selects the constant-one column.
    let a = (0..n).map(|i| (i, i, bytes(1))).collect();
    let b = (0..n).map(|i| (i, n / 2, bytes(1))).collect();
    let z = (0..n).map(|i| bytes(if i == n / 2 { 1 } else { i + 2 })).collect();
    (a, b, z)
}

#[test]
fn crate_prove_then_vendored_verify() {
    for m in [3, 4, 5] {
        let n = 1 << m;
        let (a, b, z) = statement(n);
        let inst = libspartan::Instance::new(n, n / 2, n / 2 - 1, &a, &b, &a).unwrap();
        let vars = libspartan::VarsAssignment::new(&z[..n / 2]).unwrap();
        let inputs = libspartan::InputsAssignment::new(&z[n / 2 + 1..]).unwrap();
        let gens = libspartan::NIZKGens::new(n, n / 2, n / 2 - 1);
        let proof = libspartan::NIZK::prove(&inst, vars, &inputs, &gens, &mut merlin::Transcript::new(b"compat"));
        let inst = Instance::new(n, n / 2, n / 2 - 1, &a, &b, &a).unwrap();
        let inputs = InputsAssignment::new(&z[n / 2 + 1..]).unwrap();
        let gens = NIZKGens::new(n, n / 2, n / 2 - 1);
        let proof: NIZK = bincode::deserialize(&bincode::serialize(&proof).unwrap()).unwrap();
        assert!(proof.verify(&inst, &inputs, &mut merlin::Transcript::new(b"compat"), &gens).is_ok());
    }
}

#[test]
fn vendored_prove_then_crate_verify() {
    for m in [3, 4, 5] {
        let n = 1 << m;
        let (a, b, z) = statement(n);
        let inst = Instance::new(n, n / 2, n / 2 - 1, &a, &b, &a).unwrap();
        let vars = VarsAssignment::new(&z[..n / 2]).unwrap();
        let inputs = InputsAssignment::new(&z[n / 2 + 1..]).unwrap();
        let gens = NIZKGens::new(n, n / 2, n / 2 - 1);
        let proof = NIZK::prove(&inst, vars, &inputs, &gens, &mut merlin::Transcript::new(b"compat"));
        let inst = libspartan::Instance::new(n, n / 2, n / 2 - 1, &a, &b, &a).unwrap();
        let inputs = libspartan::InputsAssignment::new(&z[n / 2 + 1..]).unwrap();
        let gens = libspartan::NIZKGens::new(n, n / 2, n / 2 - 1);
        let proof: libspartan::NIZK = bincode::deserialize(&bincode::serialize(&proof).unwrap()).unwrap();
        assert!(proof.verify(&inst, &inputs, &mut merlin::Transcript::new(b"compat"), &gens).is_ok());
    }
}
