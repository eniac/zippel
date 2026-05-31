//! Smoke test for the arkworks field used as the coefficient layer.
//!
//! Replaces the legacy Z/p Barrett field property tests now that
//! `ark-gb` is generic over `ark_ff::Field`.

use ark_bls12_381::Fr;
use ark_ff::{Field, One, Zero};

#[test]
fn fr_zero_one_identities() {
    let z = Fr::zero();
    let o = Fr::one();
    assert_eq!(z + o, o);
    assert_eq!(o * o, o);
    assert_eq!(o - o, z);
    assert!(Fr::inverse(&z).is_none());
    assert_eq!(Fr::inverse(&o).unwrap(), o);
}
