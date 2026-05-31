//! Property-based tests for monomials.

use ark_bls12_381::Fr;
use ark_gb::{GrevLexTerm, MonoTerm, Ring};
use proptest::prelude::*;
use std::cmp::Ordering;

/// Generate a random ring with `nvars ∈ [1, 25]`, fixed prime.
///
/// 25 is the staging workload size; it also leaves room (we permit up
/// to 31) for the packing overflow cases.
fn ring_strategy() -> impl Strategy<Value = Ring<Fr>> {
    (1u32..=25).prop_map(|nvars| Ring::<Fr>::new(nvars).unwrap())
}

/// Generate a monomial in the given ring with per-variable exponents
/// small enough that products stay within the 8-bit limit.
fn mono_strategy(ring: Ring<Fr>) -> impl Strategy<Value = (Ring<Fr>, MonoTerm)> {
    let n = ring.nvars() as usize;
    // Cap at 30 so sums of up to ~8 monomials stay within 255.
    prop::collection::vec(0u32..30, n).prop_map(move |exps| {
        let m = MonoTerm::from_exponents(&ring, &exps).unwrap();
        (ring.clone(), m)
    })
}

/// Generate a ring and three monomials sharing it.
fn ring_mono3_strategy() -> impl Strategy<Value = (Ring<Fr>, MonoTerm, MonoTerm, MonoTerm)> {
    ring_strategy().prop_flat_map(|r| {
        let n = r.nvars() as usize;
        (
            Just(r),
            prop::collection::vec(0u32..20, n),
            prop::collection::vec(0u32..20, n),
            prop::collection::vec(0u32..20, n),
        )
            .prop_map(|(r, ae, be, ce)| {
                let a = MonoTerm::from_exponents(&r, &ae).unwrap();
                let b = MonoTerm::from_exponents(&r, &be).unwrap();
                let c = MonoTerm::from_exponents(&r, &ce).unwrap();
                (r, a, b, c)
            })
    })
}

fn ring_mono2_strategy() -> impl Strategy<Value = (Ring<Fr>, MonoTerm, MonoTerm)> {
    ring_strategy().prop_flat_map(|r| {
        let n = r.nvars() as usize;
        (
            Just(r),
            prop::collection::vec(0u32..25, n),
            prop::collection::vec(0u32..25, n),
        )
            .prop_map(|(r, ae, be)| {
                let a = MonoTerm::from_exponents(&r, &ae).unwrap();
                let b = MonoTerm::from_exponents(&r, &be).unwrap();
                (r, a, b)
            })
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    #[test]
    fn mul_associative((r, a, b, c) in ring_mono3_strategy()) {
        // Exponents capped at 20 to keep products in range.
        let ab = a.mul(&b, &r);
        let ab_c = ab.mul(&c, &r);
        let bc = b.mul(&c, &r);
        let a_bc = a.mul(&bc, &r);
        prop_assert_eq!(ab_c, a_bc);
    }

    #[test]
    fn mul_commutative((r, a, b) in ring_mono2_strategy()) {
        let ab = a.mul(&b, &r);
        let ba = b.mul(&a, &r);
        prop_assert_eq!(ab, ba);
    }

    #[test]
    fn a_divides_ab((r, a, b) in ring_mono2_strategy()) {
        let ab = a.mul(&b, &r);
        prop_assert!(a.divides(&ab, &r));
        prop_assert!(b.divides(&ab, &r));
    }

    #[test]
    fn div_after_mul_recovers((r, a, b) in ring_mono2_strategy()) {
        let ab = a.mul(&b, &r);
        prop_assert_eq!(ab.div(&b, &r).unwrap(), a);
    }

    #[test]
    fn lcm_commutative((r, a, b) in ring_mono2_strategy()) {
        let ab = a.lcm(&b, &r);
        let ba = b.lcm(&a, &r);
        prop_assert_eq!(ab, ba);
    }

    #[test]
    fn lcm_absorbs_both((r, a, b) in ring_mono2_strategy()) {
        let l = a.lcm(&b, &r);
        prop_assert!(a.divides(&l, &r));
        prop_assert!(b.divides(&l, &r));
    }

    #[test]
    fn total_deg_is_sum((r, a, b) in ring_mono2_strategy()) {
        let ab = a.mul(&b, &r);
        prop_assert_eq!(ab.total_deg(), a.total_deg() + b.total_deg());
    }

    #[test]
    fn sev_of_product_is_or((r, a, b) in ring_mono2_strategy()) {
        let ab = a.mul(&b, &r);
        prop_assert_eq!(ab.sev(), a.sev() | b.sev());
    }

    /// sev pre-filter soundness: `a | b` implies every bit set in `sev(a)`
    /// is also set in `sev(b)`.  The sweep relies on the contrapositive
    /// (bits in `sev(a)` not in `sev(b)` => a ∤ b) to reject non-divisors
    /// cheaply; if this ever fails, the sweep is unsound.
    #[test]
    fn sev_prefilter_sound((r, a, b) in ring_mono2_strategy()) {
        if a.divides(&b, &r) {
            prop_assert_eq!(a.sev() & !b.sev(), 0,
                "a | b but sev(a) has bits not in sev(b)");
        }
    }

    #[test]
    fn cmp_is_total((_r, a, b) in ring_mono2_strategy()) {
        let ga = GrevLexTerm::from(a);
        let gb = GrevLexTerm::from(b);
        let ord_ab = ga.cmp(&gb);
        let ord_ba = gb.cmp(&ga);
        match (ord_ab, ord_ba) {
            (Ordering::Less, Ordering::Greater)
            | (Ordering::Greater, Ordering::Less)
            | (Ordering::Equal, Ordering::Equal) => {}
            other => prop_assert!(false, "cmp not antisymmetric: {:?}", other),
        }
    }

    #[test]
    fn cmp_equal_iff_same_exponents((r, a, b) in ring_mono2_strategy()) {
        let equal_exps = a.exponents(&r) == b.exponents(&r);
        let ga = GrevLexTerm::from(a);
        let gb = GrevLexTerm::from(b);
        prop_assert_eq!(ga.cmp(&gb) == Ordering::Equal, equal_exps);
    }

    #[test]
    fn round_trip_exponents((r, m) in ring_strategy().prop_flat_map(mono_strategy)) {
        let es = m.exponents(&r);
        let m2 = MonoTerm::from_exponents(&r, &es).unwrap();
        prop_assert_eq!(m, m2);
    }

    #[test]
    fn assert_canonical_after_ops((r, a, b) in ring_mono2_strategy()) {
        a.assert_canonical(&r);
        b.assert_canonical(&r);
        let ab = a.mul(&b, &r);
        ab.assert_canonical(&r);
        let l = a.lcm(&b, &r);
        l.assert_canonical(&r);
        if a.divides(&b, &r) {
            let q = b.div(&a, &r).unwrap();
            q.assert_canonical(&r);
        }
    }
}
