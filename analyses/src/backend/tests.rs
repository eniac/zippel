//! Smoke tests for the new backend API (order-free Polynomial + MonoOrder + GbBackend).

#[cfg(test)]
mod backend_tests {
    use crate::backend::{GbBackend, ark_gb::ArkGb};
    use crate::frontend::{MonoOrder, Polynomial};
    use ark_bls12_381::Fr;
    use ark_ff::One;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use graph::PRef;
    use lang::id::Vid;
    use lang::typ::{Distribution, Qualifier};
    use petgraph::graph::NodeIndex;

    fn mk_var(name: &str, idx: usize) -> PRef {
        PRef::from_var(
            Vid(name.to_string()),
            NodeIndex::new(idx),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::default(),
        )
    }

    #[test]
    fn grevlex_basic_gb() {
        let g = mk_var("g", 0);
        let x = mk_var("x", 1);
        let h = mk_var("h", 2);
        let r = mk_var("r", 3);
        let u = mk_var("u", 4);

        let var = |p: &PRef| Polynomial::<Fr>::var(p);
        let p1 = var(&g) * var(&x) - var(&h);
        let p2 = var(&g) * var(&r) - var(&u);

        let backend = ArkGb::<ArkBls12_381>::default();
        let basis = backend
            .compute_gb(vec![p1.clone(), p2.clone()], &MonoOrder::grevlex(), 8)
            .unwrap();

        // Input polys should reduce to 0
        let rem1 = backend.reduce(p1, &basis);
        assert!(rem1.is_zero(), "p1 should reduce to 0, got: {}", rem1);
        let rem2 = backend.reduce(p2, &basis);
        assert!(rem2.is_zero(), "p2 should reduce to 0, got: {}", rem2);

        // h*r - u*x should reduce to 0 given g*x = h and g*r = u
        let target = var(&h) * var(&r) - var(&u) * var(&x);
        let rem = backend.reduce(target, &basis);
        assert!(rem.is_zero(), "h*r - u*x should reduce to 0, got: {}", rem);
    }

    #[test]
    fn grevlex_unit_ideal() {
        let x = mk_var("x", 0);
        let var = |p: &PRef| Polynomial::<Fr>::var(p);
        let one = Polynomial::lit(&Fr::one());

        // x and 1 → unit ideal
        let backend = ArkGb::<ArkBls12_381>::default();
        let basis = backend
            .compute_gb(vec![var(&x), one], &MonoOrder::grevlex(), 8)
            .unwrap();
        assert!(basis.is_unit(), "basis with constant should be unit ideal");
    }

    #[test]
    fn unsupported_order_returns_err() {
        use crate::frontend::{Block, BlockKind};
        let x = mk_var("x", 0);
        let var = |p: &PRef| Polynomial::<Fr>::var(p);

        let backend = ArkGb::<ArkBls12_381>::default();
        let order = MonoOrder::block(vec![Block {
            vars: None,
            kind: BlockKind::DegLex,
        }]);
        let result = backend.compute_gb(vec![var(&x)], &order, 8);
        assert!(result.is_err(), "DegLex should be unsupported by ark-gb");
    }
}
