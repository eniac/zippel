//! Smoke tests for the new backend API (order-free Polynomial + MonoOrder + GbBackend).

#[cfg(test)]
mod backend_tests {
    use crate::PRef;
    use crate::backend::{GbBackend, ark_gb::ArkGb};
    use crate::frontend::{MonoOrder, Polynomial};
    use ark_bls12_381::Fr;
    use ark_ff::One;
    use backend::ATyp;

    use lang::typ::{Distribution, Qualifier};
    use petgraph::graph::NodeIndex;

    fn mk_var(name: &str, idx: usize) -> PRef {
        PRef::from_var(
            name.to_string(),
            NodeIndex::new(idx),
            ATyp::scalar(),
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

        let backend = ArkGb::<Fr>::default();
        let basis = backend
            .compute_gb(vec![p1.clone(), p2.clone()], &MonoOrder::grevlex())
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
        let backend = ArkGb::<Fr>::default();
        let basis = backend
            .compute_gb(vec![var(&x), one], &MonoOrder::grevlex())
            .unwrap();
        assert!(basis.is_unit(), "basis with constant should be unit ideal");
    }

    #[test]
    fn unsupported_order_returns_err() {
        use crate::frontend::{Block, BlockKind};
        let x = mk_var("x", 0);
        let y = mk_var("y", 1);
        let var = |p: &PRef| Polynomial::<Fr>::var(p);

        let backend = ArkGb::<Fr>::default();
        // GrevLex-then-Lex: ark-gb's Case 3 requires the first block to be Lex.
        let order = MonoOrder::block(vec![
            Block {
                vars: Some(vec![x.clone()]),
                kind: BlockKind::GrevLex,
            },
            Block {
                vars: Some(vec![y.clone()]),
                kind: BlockKind::Lex,
            },
        ]);
        let result = backend.compute_gb(vec![var(&x) * var(&y.clone()) - var(&x)], &order);
        assert!(
            result.is_err(),
            "GrevLex-then-Lex should be unsupported by ark-gb"
        );
    }
}

/// Tests that cross-check the Singular backend against ArkGb.
///
/// These tests **skip** (not fail) if the `Singular` binary is not on `PATH`,
/// so CI without Singular passes.
#[cfg(test)]
mod singular_tests {
    use crate::PRef;
    use crate::backend::{GbBackend, ark_gb::ArkGb, singular::Singular};
    use crate::frontend::{Block, BlockKind, MonoOrder, Polynomial};
    use ark_bls12_381::Fr;
    use ark_ff::One;
    use backend::ATyp;

    use lang::typ::{Distribution, Qualifier};
    use petgraph::graph::NodeIndex;

    fn mk_var(name: &str, idx: usize) -> PRef {
        PRef::from_var(
            name.to_string(),
            NodeIndex::new(idx),
            ATyp::scalar(),
            Qualifier::Public,
            Distribution::default(),
        )
    }

    /// Return `true` if the `Singular` binary is on `PATH`.
    fn singular_available() -> bool {
        std::process::Command::new("Singular")
            .arg("-q")
            .arg("-c")
            .arg("ring r = (integer, 7), (x(1)), dp;")
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .is_ok()
    }

    /// Assert that every generator in `ideal` reduces to zero under `basis`
    /// (via `backend`), i.e. the basis spans the same ideal.
    fn assert_generators_reduce_to_zero<B: GbBackend<Fr>>(
        backend: &B,
        ideal: &[Polynomial<Fr>],
        basis: &crate::backend::GbBasis<Fr>,
        label: &str,
    ) {
        for (i, g) in ideal.iter().enumerate() {
            if g.is_zero() {
                continue;
            }
            let rem = backend.reduce(g.clone(), basis);
            assert!(
                rem.is_zero(),
                "{label}: generator {i} should reduce to 0, got: {rem}"
            );
        }
    }

    /// Build the test ideal: g*x = h, g*r = u (from `grevlex_basic_gb`).
    fn gx_hu_ideal() -> (Vec<PRef>, Vec<Polynomial<Fr>>) {
        let g = mk_var("g", 0);
        let x = mk_var("x", 1);
        let h = mk_var("h", 2);
        let r = mk_var("r", 3);
        let u = mk_var("u", 4);
        let var = |p: &PRef| Polynomial::<Fr>::var(p);
        let ideal = vec![var(&g) * var(&x) - var(&h), var(&g) * var(&r) - var(&u)];
        (vec![g, x, h, r, u], ideal)
    }

    #[test]
    fn parity_grevlex() {
        if !singular_available() {
            eprintln!("skipping: Singular not on PATH");
            return;
        }
        let (_vars, ideal) = gx_hu_ideal();
        let order = MonoOrder::grevlex();

        let ark = ArkGb::<Fr>::default();
        let sing = Singular::<Fr>::default();

        let ark_basis = ark
            .compute_gb(ideal.clone(), &order)
            .expect("ark-gb should support grevlex");
        let sing_basis = sing
            .compute_gb(ideal.clone(), &order)
            .expect("Singular should support grevlex");

        assert_generators_reduce_to_zero(&ark, &ideal, &ark_basis, "ArkGb/grevlex");
        assert_generators_reduce_to_zero(&sing, &ideal, &sing_basis, "Singular/grevlex");

        // Cross-check: ArkGb's basis reduces to 0 under Singular's basis and
        // vice versa (both span the same ideal).
        for p in &ark_basis.polys {
            let rem = sing.reduce(p.clone(), &sing_basis);
            assert!(
                rem.is_zero(),
                "ArkGb poly should reduce to 0 under Singular: {rem}"
            );
        }
        for p in &sing_basis.polys {
            let rem = ark.reduce(p.clone(), &ark_basis);
            assert!(
                rem.is_zero(),
                "Singular poly should reduce to 0 under ArkGb: {rem}"
            );
        }
    }

    #[test]
    fn parity_two_block_grevlex() {
        if !singular_available() {
            eprintln!("skipping: Singular not on PATH");
            return;
        }
        let (vars, ideal) = gx_hu_ideal();
        // 2-block GrevLex/GrevLex: eliminate g first, then the rest.
        let order = MonoOrder::block(vec![
            Block {
                vars: Some(vec![vars[0].clone()]),
                kind: BlockKind::GrevLex,
            },
            Block {
                vars: None,
                kind: BlockKind::GrevLex,
            },
        ]);

        let ark = ArkGb::<Fr>::default();
        let sing = Singular::<Fr>::default();

        let ark_basis = ark
            .compute_gb(ideal.clone(), &order)
            .expect("ark-gb should support 2-block grevlex");
        let sing_basis = sing
            .compute_gb(ideal.clone(), &order)
            .expect("Singular should support 2-block grevlex");

        assert_generators_reduce_to_zero(&ark, &ideal, &ark_basis, "ArkGb/2-block");
        assert_generators_reduce_to_zero(&sing, &ideal, &sing_basis, "Singular/2-block");
    }

    #[test]
    fn parity_lex() {
        if !singular_available() {
            eprintln!("skipping: Singular not on PATH");
            return;
        }
        let (vars, ideal) = gx_hu_ideal();
        // Lex with explicit var order (g first = highest elimination priority).
        let order = MonoOrder::lex(vars.clone());

        let ark = ArkGb::<Fr>::default();
        let sing = Singular::<Fr>::default();

        let ark_basis = ark
            .compute_gb(ideal.clone(), &order)
            .expect("ark-gb should support lex");
        let sing_basis = sing
            .compute_gb(ideal.clone(), &order)
            .expect("Singular should support lex");

        assert_generators_reduce_to_zero(&ark, &ideal, &ark_basis, "ArkGb/lex");
        assert_generators_reduce_to_zero(&sing, &ideal, &sing_basis, "Singular/lex");
    }

    #[test]
    fn parity_unit_ideal() {
        if !singular_available() {
            eprintln!("skipping: Singular not on PATH");
            return;
        }
        let x = mk_var("x", 0);
        let var = |p: &PRef| Polynomial::<Fr>::var(p);
        let one = Polynomial::lit(&Fr::one());
        let ideal = vec![var(&x), one];
        let order = MonoOrder::grevlex();

        let sing = Singular::<Fr>::default();
        let basis = sing
            .compute_gb(ideal, &order)
            .expect("Singular should compute unit ideal");
        assert!(basis.is_unit(), "Singular basis should be unit ideal");
    }

    /// GrevLex-then-Lex: ark-gb returns Err, Singular returns Ok.
    #[test]
    fn unsupported_combo_ark_err_singular_ok() {
        if !singular_available() {
            eprintln!("skipping: Singular not on PATH");
            return;
        }
        let x = mk_var("x", 0);
        let y = mk_var("y", 1);
        let var = |p: &PRef| Polynomial::<Fr>::var(p);
        let ideal = vec![var(&x) * var(&y.clone()) - var(&x)];
        let order = MonoOrder::block(vec![
            Block {
                vars: Some(vec![x.clone()]),
                kind: BlockKind::GrevLex,
            },
            Block {
                vars: Some(vec![y.clone()]),
                kind: BlockKind::Lex,
            },
        ]);

        let ark = ArkGb::<Fr>::default();
        let ark_result = ark.compute_gb(ideal.clone(), &order);
        assert!(
            ark_result.is_err(),
            "ark-gb should not support GrevLex-then-Lex"
        );

        let sing = Singular::<Fr>::default();
        let sing_basis = sing
            .compute_gb(ideal.clone(), &order)
            .expect("Singular should support GrevLex-then-Lex");
        assert_generators_reduce_to_zero(&sing, &ideal, &sing_basis, "Singular/grevlex-then-lex");
    }
}
