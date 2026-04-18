use backend::ArkConfig;
use backend::op::HasOpFactory;
use log::{warn};
#[cfg(test)]
use log::debug;
#[cfg(test)] use crate::WritePdf;
use crate::{DQDag, PRef};
use crate::analyses::groebner::{ElimTerm, SparsePolynomial, GroebnerBuilder, GroebnerBasis};
use crate::analyses::error::AnalysisError;


/// Perform a knowledge analysis using Groebner bases.
pub struct KnowledgeAnalysis<C: ArkConfig> {
    builder: GroebnerBuilder<C, ElimTerm>,
    /// Gröbner basis of the relation (precondition) alone, used to filter
    /// polynomials that are derivable from the precondition (not real leaks).
    relation_basis: Option<GroebnerBasis<C::F, ElimTerm>>,
}

impl<C: ArkConfig + HasOpFactory> KnowledgeAnalysis<C> {
    pub fn new(gb: GroebnerBuilder<C, ElimTerm>) -> Self {
        Self { builder: gb, relation_basis: None }
    }

    pub fn from_input(dag: &DQDag<C>) -> Self {
        let mut gb = GroebnerBuilder::new();
        gb.add_input(dag);

        // Include the relation (where clause) in the main basis so Buchberger
        // can use it for substitution (e.g., g*x → h). Build a separate
        // relation-only basis to later identify and skip precondition polys.
        let relation_basis = if dag.relation_node().is_some() {
            gb.add_relation(dag);
            let mut rel_gb = GroebnerBuilder::new();
            rel_gb.add_relation(dag);
            rel_gb.run();
            Some(rel_gb.basis)
        } else {
            None
        };

        Self { builder: gb, relation_basis }
    }

    #[cfg(test)]
    pub fn from_relation(dag: &DQDag<C>) -> Self {
        let mut gb = GroebnerBuilder::new();
        gb.add_relation(dag);
        Self { builder: gb, relation_basis: None }
    }

    fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
        let vars = p.vars();
        let has_public = vars.iter().any(|v| v.is_public());
        let has_private = vars.iter().any(|v| v.is_private());

        if !has_public || !has_private {
            return false;
        }

        // A polynomial with a private uniform variable appearing at degree 1
        // alone in its own term is safe — it acts as a one-time pad mask.
        // E.g., r + c*x - z where r is private uniform.
        let has_uniform_mask = p.terms.iter().any(|(term, _coeff)| {
            let term_vars: Vec<_> = term.iter().collect();
            term_vars.len() == 1
                && *term_vars[0].1 == 1
                && term_vars[0].0.is_private()
                && (term_vars[0].0.is_uniform() || term_vars[0].0.is_uniform_nz())
        });

        !has_uniform_mask
    }

    pub fn private(&self) -> Vec<PRef> {
        self.builder.vars()
        .into_iter()
        .filter(|v| v.is_private())
        .collect()
    }

    pub fn public(&self) -> Vec<PRef> {
        self.builder.vars()
        .into_iter()
        .filter(|v| v.is_public())
        .collect()
    }

    pub fn eliminate_var(&mut self){
        self.builder.basis.basis.retain(|p| {
            let vars = p.vars();
            if vars.is_empty() {
                return true;
            }
            // Remove polynomials where ALL variables are private uniform
            let all_private_uniform = vars.iter().all(|v|
                v.is_private() && v.is_uniform()
            );
            if all_private_uniform {
                return false;
            }
            // Remove polynomials containing Local variables — these are
            // prover-internal computations that the verifier cannot observe
            let has_local = vars.iter().any(|v| v.is_local());
            !has_local
        });
    }

    pub fn eliminate_groups(&mut self) {
        self.builder.eliminate_monomial(&|t| {
            let mono_sum = t.iter()
            .filter_map(|(v, i)| if v.typ.is_group() { Some(*i) } else { None })
            .sum::<usize>();
            mono_sum > 1
        });
    }

    pub fn run(&mut self) -> Result<(), AnalysisError<C>> {
        // Compute the Groebner basis
        self.builder.run();

        // Delete varieties with elimination variables
        self.eliminate_var();

        // Delete varieties where group elements are multiplied
        self.eliminate_groups();

        for p in self.builder.basis.iter() {
            if Self::is_leak(p) {
                // Skip polynomials derivable from the relation (precondition).
                // The verifier already knows these — they're not new leaks.
                if let Some(ref rel_basis) = self.relation_basis {
                    if rel_basis.contains_poly(p) {
                        continue;
                    }
                }
                warn!("Leak found: {}", p);
                return Err(AnalysisError::KnowledgeLeak(p.clone()));
            }
        }
        Ok(())
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
#[cfg(test)] use share::Ctx;
#[cfg(test)] use backend::ArkBls12_381;
#[cfg(test)] use crate::analyses::{UniformityPropagation, QualifierPropagation};
#[cfg(test)] use crate::UDags;

#[test]
#[ignore]
fn knowledge_foo() {
    let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r  + c + s;
            verify(a == b)
        }"#;

    debug!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_foo").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);
    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);


    // Compute Groebner basis for the implementation
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Compute the Groebner bases
    assert!(kz.run().is_err());
}


#[test]
fn groebner_bar() {

    let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            a <- r * s;
            b <- r * s';
            verify(a == b)
        }"#;

    debug!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_bar").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);
    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);

    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Compute the Groebner basis
    assert!(kz.run().is_ok());
}


#[test]
fn groebner_baz() {

    let ex = r#"
        proto baz<F: Field, N: 4..8>(private s: [F; N], private s': F) where s[3] == s' {
            let r = random<F>;
            a <- r * s[3];
            b <- r * s';
            verify(a == b)
        }"#;

    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_baz").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);
    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Compute the Groebner basis
    assert!(kz.run().is_ok());
}

/// This example is somewhat contrived. Here is how we leak s = s'.
/// 1. We have two private inputs s and s'.
/// 2. a - b = s - s'
/// 3. g*a = g*b from [verify]
/// 4. g*(a - b) = g *(s - s') = 0 from [2]
/// 5. s = s' if g != 0.

#[test]
fn groebner_ex3() {
    let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(private s: F, private s': F, public g: G) where s == s {
            let r = random<F>;
            let a = r + s;
            let b = r + s';
            c <- g * a;
            d <- g * b;
            verify(c == d)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_ex3").unwrap_or_else(|e| {
        debug!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    assert!(kz.run().is_err());
}


#[test]
#[ignore]
fn schnorr_zk() {
    let ex = r#"
        proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_ok(), "Schnorr protocol should be zero-knowledge");
}


#[test]
fn zk_regression_direct_secret_leak() {
    let ex = r#"
        proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            d <- x;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    let result = kz.run();
    if let Err(ref e) = result {
        eprintln!("Leak detected: {}", e);
    }
    assert!(result.is_err(), "d <- x directly leaks private x to transcript");
}

/// Leak: transcript contains x + public_val (no blinding).
/// Verifier computes x = d - y.
#[test]
fn zk_leak_unblinded_linear_combination() {
    let ex = r#"
        proto leak<F: Field>(private x: F, public y: F) where x == x {
            d <- x + y;
            verify(d == d)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_err(), "d <- x + y leaks x (verifier knows y and d)");
}

/// Leak: Schnorr-like protocol without random blinding.
/// Response z = x*c is sent to verifier, who knows c and computes x = z/c.
#[test]
fn zk_leak_no_random_blinding() {
    let ex = r#"
        proto leak<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            c <- challenge<F*>;
            z <- x * c;
            verify(g*z == h*c)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_err(), "z <- x*c without random blinding leaks x");
}

/// Leak: two transcripts that differ only by the secret.
/// Verifier sees a and b, computes a - b = s - s'.
#[test]
fn zk_leak_secret_difference_on_transcript() {
    let ex = r#"
        proto leak<F: Field>(private s: F, private t: F, public y: F) where y == y {
            a <- s + y;
            b <- t + y;
            verify(a == b)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_err(), "a - b = s - t leaks relationship between secrets");
}

/// NOT a leak: proper Schnorr with random blinding.
/// Verifier cannot recover x from z = r + x*c (r is uniform mask).
#[test]
fn zk_safe_schnorr_with_blinding() {
    let ex = r#"
        proto safe<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
            let r = random<F>;
            u <- g*r;
            c <- challenge<F*>;
            z <- r + x*c;
            verify(g*z == u + h*c)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_ok(), "Schnorr with proper blinding should be ZK");
}

/// Leak: one verify is properly blinded, another directly leaks the secret.
/// The first verify is safe (has random blinding), but the second verify(s == s)
/// directly leaks s to the transcript.
#[test]
fn zk_multiple_verify_one_safe_one_leak() {
    let ex = r#"
        proto mixed<F: Field>(private s: F, private t: F, public y: F) where y == y {
            let r = random<F>;
            x <- s * r;
            w <- t * r;
            verify(x == w);
            verify(s == s)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_err(), "One safe and one leaking verify should fail knowledge analysis");
}

/// Leak: the two verify statements together leak private information.
/// Each check is a trivial self-equality on a transcript value (`a == a` and `b == b`).
/// Since `a = s + r` and `b = t + r` reuse the same blinding value `r`, publishing both
/// values reveals `a - b = s - t`, so the transcript leaks information about the secrets.
#[test]
fn zk_multiple_verify_one_safe_one_subtle_leak() {
    let ex = r#"
        proto mixed<F: Field>(private s: F, private t: F, public y: F) where y == y {
            let r = random<F>;
            a <- s + r;
            b <- t + r;
            verify(a == a);
            verify(b == b)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_err(), "One safe and one leaking verify should fail knowledge analysis");
}

/// Safe: both verify statements are properly blinded with independent random values.
/// Each check uses a separate random blinding factor, so no private information leaks.
#[test]
fn zk_multiple_verify_both_safe() {
    let ex = r#"
        proto safe<F: Field>(private a: F, private b: F) where a == b {
            let r = random<F>;
            let s = random<F>;
            x <- a * r;
            y <- b * r;
            u <- a * s;
            v <- b * s;
            verify(x == y);
            verify(u == v)
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize(&Ctx::new()).unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run().is_ok(), "Two verify statements both properly blinded with independent randoms should pass knowledge analysis");
}
