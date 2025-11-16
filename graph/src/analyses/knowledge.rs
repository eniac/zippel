use backend::ArkConfig;
use log::{warn, debug};
use crate::{DQDag, Ref, PRef};
use crate::analyses::groebner::{ElimTerm, SparsePolynomial, GroebnerBasis, GroebnerBuilder};
use share::Ctx;
use petgraph::graph::NodeIndex;
use lang::id::Vid;


/// Perform a knowledge analysis using Groebner bases.
pub struct KnowledgeAnalysis<C: ArkConfig>(GroebnerBuilder<C, ElimTerm>);

impl<C: ArkConfig> KnowledgeAnalysis<C> {
    pub fn new(gb: GroebnerBuilder<C, ElimTerm>) -> Self {
        Self(gb)
    }

    pub fn from_input(dag: &DQDag<C>) -> Self {
        let mut gb = GroebnerBuilder::new();
        gb.add_input(dag);
        Self(gb)
    }

    pub fn from_relation(dag: &DQDag<C>) -> Self {
        let mut gb = GroebnerBuilder::new();
        gb.add_relation(dag);
        Self(gb)
    }

    fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
        let vars = p.vars();
        // Contains both secret and public variables, and the secret values are non-uniform random
        vars.iter().all(|v| !v.is_uniform())
        && vars.iter().any(|v| v.is_public())
        && vars.iter().any(|v| v.is_private())
    }

    pub fn private(&self) -> Vec<PRef> {
        self.0.vars()
        .into_iter()
        .filter(|v| v.is_private())
        .collect()
    }

    pub fn public(&self) -> Vec<PRef> {
        self.0.vars()
        .into_iter()
        .filter(|v| v.is_public())
        .collect()
    }

    pub fn eliminate_var(&mut self){
        self.0.eliminate_var(&|v| ElimTerm::eliminate_var(v));
    }

    pub fn eliminate_groups(&mut self) {
        self.0.eliminate_monomial(&|t| {
            let mono_sum = t.iter()
            .filter_map(|(v, i)| if v.typ.is_group() { Some(*i) } else { None })
            .sum::<usize>();
            mono_sum > 1
        });
    }

    pub fn run(&mut self) -> bool {
        // Compute the Groebner basis
        self.0.run();

        // Delete varieties with elimination variables
        self.eliminate_var();

        // Inline all polynomials except for public variables
        self.0.inline(|p| p.is_public());

        // Delete varieties where group elements are multiplied
        self.eliminate_groups();

        if self.0.basis.iter().any(Self::is_leak) {
            warn!("Leak found");
            for p in self.0.basis.iter() {
                if Self::is_leak(p) {
                    warn!("{}", p);
                }
            }
            return true;
        }
        false
    }
}

#[cfg(test)] use lang::ast::UModule;
#[cfg(test)] use share::unwrap;
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
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    // Propagate qualifiers
    let g = QualifierPropagation::from_dag(&gs[0]);
    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);


    // Compute Groebner basis for the implementation
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Compute the Groebner bases
    assert!(kz.run());
}

#[test]
fn groebner_bar() {

    let ex = r#"
        proto foo<F: Field>(private s: F, private s': F) where s == s' {
            let r = random<F>;
            a <- r * s;
            b <- r * s';
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_bar").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);
    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);

    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Compute the Groebner basis
    assert!(kz.run());
}

#[test]
fn groebner_baz() {

    let ex = r#"
        proto baz<F: Field, N: 4..8>(private s: [F; N], private s': F) where s[3] == s' {
            let r = random<F>;
            a <- r * s[3];
            b <- r * s';
            verify(a == b);
        }"#;

    println!("Parsing example: {}", ex);
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_baz").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g_inp = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);
    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    // Compute the Groebner basis
    assert!(kz.run());
}

#[cfg(test)] use crate::WritePdf;
/// This example is somewhat contrived. Here is how we leak s = s'.
/// 1. We have two private inputs s and s'.
/// 2. a - b = s - s'
/// 3. g*a = g*b from [verify]
/// 4. g*(a - b) = g *(s - s') = 0 from [2]
/// 5. s = s' if g != 0.
#[test]
#[ignore]
fn groebner_ex3() {
    let ex = r#"
        proto foo<G: Group, F: Scalar<G>>(private s: F, private s': F, public g: G) where s == s {
            let r = random<F>;
            let a = r + s;
            let b = r + s';
            c <- g * a;
            d <- g * b;
            verify(c == d);
        }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("groebner_ex3").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let g = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g);

    // Create an object computing the Groebner basis
    let mut kz = KnowledgeAnalysis::from_input(&g);

    assert!(kz.run());    
}

#[test]
#[ignore]
fn groebner_zerocheck() {
    let ex = r#"
        proto zerocheck<F: Field>(private p: Uni<F, 16>, public q: Uni<F, 16>) where p == q {
            let r = random<F>;
            verify(p(r) == q(r))
        }"#;

    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    let g_inp = QualifierPropagation::from_dag(&gs[0]);

    // Uniformity propagation
    let mut up = UniformityPropagation::new();
    let g = up.from_dag(&g_inp);

    let mut kz = KnowledgeAnalysis::from_input(&g);
    assert!(kz.run());
}