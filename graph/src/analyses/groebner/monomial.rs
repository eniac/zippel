use ark_ff::Field;
use lang::typ::Qualifier;
use crate::PRef;
use core::cmp::Ordering;
use core::ops::{Mul, Div, MulAssign};
use share::Ctx;
use std::fmt::Debug;
use std::fmt;

/// A monomial trait that represents a term in a polynomial.
pub trait Monomial:
    Clone
    + PartialEq
    + Eq
    + Default
    + Send  
    + Sync
    + fmt::Display
    + MulAssign
    + Mul<Output = Self>
    + Div<Output = Option<Self>>
    + From<Vec<(PRef, usize)>>
    + Ord {

    fn vars(&self) -> Vec<PRef>;
    fn powers(&self) -> Vec<usize>;
    fn degree(&self) -> usize {
        self.powers().iter().sum()
    }
    fn is_constant(&self) -> bool {
        self.vars().is_empty()
    }
    fn evaluate<F: Field>(&self, p: &Ctx<PRef, F>) -> F;

    fn is_divided(&self, other: &Self) -> bool;

    fn is_coprime(&self, other: &Self) -> bool {
        self.gcd(other).is_constant()
    }
    fn lcm(&self, other: &Self) -> Self;
    fn gcd(&self, other: &Self) -> Self;
}


#[derive(Clone, PartialEq, Eq, PartialOrd, Debug)]
pub struct MonoTerm(Ctx<PRef, usize>); // (var index, power)

/// A monomial term with elimination ordering
#[derive(Clone, PartialEq, Eq, PartialOrd, Debug)]
pub struct ElimTerm(MonoTerm);

/// A monomial term with grevlex ordering
#[derive(Clone, PartialEq, Eq, PartialOrd, Debug)]
pub struct GrevLexTerm(MonoTerm);

/// From constructors for ElimTerm and GrevLexTerm
impl From<MonoTerm> for ElimTerm {
    fn from(t: MonoTerm) -> Self {
        ElimTerm(t)
    }
}

impl From<MonoTerm> for GrevLexTerm {
    fn from(t: MonoTerm) -> Self {
        GrevLexTerm(t)
    }
}

impl MonoTerm {
    fn vars(&self) -> Vec<PRef> {
        self.0.keys().into_iter().collect()
    }
    fn powers(&self) -> Vec<usize> {
        self.0.values().into_iter().collect()
    }
    fn degree(&self) -> usize {
        self.powers().iter().sum()
    }
    fn is_constant(&self) -> bool {
        self.0.is_empty() // Empty vec means the term is 1 (constant)
    }

    fn evaluate<F: Field>(&self, p: &Ctx<PRef, F>) -> F {
        let mut result = F::one();
        for (var, power) in self.0.iter() {
            if let Some(value) = p.get(&var) {
                for _ in 0..*power {
                    result *= value;
                }
            } else {
                // Variable not found in context, assume it evaluates to 1
            }
        }
        result
    }
    fn is_divided(&self, other: &Self) -> bool {
        for (var, power2) in other.0.iter() {
            match self.0.get(var) {
                Some(power1) => {
                    if power1 < power2 {
                        return false;
                    }
                }
                None => return false, // other has a variable self doesn't have
            }
        }
        true // All variables in other are in self with sufficient power
    }

    fn lcm(&self, other: &Self) -> Self {
        let mut lcm_powers: Vec<(PRef, usize)> = self.0.iter().map(|(v, p)| (v.clone(), *p)).collect();
        for (var, power2) in other.0.iter() {
            match lcm_powers.iter_mut().find(|(v, _)| v == var) {
                Some((_, power1)) => *power1 = (*power1).max(*power2),
                None => lcm_powers.push((var.clone(), *power2)),
            }
        }
        MonoTerm(lcm_powers.into_iter().collect())
    }

    fn gcd(&self, other: &Self) -> Self {
        let mut gcd_powers: Vec<(PRef, usize)> = Vec::new();
        for (var1, power1) in self.0.iter() {
            if let Some((_, power2)) = other.0.iter().find(|(v, _p)| v == &var1) {
                let min_power = (*power1).min(*power2);
                if min_power > 0 {
                    gcd_powers.push((var1.clone(), min_power));
                }
            }
        }
        MonoTerm(gcd_powers.into_iter().collect())
    }

    fn div(self, other: Self) -> Option<Self> {
        if !self.is_divided(&other) {
            return None;
        }

        let mut powers1 = self.0.iter().map(|(v, p)| (v.clone(), *p)).collect::<Vec<_>>();
        for (var, power2) in other.0.iter() {
            // We know var is in powers1 with sufficient power because term_is_divided was true
            if let Some(power1) = powers1.iter_mut().find(|(v, _)| v == var) {
                power1.1 -= power2;
            }
        }

        Some(MonoTerm(powers1.into_iter().filter(|(_, p)| *p > 0).collect()))
    }

    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_constant() {
            write!(f, "1")
        } else {
            let mut terms: Vec<String> = Vec::new();
            for (var, power) in self.0.iter() {
                if *power == 1 {
                    terms.push(format!("{}", var));
                } else if *power > 0 {
                    terms.push(format!("{}^{}", var, power));
                }
            }
            write!(f, "{}", terms.join("*"))
        }
    }

    // Graded reverse lexicographic order (grevlex, or degrevlex for degree reverse lexicographic order)
    // compares the total degree first, then uses a lexicographic order as tie-breaker, but it reverses
    // the outcome of the lexicographic comparison so that lexicographically larger monomials of the same
    // degree are considered to be degrevlex smaller.
    fn grevlex(&self, other: &Self) -> Ordering {
        // Compare total degrees of the monomials
        match self.degree().cmp(&other.degree()) {
            Ordering::Equal => {},
            order => return order.reverse(),
        };

        // Compare powers in reverse lexicographic order
        for ((v1, p1), (v2, p2)) in self.0.iter().zip(other.0.iter()) {
            match (v1.cmp(v2), p1.cmp(p2)) {
                (Ordering::Equal, Ordering::Equal) => continue,
                (Ordering::Equal, order) => return order.reverse(),
                (order, _) => return order
            }
        }
        Ordering::Equal
    }

    fn iter(&self) -> impl Iterator<Item=(&PRef, &usize)> {
        self.0.iter()
    }
}

/// Constructors for GrevLexTerm
impl GrevLexTerm {
    pub fn new(vars: Ctx<PRef, usize>) -> Self {
        GrevLexTerm(MonoTerm(vars))
    }

    pub fn iter(&self) -> impl Iterator<Item=(&PRef, &usize)> {
        self.0.iter()
    }
}

/// Constructors for ElimTerm
impl ElimTerm {
    pub fn new(vars: Ctx<PRef, usize>) -> Self {
        ElimTerm(MonoTerm(vars))
    }

    /// Returns true if the variable should be eliminated in the KnowledgeAnalysis.
    /// Local variables (prover-internal computations) and private uniform variables
    /// (random masks) are eliminated.
    pub fn eliminate_var(v: &PRef) -> bool {
        v.qualifier == Qualifier::Local
        || (v.qualifier == Qualifier::Private && v.distribution.is_uniform())
    }

    pub fn eliminate(&self) -> bool {
        self.0.iter().any(|(v, _)| Self::eliminate_var(v))
    }

    pub fn iter(&self) -> impl Iterator<Item=(&PRef, &usize)> {
        self.0.iter()
    }
}

/// Default constructors for Monomials
impl Default for ElimTerm {
    fn default() -> Self {
        ElimTerm(MonoTerm(Ctx::new()))
    }
}

impl Default for GrevLexTerm {
    fn default() -> Self {
        GrevLexTerm(MonoTerm(Ctx::new()))
    }
}

/// Multiplies two terms in place. (var, power) pairs are combined by adding powers
/// for common variables.
impl MulAssign for ElimTerm {
    fn mul_assign(&mut self, other: Self) {
        for (var, power) in other.0.iter() {
            *self.0.0.entry(var.clone()).or_insert(0) += power;
        }
    }
}

impl MulAssign for GrevLexTerm {
    fn mul_assign(&mut self, other: Self) {
        for (var, power) in other.0.iter() {   
            *self.0.0.entry(var.clone()).or_insert(0) += power;
        }
    }
}

/// Multiplies two terms. (var, power) pairs are combined by adding powers
impl Mul for ElimTerm {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl Mul for GrevLexTerm {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

/// Multiplies by reference
impl<'a> Mul for &'a ElimTerm {
    type Output = ElimTerm;

    fn mul(self, other: &'a ElimTerm) -> ElimTerm {
        self.clone() * other.clone()
    }
}

impl<'a> Mul for &'a GrevLexTerm {
    type Output = GrevLexTerm;

    fn mul(self, other: &'a GrevLexTerm) -> GrevLexTerm {
        self.clone() * other.clone()
    }
}

/// Display for Monomials

impl fmt::Display for ElimTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for GrevLexTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Divides two terms. (var, power) pairs are combined by subtracting powers
impl Div for ElimTerm {
    type Output = Option<Self>;

    fn div(self, other: Self) -> Option<Self> {
        self.0.div(other.0).map(|t| ElimTerm(t))
    }
}

impl Div for GrevLexTerm {
    type Output = Option<Self>;

    fn div(self, other: Self) -> Option<Self> {
        self.0.div(other.0).map(|t| GrevLexTerm(t))
    }
}

/// Divides by reference
impl<'a> Div for &'a ElimTerm {
    type Output = Option<ElimTerm>;

    fn div(self, other: &'a ElimTerm) -> Option<ElimTerm> {
        self.clone() / other.clone()
    }
}

impl<'a> Div for &'a GrevLexTerm {
    type Output = Option<GrevLexTerm>;

    fn div(self, other: &'a GrevLexTerm) -> Option<GrevLexTerm> {
        self.clone() / other.clone()
    }
}

/// Convenienec constructors from vectors of variables and exponents
impl From<Vec<(PRef, usize)>> for ElimTerm {
    fn from(vars: Vec<(PRef, usize)>) -> Self {
        ElimTerm::new(vars.into_iter().collect())
    }
}

impl From<Vec<(PRef, usize)>> for GrevLexTerm {
    fn from(vars: Vec<(PRef, usize)>) -> Self {
        GrevLexTerm::new(vars.into_iter().collect())
    }
}

/// Implement Monomial trait for GrevLexTerm
impl Monomial for GrevLexTerm {
    fn vars(&self) -> Vec<PRef> {
        self.0.vars()
    }
    fn powers(&self) -> Vec<usize> {
        self.0.powers()
    }
    fn is_constant(&self) -> bool {
        self.0.is_constant()
    }

    fn evaluate<F: Field>(&self, p: &Ctx<PRef, F>) -> F {
        self.0.evaluate(p)
    }
    fn is_divided(&self, other: &Self) -> bool {
        self.0.is_divided(&other.0)
    }

    fn lcm(&self, other: &Self) -> Self {
        GrevLexTerm(self.0.lcm(&other.0))
    }

    fn gcd(&self, other: &Self) -> Self {
        GrevLexTerm(self.0.gcd(&other.0))
    }
}

/// Implement Monomial trait for ElimTerm
impl Monomial for ElimTerm {
    fn vars(&self) -> Vec<PRef> {
        self.0.vars()
    }

    fn powers(&self) -> Vec<usize> {
        self.0.powers()
    }
    fn is_constant(&self) -> bool {
        self.0.is_constant()
    }
    fn evaluate<F: Field>(&self, p: &Ctx<PRef, F>) -> F {
        self.0.evaluate(p)
    }
    fn is_divided(&self, other: &Self) -> bool {
        self.0.is_divided(&other.0)
    }
    fn lcm(&self, other: &Self) -> Self {
        ElimTerm(self.0.lcm(&other.0))
    }
    fn gcd(&self, other: &Self) -> Self {
        ElimTerm(self.0.gcd(&other.0))
    }
}

/// Define elimination order comparison. First, we compare principals such that if any variable has
/// Principal::Any > Principal::Verifier and Principal::Any > Principal::Prover, then the same is true for MonoTerm.
/// If the principals are equal, then perform a grevlex comparison on the powers of the variables (graded, reverse lexicographic order).
impl Ord for ElimTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        let elim_self = MonoTerm(self.0.iter()
                .filter(|(var, _)| ElimTerm::eliminate_var(var))
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<PRef, usize>>());

        let elim_other = MonoTerm(other.0.iter()
                .filter(|(var, _)| ElimTerm::eliminate_var(var))
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<PRef, usize>>());

        // Compare the variables we prefer to eliminate first, using the grevlex monomial order
        match elim_self.grevlex(&elim_other) {
            Ordering::Equal => {},
            order => return order
        };

        // If they are equal, compare the remaining variables
        let other_self = MonoTerm(self.0.iter()
                .filter(|(var, _)| !ElimTerm::eliminate_var(var))
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<PRef, usize>>());

        let other_other = MonoTerm(other.0.iter()
                .filter(|(var, _)| !ElimTerm::eliminate_var(var))
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<PRef, usize>>());

        // If they are equal, compare the remaining variables
        other_self.grevlex(&other_other)
    }
}

/// Define grevlex order comparison.
impl Ord for GrevLexTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.grevlex(&other.0)
    }
}