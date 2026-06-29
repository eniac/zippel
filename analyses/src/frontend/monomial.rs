//! Structural monomial — a variable-exponent map with no semantic ordering.
//!
//! `Monomial` is `Hash + Eq` (structural: sorted `PRef` keys) but carries **no
//! `Ord`** and no notion of a "leading" term. Ordering is runtime data
//! ([`super::MonoOrder`]) owned by the backend.

use core::cmp::Ordering;
use core::ops::{Div, Mul, MulAssign};

use ark_ff::Field;
use graph::PRef;
use share::Ctx;
use std::fmt;

/// A monomial: a map from variables to positive exponents.
///
/// Stored as a `Ctx<PRef, usize>` (sorted by `PRef`) so that structurally equal
/// monomials are byte-identical for `Hash`/`Eq`. The `Ord` impl is structural
/// (by `PRef` then exponent) and is used **only** for deterministic `Display`
/// iteration — never for leading-term semantics.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Monomial(pub(crate) Ctx<PRef, usize>);

impl Monomial {
    pub fn new(vars: Ctx<PRef, usize>) -> Self {
        Monomial(vars)
    }

    pub fn vars(&self) -> Vec<PRef> {
        self.0.keys().into_iter().collect()
    }

    pub fn powers(&self) -> Vec<usize> {
        self.0.values().into_iter().collect()
    }

    /// Get the exponent of `v` in this monomial (0 if absent).
    pub fn powers_for(&self, v: &PRef) -> usize {
        self.0.get(v).copied().unwrap_or(0)
    }

    pub fn degree(&self) -> usize {
        self.powers().iter().sum()
    }

    pub fn is_constant(&self) -> bool {
        self.0.is_empty()
    }

    pub fn evaluate<F: Field>(&self, p: &Ctx<PRef, F>) -> F {
        let mut result = F::one();
        for (var, power) in self.0.iter() {
            if let Some(value) = p.get(var) {
                for _ in 0..*power {
                    result *= value;
                }
            }
        }
        result
    }

    pub fn is_divided(&self, other: &Self) -> bool {
        for (var, power2) in other.0.iter() {
            match self.0.get(var) {
                Some(power1) => {
                    if power1 < power2 {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }

    pub fn lcm(&self, other: &Self) -> Self {
        let mut lcm_powers: Vec<(PRef, usize)> =
            self.0.iter().map(|(v, p)| (v.clone(), *p)).collect();
        for (var, power2) in other.0.iter() {
            match lcm_powers.iter_mut().find(|(v, _)| v == var) {
                Some((_, power1)) => *power1 = (*power1).max(*power2),
                None => lcm_powers.push((var.clone(), *power2)),
            }
        }
        Monomial(lcm_powers.into_iter().collect())
    }

    pub fn gcd(&self, other: &Self) -> Self {
        let mut gcd_powers: Vec<(PRef, usize)> = Vec::new();
        for (var1, power1) in self.0.iter() {
            if let Some((_, power2)) = other.0.iter().find(|(v, _p)| v == &var1) {
                let min_power = (*power1).min(*power2);
                if min_power > 0 {
                    gcd_powers.push((var1.clone(), min_power));
                }
            }
        }
        Monomial(gcd_powers.into_iter().collect())
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&PRef, &usize)> {
        self.0.iter()
    }
}

impl Default for Monomial {
    fn default() -> Self {
        Monomial(Ctx::new())
    }
}

impl From<Vec<(PRef, usize)>> for Monomial {
    fn from(vars: Vec<(PRef, usize)>) -> Self {
        Monomial(vars.into_iter().collect())
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl MulAssign for Monomial {
    fn mul_assign(&mut self, other: Self) {
        for (var, power) in other.0.iter() {
            *self.0.entry(var.clone()).or_insert(0) += power;
        }
    }
}

impl Mul for Monomial {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl Div for Monomial {
    type Output = Option<Self>;
    fn div(self, other: Self) -> Option<Self> {
        if !self.is_divided(&other) {
            return None;
        }
        let mut powers1: Vec<(PRef, usize)> = self.0.iter().map(|(v, p)| (v.clone(), *p)).collect();
        for (var, power2) in other.0.iter() {
            if let Some(power1) = powers1.iter_mut().find(|(v, _)| v == var) {
                power1.1 -= power2;
            }
        }
        Some(Monomial(
            powers1.into_iter().filter(|(_, p)| *p > 0).collect(),
        ))
    }
}

impl fmt::Display for Monomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_constant() {
            return write!(f, "1");
        }
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

/// Structural `Ord` for deterministic `Display` iteration only.
/// **Not** a monomial ordering — the backend owns ordering semantics.
impl Ord for Monomial {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut a = self.0.iter().rev().peekable();
        let mut b = other.0.iter().rev().peekable();
        loop {
            match (a.peek(), b.peek()) {
                (None, None) => return Ordering::Equal,
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (Some(&(va, _pa)), Some(&(vb, _pb))) => match va.cmp(vb) {
                    Ordering::Equal => {
                        let (_, pa) = a.next().unwrap();
                        let (_, pb) = b.next().unwrap();
                        match pa.cmp(pb) {
                            Ordering::Equal => continue,
                            order => return order,
                        }
                    }
                    order => return order,
                },
            }
        }
    }
}

impl PartialOrd for Monomial {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
