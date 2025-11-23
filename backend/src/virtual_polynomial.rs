use ark_ff::Field;
use crate::{PolyVariant, PolyError};

/// Virtual Polynomial - represents a polynomial as a sum of terms, where each term
/// is a coefficient multiplied by a product of base polynomials.
/// This is useful for sum-check protocols and allows flexible representation
/// of polynomial products without explicitly computing the full expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirtualPolynomial<F: Field> {
    /// List of terms, where each term is (coefficient, vector of polynomials to multiply)
    /// The term evaluates to: coefficient * poly[0] * poly[1] * ... * poly[n-1]
    pub terms: Vec<(F, Vec<PolyVariant<F>>)>,
}

impl<F: Field> VirtualPolynomial<F> {
    /// Create a new empty virtual polynomial
    pub fn new() -> Self {
        VirtualPolynomial { terms: Vec::new() }
    }

    /// Create a virtual polynomial from a single polynomial (coefficient 1)
    pub fn from_poly(poly: PolyVariant<F>) -> Self {
        VirtualPolynomial {
            terms: vec![(F::one(), vec![poly])],
        }
    }

    /// Create a virtual polynomial from a scalar (constant term)
    pub fn from_scalar(scalar: F) -> Self {
        if scalar.is_zero() {
            VirtualPolynomial::new()
        } else {
            VirtualPolynomial {
                terms: vec![(scalar, vec![])],
            }
        }
    }

    /// Multiply two virtual polynomials
    pub fn mul_virtual(&self, other: &Self) -> Self {
        let mut result = VirtualPolynomial::new();
        for (coeff1, polys1) in &self.terms {
            for (coeff2, polys2) in &other.terms {
                let new_coeff = *coeff1 * *coeff2;
                let mut new_polys = polys1.clone();
                new_polys.extend(polys2.clone());
                result.terms.push((new_coeff, new_polys));
            }
        }
        result.simplify();
        result
    }

    /// Add two virtual polynomials
    pub fn add_virtual(&mut self, other: &Self) {
        self.terms.extend(other.terms.clone());
        self.simplify();
    }

    pub fn neg_virtual(&mut self) {
        for (coeff, _) in &mut self.terms {
            *coeff = -*coeff;
        }
    }

    /// Multiply by a scalar
    pub fn mul_scalar(&mut self, scalar: F) {
        if scalar.is_zero() {
            self.terms.clear();
        }
        for (coeff, _) in &mut self.terms {
            *coeff *= scalar;
        }
    }

    /// Evaluate univariate - the virtual polynomial at a singular point (for univariate)
    pub fn evaluate_uv(&self, point: &F) -> F {
        self.terms.iter()
            .map(|(coeff, polys)| {
                let prod = polys.iter()
                    .map(|p| p.evaluate(point))
                    .fold(F::one(), |acc, val| acc * val);
                *coeff * prod
            })
            .sum()
    }

    /// Evaluate multivariate - the virtual polynomial at a multidimensional point (n-variate)
    pub fn evaluate_mv(&self, point: &[F]) -> Result<F, PolyError<F>> {
        let mut result = F::zero();
        for (coeff, polys) in &self.terms {
            let mut prod = *coeff;
            for p in polys {
                prod = prod * p.evaluate_mv(point)?;
            }
            result += prod;
        }
        Ok(result)
    }

    /// Check if the virtual polynomial is zero
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty() || self.terms.iter().all(|(coeff, _)| coeff.is_zero())
    }

    /// Simplify by removing zero terms
    // TODO: Should also combine like terms if possible
    pub fn simplify(&mut self) {
        self.terms.retain(|(coeff, _)| !coeff.is_zero());
    }
}

impl<F: Field> Default for VirtualPolynomial<F> {
    fn default() -> Self {
        VirtualPolynomial::new()
    }
}

impl<F: Field> Add for VirtualPolynomial<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.add_virtual(&other);
        result
    }
}

impl<F: Field> Sub for VirtualPolynomial<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        other_neg.add_virtual(&self);
        other_neg
    }
}

impl<F: Field> Add for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn add(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.add_virtual(&other);
        result
    }
}

impl<F: Field> Sub for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn sub(self, other: Self) -> Self::Output {
        let mut other_neg = other.clone();
        other_neg.neg_virtual();
        other_neg.add_virtual(&self);
        other_neg
    }
}

impl<F: Field> Mul for VirtualPolynomial<F> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result.mul_virtual(&other);
        result
    }
}

impl<F: Field> Mul for &VirtualPolynomial<F> {
    type Output = VirtualPolynomial<F>;

    fn mul(self, other: Self) -> Self::Output {
        let mut result = self.clone();
        result.mul_virtual(other);
        result
    }
}

// TODO: Write tests for algebraic properties of rings, e.g., associativity, distributivity, identity elements, etc.
