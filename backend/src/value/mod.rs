/// Group point vectors with optional precomputations an operation may use.
pub mod points;
/// Vectors that share their storage: O(1) clones and slices, copy-on-write.
pub mod shared;

mod access;
mod arith;
mod group;
mod poly;
mod sample;
mod vector;

#[cfg(test)]
mod test_division;
#[cfg(test)]
mod tests;

use crate::backends::keys::Key;
use crate::poly::virtual_polynomial::VirtualPolynomial;
use crate::value::points::Points;
use crate::value::shared::Shared;
use crate::{ABase, ATyp, Backend, Field, G1Affine, G2Affine, GT, Group};
use lang::typ::CRange;
use share::Ctx;
use std::fmt;
use std::sync::Arc;

/// A runtime value: the payload carried by a node of a scheduled DAG during
/// execution by `runtime::MutexGraph`.
///
/// Each variant fixes both an arkworks carrier type and a shape (single
/// element, flat homogeneous vector, nested vector, record, polynomial) and
/// corresponds to an `ATyp` recoverable via [`Value::typ`]. The flat `Vec*`
/// variants are not merely `Value::Vec` specializations: they let bulk
/// operations dispatch straight to batched `arkworks` routines (MSM, batch
/// affine normalization) instead of walking boxed elements. The `into_*_mut`
/// casts move a value between those representations in place, so an operand
/// silently re-shapes itself to whatever the operator needs.
///
/// A `Value` is a cheap handle (40 bytes): vectors are [`Shared`] views,
/// group elements and polynomials are behind an `Arc`, and only scalars,
/// indices and other small values are inline, so `clone()` shares data and
/// never copies it. The runtime passes values by clone, and writes copy first
/// when data is shared ([`Shared::to_mut`], `Arc::make_mut`). Build the
/// `Arc`-held variants with [`Value::g1`], [`Value::g1_affine`],
/// [`Value::g2`], [`Value::g2_affine`], [`Value::gt`] and [`Value::poly`].
#[derive(Debug, Clone, Eq)]
pub enum Value<C: Backend> {
    /// Scalars
    Index(usize),
    /// A single element of the backend scalar field `C::F`.
    Scalar(C::F),
    /// A flat vector of machine indices; the vector form of `Value::Index`.
    VecIndex(Shared<usize>),
    /// A flat vector of scalar-field elements; the dense carrier for a
    /// source-level `Vec(F, n)`.
    VecScalar(Shared<C::F>),
    /// Groups
    G1(Arc<C::G1>),
    /// A projective point of the second pairing source group.
    G2(Arc<C::G2>),
    /// An element of the pairing target group.
    GT(Arc<GT<C>>),
    /// A flat vector of projective first-source-group points, kept flat so
    /// dot products lower to a single multi-scalar multiplication.
    VecG1(Shared<C::G1>),
    /// A flat vector of projective second-source-group points.
    VecG2(Shared<C::G2>),
    /// A flat vector of pairing target group elements.
    VecGT(Shared<GT<C>>),
    /// Affine group elements
    G1Affine(Arc<G1Affine<C>>),
    /// An affine point of the second pairing source group.
    G2Affine(Arc<G2Affine<C>>),
    /// A flat vector of affine first-source-group points, the form the
    /// batched `arkworks` MSM routines consume directly, with any MSM
    /// precomputation declared for it (see [`G1Points`]).
    VecG1Affine(G1Points<C>),
    /// A flat vector of affine second-source-group points, with any pairing
    /// precomputation declared for it (see [`G2Points`]).
    VecG2Affine(G2Points<C>),
    /// Vectors of vectors etc
    Vec(Shared<Value<C>>),
    /// Record with named fields
    Record(Ctx<String, Value<C>>),
    /// Virtual Polynomial (sum-of-products of univariate or multilinear, dense or sparse)
    Poly(Arc<VirtualPolynomial<C::F>>),
    /// Unit value (the only inhabitant of type Unit)
    Unit,
    /// Boolean value (0 or 1)
    Bool(bool),
}

pub use crate::backends::{G1Points, G2Points};

impl<C: Backend> PartialEq for Value<C> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // For projective group elements, normalize before comparing
            (Value::G1(a), Value::G1(b)) => a.normalize() == b.normalize(),
            (Value::G2(a), Value::G2(b)) => a.normalize() == b.normalize(),
            (Value::VecG1(a), Value::VecG1(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(x, y)| x.normalize() == y.normalize())
            }
            (Value::VecG2(a), Value::VecG2(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(x, y)| x.normalize() == y.normalize())
            }
            // For all other variants, use structural equality
            (Value::Index(a), Value::Index(b)) => a == b,
            (Value::Scalar(a), Value::Scalar(b)) => a == b,
            (Value::VecIndex(a), Value::VecIndex(b)) => a == b,
            (Value::VecScalar(a), Value::VecScalar(b)) => a == b,
            (Value::GT(a), Value::GT(b)) => a == b,
            (Value::VecGT(a), Value::VecGT(b)) => a == b,
            (Value::G1Affine(a), Value::G1Affine(b)) => a == b,
            (Value::G2Affine(a), Value::G2Affine(b)) => a == b,
            (Value::VecG1Affine(a), Value::VecG1Affine(b)) => a == b,
            (Value::VecG2Affine(a), Value::VecG2Affine(b)) => a == b,
            (Value::Vec(a), Value::Vec(b)) => a == b,
            (Value::Record(a), Value::Record(b)) => a == b,
            (Value::Poly(a), Value::Poly(b)) => a == b,
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            // Different variants are not equal
            _ => false,
        }
    }
}

impl<C: Backend> std::hash::Hash for Value<C> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::Index(i) => i.hash(state),
            Value::Scalar(f) => f.hash(state),
            Value::VecIndex(v) => v.hash(state),
            Value::VecScalar(v) => v.hash(state),
            // Projective → affine for canonical hashing (matches PartialEq)
            Value::G1(g) => g.normalize().hash(state),
            Value::G2(g) => g.normalize().hash(state),
            Value::GT(g) => g.hash(state),
            Value::VecG1(v) => {
                v.len().hash(state);
                for g in v {
                    g.normalize().hash(state);
                }
            }
            Value::VecG2(v) => {
                v.len().hash(state);
                for g in v {
                    g.normalize().hash(state);
                }
            }
            Value::VecGT(v) => v.hash(state),
            Value::G1Affine(g) => g.hash(state),
            Value::G2Affine(g) => g.hash(state),
            Value::VecG1Affine(v) => v.hash(state),
            Value::VecG2Affine(v) => v.hash(state),
            Value::Vec(v) => v.hash(state),
            Value::Record(r) => r.hash(state),
            Value::Poly(p) => {
                let mut bytes = Vec::new();
                p.write_bytes(&mut bytes);
                bytes.hash(state);
            }
            Value::Unit => {}
            Value::Bool(b) => b.hash(state),
        }
    }
}

/// Appends the canonical encoding of `value`: each element in its backend
/// encoding, an index or a record's field count as a little-endian `u64`, a
/// boolean as one byte.
fn write_value<C: Backend>(value: &Value<C>, out: &mut Vec<u8>) {
    let u64_le = |out: &mut Vec<u8>, x: usize| out.extend((x as u64).to_le_bytes());
    match value {
        Value::Index(i) => u64_le(out, *i),
        Value::Scalar(f) => f.write_bytes(out),
        Value::VecIndex(v) => v.iter().for_each(|i| u64_le(out, *i)),
        Value::VecScalar(v) => v.iter().for_each(|f| f.write_bytes(out)),
        Value::G1(g) => g.write_bytes(out),
        Value::G2(g) => g.write_bytes(out),
        Value::GT(g) => g.write_bytes(out),
        Value::VecG1(v) => v.iter().for_each(|g| g.write_bytes(out)),
        Value::VecG2(v) => v.iter().for_each(|g| g.write_bytes(out)),
        Value::VecGT(v) => v.iter().for_each(|g| g.write_bytes(out)),
        Value::G1Affine(g) => C::G1::write_affine_bytes(g, out),
        Value::G2Affine(g) => C::G2::write_affine_bytes(g, out),
        Value::VecG1Affine(v) => v.iter().for_each(|g| C::G1::write_affine_bytes(g, out)),
        Value::VecG2Affine(v) => v.iter().for_each(|g| C::G2::write_affine_bytes(g, out)),
        Value::Vec(values) => values.iter().for_each(|v| write_value(v, out)),
        Value::Poly(poly) => poly.write_bytes(out),
        Value::Record(fields) => {
            u64_le(out, fields.len());
            for (name, value) in fields.iter() {
                u64_le(out, name.len());
                out.extend(name.as_bytes());
                write_value(value, out);
            }
        }
        Value::Unit => {}
        Value::Bool(b) => out.push(u8::from(*b)),
    }
}

/// The canonical byte encoding of `value`.
///
/// This is the encoding fed to the Fiat-Shamir transcript and used to measure
/// proof size, so it is deliberately untagged and length-free for the flat
/// vector variants; only `Value::Record` writes a field count, because field
/// order alone does not determine the byte layout. `Value::Unit` writes nothing.
pub fn value_to_bytes<C: Backend>(value: &Value<C>) -> Vec<u8> {
    let mut out = Vec::new();
    write_value(value, &mut out);
    out
}

impl<C: Backend> Value<C> {
    /// This value with every vector in a buffer of its own (see
    /// [`Shared::compact`]), for a value that outlives the run that computed
    /// it: a view would keep its whole buffer alive.
    #[must_use]
    pub fn compact(self) -> Self {
        match self {
            Value::VecScalar(v) => Value::VecScalar(v.compact()),
            Value::VecG1(v) => Value::VecG1(v.compact()),
            Value::VecG2(v) => Value::VecG2(v.compact()),
            Value::VecGT(v) => Value::VecGT(v.compact()),
            Value::VecG1Affine(v) => Value::VecG1Affine(v.compact()),
            Value::VecG2Affine(v) => Value::VecG2Affine(v.compact()),
            Value::Vec(vs) => Value::Vec(vs.into_vec().into_iter().map(Value::compact).collect()),
            Value::Record(fields) => {
                Value::Record(fields.into_iter().map(|(k, v)| (k, v.compact())).collect())
            }
            other => other,
        }
    }

    /// A first-source-group point (held behind an `Arc`).
    #[must_use]
    pub fn g1(g: C::G1) -> Self {
        Value::G1(Arc::new(g))
    }

    /// An affine first-source-group point (held behind an `Arc`).
    #[must_use]
    pub fn g1_affine(g: G1Affine<C>) -> Self {
        Value::G1Affine(Arc::new(g))
    }

    /// A second-source-group point (held behind an `Arc`: it is large).
    #[must_use]
    pub fn g2(g: C::G2) -> Self {
        Value::G2(Arc::new(g))
    }

    /// An affine second-source-group point (held behind an `Arc`).
    #[must_use]
    pub fn g2_affine(g: G2Affine<C>) -> Self {
        Value::G2Affine(Arc::new(g))
    }

    /// A pairing target group element (held behind an `Arc`: it is large).
    #[must_use]
    pub fn gt(g: GT<C>) -> Self {
        Value::GT(Arc::new(g))
    }

    /// A polynomial.
    #[must_use]
    pub fn poly(p: VirtualPolynomial<C::F>) -> Self {
        Value::Poly(Arc::new(p))
    }

    /// A vector of scalar-field elements.
    #[must_use]
    pub fn vec_scalar(xs: Vec<C::F>) -> Self {
        Value::VecScalar(xs.into())
    }

    /// A vector of projective first-source-group points.
    #[must_use]
    pub fn vec_g1(xs: Vec<C::G1>) -> Self {
        Value::VecG1(xs.into())
    }

    /// A vector of projective second-source-group points.
    #[must_use]
    pub fn vec_g2(xs: Vec<C::G2>) -> Self {
        Value::VecG2(xs.into())
    }

    /// A vector of pairing target group elements.
    #[must_use]
    pub fn vec_gt(xs: Vec<GT<C>>) -> Self {
        Value::VecGT(xs.into())
    }

    /// `points` declared as a key: an operand reused across operations (a commitment
    /// key), for which the backend may keep data ([`Backend::G1Key`]).
    #[must_use]
    pub fn vec_g1_key(points: Vec<G1Affine<C>>) -> Self {
        Value::VecG1Affine(Points::keyed(points, <C::G1Key as Key<_>>::prepare))
    }

    /// `points` declared as a key: an operand reused across operations (a verifier
    /// key), for which the backend may keep data ([`Backend::G2Key`]).
    #[must_use]
    pub fn vec_g2_key(points: Vec<G2Affine<C>>) -> Self {
        Value::VecG2Affine(Points::keyed(points, <C::G2Key as Key<_>>::prepare))
    }

    /// A vector of affine first-source-group points.
    #[must_use]
    pub fn vec_g1_affine(xs: Vec<G1Affine<C>>) -> Self {
        Value::VecG1Affine(xs.into())
    }

    /// A vector of affine second-source-group points.
    #[must_use]
    pub fn vec_g2_affine(xs: Vec<G2Affine<C>>) -> Self {
        Value::VecG2Affine(xs.into())
    }

    /// Returns an integer representing the constructor order.
    /// Higher values correspond to constructors defined earlier.
    pub fn discriminant_order(&self) -> u8 {
        match self {
            Value::Poly(_) => 19,
            Value::Index(_) => 15,
            Value::Scalar(_) => 14,
            Value::VecIndex(_) => 13,
            Value::VecScalar(_) => 12,
            Value::G1(_) => 10,
            Value::G2(_) => 9,
            Value::GT(_) => 8,
            Value::VecG1(_) => 7,
            Value::VecG2(_) => 6,
            Value::VecGT(_) => 5,
            Value::G1Affine(_) => 4,
            Value::G2Affine(_) => 3,
            Value::VecG1Affine(_) => 2,
            Value::VecG2Affine(_) => 1,
            Value::Vec(_) => 0,
            Value::Record(_) => 0,
            Value::Unit => 20,
            Value::Bool(_) => 21,
        }
    }

    /// Lifts a machine integer into the backend scalar field.
    ///
    /// Used wherever an `Index`-typed operand has to meet a field-typed one. The
    /// coercion is one-directional: indices are never recovered from `C::F`.
    pub fn scalar_from_usize(i: usize) -> Self {
        Value::Scalar(C::F::from_usize(i))
    }

    /// Returns the zero value for `typ` while preserving declared polynomial
    /// arity for typed zero polynomials.
    pub fn zero(typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Fin(r)) if r.contains(0) => Value::Index(0),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::F::zero()),
            ATyp::Base(ABase::Bool) => Value::Bool(false),
            ATyp::Base(ABase::G1) => Value::g1(C::G1::zero()),
            ATyp::Base(ABase::G2) => Value::g2(C::G2::zero()),
            ATyp::Base(ABase::GT) => Value::GT(GT::<C>::zero().into()),
            ATyp::Uni(_m) => Value::poly(VirtualPolynomial::zero_with_num_vars(1)),
            ATyp::Mle(n) => Value::poly(VirtualPolynomial::zero_with_num_vars(*n)),
            ATyp::VPoly(n, _) => Value::poly(VirtualPolynomial::zero_with_num_vars(*n)),
            ATyp::Vec(ATyp::Base(ABase::Fin(r)), n) if r.contains(0) => {
                Value::VecIndex(vec![0; *n].into())
            }
            ATyp::Vec(ATyp::Base(ABase::Scalar), n) => Value::vec_scalar(vec![C::F::zero(); *n]),
            ATyp::Vec(ATyp::Base(ABase::G1), n) => Value::vec_g1(vec![C::G1::zero(); *n]),
            ATyp::Vec(ATyp::Base(ABase::G2), n) => Value::vec_g2(vec![C::G2::zero(); *n]),
            ATyp::Vec(ATyp::Base(ABase::GT), n) => Value::vec_gt(vec![GT::<C>::zero(); *n]),
            ATyp::Vec(deref!(vt), n) => {
                let mut v = Vec::<Value<C>>::with_capacity(*n);
                for _ in 0..*n {
                    v.push(Value::<C>::zero(vt));
                }
                Value::Vec(v.into())
            }
            ATyp::Record(fields) => {
                let mut record_fields = Ctx::new();
                for (name, field_typ) in fields.iter() {
                    let v = Value::<C>::zero(field_typ);
                    record_fields.insert(name, &v);
                }
                Value::Record(record_fields)
            }
            _ => panic!("Cannot create zero value for type {}", typ),
        }
    }

    /// Creates the multiplicative identity (one) for the given type.
    pub fn one(typ: &ATyp) -> Self {
        match typ {
            ATyp::Base(ABase::Fin(r)) if r.contains(1) => Value::Index(1),
            ATyp::Base(ABase::Scalar) => Value::Scalar(C::F::one()),
            ATyp::Base(ABase::Bool) => Value::Bool(true),
            ATyp::Vec(ATyp::Base(ABase::Scalar), n) => Value::vec_scalar(vec![C::F::one(); *n]),
            ATyp::Vec(ATyp::Base(ABase::Fin(r)), n) if r.contains(1) => {
                Value::VecIndex(vec![1; *n].into())
            }
            ATyp::Uni(_) => Value::poly(VirtualPolynomial::constant_with_num_vars(C::F::one(), 1)),
            ATyp::Mle(n) | ATyp::VPoly(n, _) => {
                Value::poly(VirtualPolynomial::constant_with_num_vars(C::F::one(), *n))
            }
            ATyp::Vec(deref!(vt), n) => {
                let mut v = Vec::<Value<C>>::with_capacity(*n);
                for _ in 0..*n {
                    v.push(Value::<C>::one(vt));
                }
                Value::Vec(v.into())
            }
            _ => panic!("Cannot create one value for type {}", typ),
        }
    }

    /// Recovers the IR-level type of this runtime value.
    ///
    /// The inverse direction of [`Value::zero`] and [`Value::random`]: affine and
    /// projective points collapse to the same `ATyp`, `VecIndex` reports the
    /// tightest `Fin` range covering its contents, and a polynomial reports `Uni` or
    /// `Mle` according to its current representation.
    ///
    /// # Panics
    /// Panics if a `Value::Vec` holds elements of differing types, or if a
    /// `VecIndex` is empty and therefore has no range to report.
    /// Like [`Self::typ`], except that a univariate polynomial maps to
    /// `ATyp::uni(0)`: its kind is right but the degree is NOT meaningful.
    /// `typ()` on a `Poly` expands the lazy sum-of-products (one FFT
    /// multiplication per product term) just to read the degree; use this
    /// where only the kind of the type matters.
    pub fn shape_typ(&self) -> ATyp {
        match self {
            Value::Poly(poly) if poly.is_univariate() => ATyp::uni(0),
            _ => self.typ(),
        }
    }

    pub fn typ(&self) -> ATyp {
        match self {
            Value::Index(n) => ATyp::fin(CRange::singleton(*n)),
            Value::Scalar(_) => ATyp::scalar(),
            Value::G1(_) => ATyp::g1(),
            Value::G2(_) => ATyp::g2(),
            Value::G1Affine(_) => ATyp::g1(),
            Value::G2Affine(_) => ATyp::g2(),
            Value::GT(_) => ATyp::gt(),
            Value::VecScalar(v) => ATyp::vec_scalar(v.len()),
            Value::VecG1(v) => ATyp::vec_g1(v.len()),
            Value::VecG2(v) => ATyp::vec_g2(v.len()),
            Value::VecG1Affine(v) => ATyp::vec_g1(v.len()),
            Value::VecG2Affine(v) => ATyp::vec_g2(v.len()),
            Value::VecGT(v) => ATyp::vec_gt(v.len()),
            Value::VecIndex(v) => {
                let min = *v.iter().min().unwrap();
                let max = *v.iter().max().unwrap();
                ATyp::Vec(
                    Box::new(ATyp::fin(CRange::from_raw(min, 1, max + 1))),
                    v.len(),
                )
            }
            Value::Vec(v) => {
                let typ = v[0].typ();
                for i in v.iter().skip(1) {
                    if typ != i.typ() {
                        panic!("Mismatched types in vector {} and {}", typ, i.typ());
                    }
                }
                ATyp::Vec(Box::new(typ), v.len())
            }
            Value::Record(fields) => {
                let mut atyp_fields = Ctx::new();
                for (name, value) in fields.iter() {
                    let t = value.typ();
                    atyp_fields.insert(name, &t);
                }
                ATyp::Record(atyp_fields)
            }
            Value::Poly(poly) => {
                if poly.is_univariate() {
                    ATyp::uni(poly.degree())
                } else {
                    ATyp::mle(poly.num_vars().unwrap())
                }
            }
            Value::Unit => ATyp::unit(),
            Value::Bool(_) => ATyp::bool(),
        }
    }

    /// Whether this value is one of type `typ`: in any of the representations
    /// a value of that type takes at runtime (projective or affine points, a
    /// flat vector or a `Value::Vec`), with every length and `Fin` range
    /// checked. An index is accepted as a scalar, as arithmetic accepts it.
    ///
    /// A polynomial must have the type's shape and degree bound (see
    /// [`VirtualPolynomial::conforms_to`]).
    ///
    /// Unlike [`Self::typ`] this never panics, so it can vet a value that
    /// came from outside, such as a proof.
    #[must_use]
    pub fn conforms_to(&self, typ: &ATyp) -> bool {
        match typ {
            ATyp::Base(base) => match (base, self) {
                (ABase::Scalar, Value::Scalar(_) | Value::Index(_))
                | (ABase::G1, Value::G1(_) | Value::G1Affine(_))
                | (ABase::G2, Value::G2(_) | Value::G2Affine(_))
                | (ABase::GT, Value::GT(_))
                | (ABase::Unit, Value::Unit)
                | (ABase::Bool, Value::Bool(_)) => true,
                (ABase::Fin(range), Value::Index(i)) => in_range(range, *i),
                _ => false,
            },
            ATyp::Vec(elem, n) => match (&**elem, self) {
                (ATyp::Base(ABase::Scalar), Value::VecScalar(v)) => v.len() == *n,
                (ATyp::Base(ABase::Scalar), Value::VecIndex(v)) => v.len() == *n,
                (ATyp::Base(ABase::Fin(range)), Value::VecIndex(v)) => {
                    v.len() == *n && v.iter().all(|i| in_range(range, *i))
                }
                (ATyp::Base(ABase::G1), Value::VecG1(v)) => v.len() == *n,
                (ATyp::Base(ABase::G1), Value::VecG1Affine(v)) => v.len() == *n,
                (ATyp::Base(ABase::G2), Value::VecG2(v)) => v.len() == *n,
                (ATyp::Base(ABase::G2), Value::VecG2Affine(v)) => v.len() == *n,
                (ATyp::Base(ABase::GT), Value::VecGT(v)) => v.len() == *n,
                (elem, Value::Vec(vs)) => vs.len() == *n && vs.iter().all(|v| v.conforms_to(elem)),
                _ => false,
            },
            ATyp::Record(fields) => match self {
                Value::Record(values) => {
                    values.len() == fields.len()
                        && fields
                            .iter()
                            .all(|(name, typ)| values.get(name).is_some_and(|v| v.conforms_to(typ)))
                }
                _ => false,
            },
            ATyp::Uni(_) | ATyp::Mle(_) | ATyp::VPoly(_, _) => {
                matches!(self, Value::Poly(p) if p.conforms_to(typ))
            }
        }
    }
}

fn in_range(range: &CRange, i: usize) -> bool {
    range.start() <= i && i < range.end() && (i - range.start()).is_multiple_of(range.step())
}

impl<C: Backend> fmt::Display for Value<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Index(i) => write!(f, "{}", i),
            Value::Scalar(a) => write!(f, "{}", a),
            Value::G1(a) => write!(f, "{}", a),
            Value::G2(g) => write!(f, "{}", g),
            Value::G1Affine(a) => write!(f, "{}", Into::<C::G1>::into(**a)),
            Value::G2Affine(g) => write!(f, "{}", Into::<C::G2>::into(**g)),
            Value::GT(g) => write!(f, "{}", g),
            Value::VecScalar(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            }
            Value::VecG1(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}", i)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecG2(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}", i)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecG1Affine(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}", Into::<C::G1>::into(*i))?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecG2Affine(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}", Into::<C::G2>::into(*i))?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecGT(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}", i)?;
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            Value::VecIndex(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            }
            Value::Vec(v) => {
                write!(f, "[")?;
                for i in v {
                    write!(f, "{}, ", i)?;
                }
                write!(f, "]")
            }
            Value::Record(fields) => {
                write!(f, "{{|")?;
                for (i, (name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, value)?;
                }
                write!(f, "|}}")
            }
            Value::Poly(poly) => write!(f, "{}", poly),
            Value::Unit => write!(f, "()"),
            Value::Bool(b) => write!(f, "{}", b),
        }
    }
}
