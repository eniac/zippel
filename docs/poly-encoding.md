# Polynomial Encoding Spec (Phase 14)

**Status**: Normative for Zippel's polynomial type system after phase 14.
Supersedes the historical count-based interpretation that was inconsistent
with `lub_mul` / `lub_div` / `mul` / `add` degree arithmetic.

## Core invariant

The parameter `m` in every polynomial type is **always** the max
polynomial *degree*, never the coefficient count.

## Types

| Surface (Zippel) | `CTyp` (lang) | `ATyp` (graph/backend) | Coefficient count |
|---|---|---|---|
| `Poly<F, 1, m>` | `CTyp::Poly(F, 1, m)` | `ATyp::Uni(m)` | `m + 1` |
| `Poly<F, n, 1>` (n ≥ 2) | `CTyp::Poly(F, n, 1)` | `ATyp::Mle(n)` | `2^n` |
| `Poly<F, n, d>` (n ≥ 2, d ≥ 2) | `CTyp::Poly(F, n, d)` | `ATyp::VPoly(n, n·d)` | `C(n·d + n, n)` |

where `C(·, ·)` is the binomial coefficient (count of multi-indices
`(i₁, …, iₙ) ∈ ℕⁿ` with `i₁ + ⋯ + iₙ ≤ m`).

### CTyp → ATyp degree conversion

`CTyp::Poly` uses "max degree **per variable**" (`d`), while `ATyp::VPoly`
uses "max **total** degree" (`m`). The conversion is conservative:

- `Uni(m)` and `Mle(n)` are exact (no discrepancy).
- General case: `CTyp::Poly(F, n, d)` → `VPoly(n, n·d)`. The total degree
  bound `n·d` comes from the worst case where all `n` variables simultaneously
  have their maximum per-variable degree `d`. This over-approximates the
  true monomial space, but is always sound.

### `Mle(n)` effective total degree

Although `CTyp::Poly(F, n, 1)` uses per-variable degree 1, a multilinear
polynomial has total degree `n` (the monomial `x₁·x₂·…·xₙ` has total degree
`n`). Consequently, `ATyp::lub_mul` treats `Mle(n)` as having total degree
`n`:

- `Mle(n) × Mle(n)` → `VPoly(n, 2n)` (total degrees add)
- `Uni(d) × Mle(n)` → `VPoly(n, d+n)` (Uni(d) has total degree d)
- `VPoly(n,m) × Mle(v)` → `VPoly(max(n,v), m+v)`

Similarly for `lub_add`/`lub_sub`, `Mle(n)` has total degree `n` (not 1):

- `Mle(n₁) + Mle(n₂)` (n₁≠n₂) → `VPoly(max, max)` (max of total degrees)
- `VPoly(n,m) + Mle(v)` → `VPoly(max(n,v), max(m,v))`

This is why the CTyp→ATyp cross-consistency test uses containment (CTyp
path ≥ ATyp path) rather than equality: when variable counts differ, the
conservative `n·d` total-degree bound can exceed the direct `ATyp::lub_mul`
result.

Aliases defined by the lang: `Uni<F, m> ≡ Poly<F, 1, m>`,
`Mle<F, n> ≡ Poly<F, n, 1>`.

### Degenerate / boundary cases

- `Poly<F, 1, 0>` = constant polynomial (1 coefficient). Distinct from `F`
  at the type level (no implicit coercion); isomorphic in value.
- `Poly<F, 0, m>` is not a valid type (0 variables has no meaningful
  degree parameter; use `F` for scalars).
- `poly([c])` with a singleton vector is legal and yields `Poly<F, 1, 0>`.
- `coef(Poly<F, 1, 0>)` yields `[F; 1]`.

## Constructors and destructors

| Operation | Input | Output |
|---|---|---|
| `poly(v: [F; k])` | `k ≥ 1` | `Poly<F, 1, k − 1>` |
| `coef(p: Poly<F, 1, m>)` | | `[F; m + 1]` |
| `ifft(v: [F; k])` | `k ≥ 1`, power of 2 | `Poly<F, 1, k − 1>` |
| `fft(p: Poly<F, 1, m>)` | | `[F; m + 1]` |
| `mle(v: [F; 2^n])` | `n ≥ 1` | `Poly<F, n, 1>` |
| `eval(p: Poly<F, n, m>, xs: [F; k])` | `k = n` | `F` |
| `eval(p: Poly<F, n, m>, xs: [F; k])` | `k < n` | `Poly<F, n − k, m>` |
| `eval(p: Poly<F, n, m>, xs: [F; k])` | `k > n` | type error |
| `eval<i..j>(p: Poly<F, n, m>, fixed: [F; n − (j − i)])` | `0 ≤ i < j ≤ n`, step `1` | `Poly<F, j − i, m>` |
| `eval<i>(p: Poly<F, n, m>, fixed: [F; n − 1])` | unit-range sugar for `eval<i..i+1>` | `Poly<F, 1, m>` |

Selected eval fixes variables outside the half-open free range. Fixed values
are ordered as variables `[0,i)` followed by variables `[j,n)`. The backend
uses the static `Poly<F,n,m>` shape from the typed op so typed zero/constant
polynomials preserve arity even when their runtime payload is scalar-like.

## Arithmetic (lub rules)

Let `p₁ : Poly<F, n₁, m₁>`, `p₂ : Poly<F, n₂, m₂>`.

| Op | Result |
|---|---|
| `p₁ + p₂` | `Poly<F, max(n₁,n₂), max(m₁, m₂)>` |
| `p₁ − p₂` | `Poly<F, max(n₁,n₂), max(m₁, m₂)>` |
| `p₁ × p₂` | `Poly<F, max(n₁,n₂), m₁ + m₂>` |
| `p₁ / p₂` (req. `n₁ = n₂ = 1`) | `Poly<F, 1, m₁>` |
| `p₁ % p₂` (req. `n₁ = n₂ = 1`, `m₂ ≥ 1`) | `Poly<F, 1, m₂ − 1>` |
| `p : Poly<…> ± c : F` | input Poly type |
| `p : Poly<…> × c : F` | input Poly type |
| `p : Poly<…> / c : F` | input Poly type (scalar division) |

The index `m` is a degree *upper bound*, not an exact degree, so `m₁ − m₂`
would be unsound: a divisor declared `Uni<F, m₂>` may have any actual degree
`≤ m₂`, and the quotient's only sound bound is the dividend's own `m₁`.

The identity `P = D·Q + R` with `deg(R) < deg(D)` is used by the Gröbner
layer for `Uni / Uni` and `Uni % Uni`. The encoder has two branches:

- **Declared-constant divisor** (`m₂ = 0`): witnesses `q : Uni<F, m₁>` and a
  zero remainder. One row per dividend coefficient, `a[k] = b[0]·q[k]` for
  `k ∈ 0..=m₁`, plus the scalar nonzero-divisor row.
- **`m₂ > 0`**: witnesses `q : Uni<F, m₁>` and `r : Uni<F, m₂ − 1>`, with
  identity rows for every `k ∈ 0..=m₁ + m₂`. Dividend coefficients above
  `m₁` are zero; those extra rows force the high coefficients of `D·Q` to
  cancel. `m₁ < m₂` is not a special case — declared bounds do not compare
  actual degrees, so it uses the same encoding.

Polynomial-by-polynomial operations on `Mle` and `VPoly` are rejected by the
type system because multivariate division requires a term order.

Division constraints model defined program traces only. Scalar division and
`Uni(0)` division enforce `D ≠ 0` with an inverse witness `D·D⁻¹ - 1 = 0`.
Higher-degree `Uni` division enforces that at least one divisor coefficient is
nonzero through the degree chain's final `s₀ = 1` constraint.

At runtime, `coef(p)` on a value of declared type `Uni(m)` returns exactly
`m + 1` elements: the canonical Arkworks representation drops trailing zero
coefficients, so the extraction zero-pads up to the declared width (and never
truncates).

## Vec ↔ Poly length relations

These are consistency constraints enforced by `lub` whenever a `Vec` and
a `Poly` must agree (e.g., in `verify(v == p)`):

- `Vec<F, k>` is consistent with `Poly<F, 1, m>` iff `k = m + 1`.
- No implicit coercion: to cross the Vec/Poly boundary, use `poly()` or
  `coef()`.

## `num_coeffs` helper (graph/backend)

```rust
fn num_coeffs(t: &ATyp) -> usize {
    match t {
        ATyp::Uni(m)       => m + 1,
        ATyp::Mle(n)       => 1 << n,
        ATyp::VPoly(n, m)  => binomial(m + n, n),
        ATyp::Vec(_, k)    => *k,
        _                  => 1,
    }
}
```

## `multi_indices(n, m)` enumeration

`multi_indices(n, m)` must enumerate all multi-indices
`(i₁, …, iₙ)` with `0 ≤ iⱼ` and `i₁ + ⋯ + iₙ ≤ m`, in a canonical
deterministic order (e.g., degrevlex). Length = `C(m + n, n)`.

## Groebner `to_poly` slot counts

For each `Op::Ref(v, t)`:

- `t = ATyp::Uni(m)` → `m + 1` scalar slots indexed `0..=m`
  (slot `i` represents the coefficient of `xⁱ`).
- `t = ATyp::VPoly(n, m)` → `C(m + n, n)` slots, one per multi-index.
- `t = ATyp::Mle(n)` → `2ⁿ` slots, one per hypercube point.
- `t = ATyp::Vec(_, k)` → `k` slots (unchanged).

## Migration checklist (for 14.B–F)

Any site that previously wrote `m` or `Uni(n)` assuming `m`/`n` was a
coefficient count must be bumped down by 1. Concretely:

- `Uni<F, N>` (hadamard, zerocheck) where `N` was "number of
  coefficients" → `Uni<F, N - 1>`.
- `Poly<F, 1, 2>` where `2` was "3 coefficients = quadratic" →
  `Poly<F, 1, 2>` stays (quadratic = degree 2).
- `coef(p) : [F; n]` callers that allocated `n` coefficients for a
  degree-`n-1` poly are still correct because the new rule gives
  `[F; m + 1]`; only the `m` parameter shifts.

When in doubt, grep for explicit `ATyp::uni(N)` / `ATyp::vpoly(n, m)`
literals; if `N`/`m` came from a user-visible "count", subtract 1.
