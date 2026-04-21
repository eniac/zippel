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
| `Poly<F, n, m>` (general) | `CTyp::Poly(F, n, m)` | `ATyp::VPoly(n, m)` | `C(m + n, n)` |

where `C(·, ·)` is the binomial coefficient (count of multi-indices
`(i₁, …, iₙ) ∈ ℕⁿ` with `i₁ + ⋯ + iₙ ≤ m`).

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

## Arithmetic (lub rules)

Let `p₁ : Poly<F, n₁, m₁>`, `p₂ : Poly<F, n₂, m₂>`.

| Op | Result |
|---|---|
| `p₁ + p₂` | `Poly<F, max(n₁,n₂), max(m₁, m₂)>` |
| `p₁ − p₂` | `Poly<F, max(n₁,n₂), max(m₁, m₂)>` |
| `p₁ × p₂` | `Poly<F, max(n₁,n₂), m₁ + m₂>` |
| `p₁ / p₂` (req. `m₁ ≥ m₂`) | `Poly<F, max(n₁,n₂), m₁ − m₂>` |
| `p₁ % p₂` (req. `m₂ ≥ 1`) | `Poly<F, max(n₁,n₂), m₂ − 1>` |
| `p : Poly<…> ± c : F` | input Poly type |
| `p : Poly<…> × c : F` | input Poly type |
| `p : Poly<…> / c : F` | input Poly type (scalar division) |

The identity `P = D·Q + R` with `deg(R) < deg(D)` is used by the Gröbner
phase-13 layer: witnesses `q : Poly<F, nr, m₁ − m₂>` and
`r : Poly<F, nr, m₂ − 1>` where `nr = max(n₁, n₂)`.

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
