# Bug-Hunt Findings: polynomial → Groebner translation (PR #85)

**Branch:** `groebner-poly-rebase` @ `cca62a7`
**Method:** 6 independent hunter agents (per plan
`/home/eioannidis/.claude/plans/inherited-mixing-teapot.md`).
**Status:** *Report only.* No fixes, tests, or commits per user direction.
Synthesis deduplicates and re-rates the raw hunter reports.

Severity legend (ordered):

- **soundness** — analysis says complete/ZK when the protocol is not, or
  silently emits an algebraically wrong relation.
- **termination** — panic or non-termination on legitimate input.
- **completeness** — analysis says incomplete/leaks when the protocol is
  fine (or simply fails to discharge a relation it should). Tool is too
  conservative.
- **spec-mismatch** — comment/contract drift, latent invariant, or
  optimisation that under-fires. Documented for context, not actionable
  unless flagged below.

Per-row notation: `H<n>-F<m>` = Hunter n, Finding m from its raw report.
Confidence is the synthesised confidence (sometimes adjusted down when a
single hunter's "high" was not corroborated, or up when two hunters
landed independently on the same root cause).

---

## Tier 1 — soundness (5 findings)

### S1. Dynamic-index `Op::Ram` returns whole-array vector to callers; downstream `zip` silently constrains slot 0

- **Hunters:** H5-F2 (root cause), H6-C1 (adversarial protocol exhibiting it), H6-C2 (ZK variant).
- **Location:** `graph/src/analyses/groebner/mod.rs:739-750` (the buggy fallback in `to_poly`); contrast with `graph/src/analyses/groebner/mod.rs:1321-1331` (the correctly opaque `add_op` arm).
- **Trigger:** `Op::Ram(arr, r)` where `r` is not an `Op::Value(Index(_))`. Surface example: `verify(arr[r] == claim)` with `r: F`.
- **Mechanism:** `to_poly`'s dynamic-index branch returns `self.to_poly(a)` (the full array's per-slot polynomials, length `n`). When a downstream consumer (`Op::Bin(Equ)` at lines 1113-1122, `Op::Bin(Add/Sub/Mul/Dot)`, `Op::Vec`, …) `zip`s that against the other operand (length 1 for a scalar literal), `zip` truncates to length 1 and emits *one* basis row equating the result to `arr[0]`. The verifier check is then accepted as if it pinned slot 0 — an unsound reduction of a dynamic-access claim. Note the asymmetry with `add_op`'s `Op::Ram` arm, which correctly keeps everything opaque.
- **Adversary protocol** (from H6-C1):
  ```
  proto bad_ram<F: Field>(private arr: [F; 4], public claim: F, public idx: F)
      where true {
      let r = random<F>;
      a <- arr[idx] * r;
      b <- claim * r;
      verify(a == b)
  }
  ```
  Predicted verdict: `complete`. Sound verdict: `incomplete` (the prover can choose `arr` after seeing `claim`).
- **Confidence:** **high.** Two hunters converged from different starting points (code review vs adversarial synthesis); the `zip` truncation is mechanical.

### S2. Heterogeneous-poly `Op::Bin(Mul)` falls through to coefficient-wise zip with mismatched slot enumerations

- **Hunters:** H1-F6 (code review), H6-C6 (adversarial VPoly × Mle protocol).
- **Location:** `graph/src/analyses/groebner/mod.rs:1042-1055` (the fallback arm of `Op::Bin(BinOp::Mul, …)` dispatch).
- **Trigger:** Any `Mul` whose operand pair is NOT `(VPoly(n, ma), VPoly(n, mb))` with equal `n` or `(Mle(n), Mle(n))`. Concretely: `VPoly × Uni`, `Mle × Uni`, `Uni × Uni`, `VPoly(n) × VPoly(m)` with `n ≠ m`, `VPoly × Mle`, `Mle × Vec`, etc. — all admitted by `ATyp::lub_mul` (`backend/src/types.rs:437-477`).
- **Mechanism:** The fallback `to_poly(a).zip(to_poly(b)).enumerate().for_each(|(i, …)| basis += a_i * b_i - var(pr[i]))` does coefficient-wise pointwise multiplication. For the heterogeneous cases:
  - The operands enumerate their slots in *different bases* (e.g., VPoly uses graded-lex multi-indices via `multi_indices(n, m)`, Uni uses degree slots). Pairing slot `i` of one with slot `i` of the other equates monomials from disjoint bases.
  - `zip` truncates to `min(len(a), len(b))`, so the long operand's trailing slots are completely unconstrained — the result PRef has slots with no basis row, free for a malicious prover to set.
- **Adversary protocol** (from H6-C6):
  ```
  proto bad_mixed_mul<F: Field>(
      public p: Poly<F, 2, 2>, public q: Mle<F, 2>, public x: F, public y: F)
      where true {
      let r = p * q;
      let e = eval(r, [x, y]);
      verify(e == 0)
  }
  ```
  `multi_indices(2, 2)` has 6 slots, `hypercube(2)` has 4. `zip` drops two slots; the basis cannot constrain the high-degree coefficients of `r`. Predicted: `complete`. Sound: `incomplete`.
- **Confidence:** **high.** Two independent corroborations.

### S3. `Op::Record` fields with identical `ATyp` collapse onto the same `PRef` key

- **Hunters:** H5-F3 (root cause analysis), H6-C7 (adversarial record protocol).
- **Location:** `graph/src/analyses/groebner/mod.rs:1370-1381`.
- **Trigger:** Any `Op::Record` whose two or more fields share the same `ATyp` (e.g., `{ x: scalar, y: scalar }`).
- **Mechanism:** Per-field recursive call builds `sub_pr = PRef { typ: sub_op.typ(), index: 0, ..pr.clone() }`. The non-`typ` fields (`reference`, `qualifier`, `distribution`, `from_transcript`, `name`, `index`) are inherited from the record's `pr`, and `index` is fixed at 0. Two same-typed fields produce **structurally equal** sub-PRefs under `PRef`'s derived `PartialEq`. The second field's `add_op` overwrites the first field's `pl`/`np` entry via `Ctx::insert`. Any basis row already emitted referencing slot 0 of the record now points to a `pl` mapping that has been replaced. The downstream effect: `r.x` and `r.y` end up bound to the second field's value, so the basis records `r.x = (defn of r.y)` — a false equality.
- **Adversary protocol** (from H6-C7):
  ```
  proto bad_record<F: Field>(private a: F, private b: F, public claim: F)
      where true {
      let rec = {| x: a, y: b |};
      let t = rec.x;
      verify(t == claim)
  }
  ```
  Comment at lines 1364-1369 acknowledges field offsets are "deferred", but the current encoding is worse than imprecise — it inserts *incorrect* equalities. (Also depends on S4 via `Op::Proj`.)
- **Confidence:** **high.**

### S4. `Op::Proj` has no `add_op` / `to_poly` arm — projections are uniformly opaque, never linked to the producing record

- **Hunters:** H5-F5.
- **Location:** `graph/src/analyses/groebner/mod.rs:1382-1384` (the catch-all `_ => self.np.insert(&pr, &op)` is what `Op::Proj` falls through to). `Op::Proj` is defined in `backend/src/op.rs:81` and lowered at `graph/src/lib.rs:1968-1974`.
- **Trigger:** Any source that reads `record.field` and the record came from anywhere — including the literal `Op::Record` path.
- **Mechanism:** Neither `to_poly` (lines 693-843) nor `add_op` (lines 909-1386) matches `Op::Proj(record_op, field_name, _)`. Every projection PRef ends up in `np` as a fresh opaque variable, with no basis row tying it to the producer record's field-slot polynomial. Combined with S3 (which loses field layout on the producer side too), every record field read is **doubly opaque**: the producer collapsed the field bindings, and the consumer has no arm to look up which slot to project.
- **Severity classification:** flagged here as soundness because of the *interaction* with S3 (the catch-all silently accepts whatever pseudo-equality the basis already contains). On its own, treating proj as opaque is sound-but-incomplete; in combination it can enable downstream unsound reductions through aliased bindings.
- **Confidence:** **medium-high** (sound vs. completeness classification depends on whether S3 is fixed first; the *implementation gap* is high confidence).

### S5. Coverage gap: `Op::Reduce` with non-`{Add,Sub,Mul,Concat}` operator emits no relation; verifier checks become trivially accepted

- **Hunters:** H6-C4 (`&&`/`==`), H6-C5 (`Pow`), H6-C9 (`Div` leak), all variations of the same root cause.
- **Location:** `graph/src/analyses/groebner/mod.rs` `reduce_unfold` (search for it; per H6, the supported set is `Add | Sub | Mul | Concat`; `Pow | Div | Rem | Equ | And | Dot` all return `None`).
- **Trigger:** Any `reduce(op, v)` whose `op` is `==`, `&&`, `^`, `/`, `%`, or `dot`. Parser permits all `bin_op` variants in reduce position.
- **Mechanism:** Returning `None` from `reduce_unfold` sends the op into `np` (opaque). A verifier check `verify(t == claim)` where `t` was produced by an unsupported `reduce` reduces to `var(opaque_t) - var(claim) = 0` in the basis. Since both are opaque vars unconstrained elsewhere, the basis admits the row trivially and the analysis says "complete" — a false positive on soundness.
- **Adversary protocol** (from H6-C4):
  ```
  proto bad_reduce<F: Field>(private a: F, private b: F, public claim: Bool)
      where true {
      let v = [a == b, a == b];
      let t = reduce(&&, v);
      verify(t == claim)
  }
  ```
  Predicted: `complete`. Sound: `incomplete`.
- **Confidence:** **medium-high.** Mechanically clear, depends on which reduce ops actually parse — H6 verified `^` does; `==`, `&&`, `/` likely do via `bin_op`; confirm during fix phase.

---

## Tier 2 — termination (3 findings)

### T1. `to_poly`'s `Op::Value(v)` arm panics on every unsupported `Value` variant (no guard)

- **Hunters:** H5-F1.
- **Location:** `graph/src/analyses/groebner/mod.rs:737` (the `Op::Value(v) => self.to_poly_value(v)` line); `to_poly_value` itself at lines 501-522 has `_ => unreachable!("Unsupported value: {}", v)`.
- **Trigger:** Any DAG that flows `Op::Value(v)` for `v ∈ {G1, G2, GT, VecG1, VecG2, VecGT, G1Affine, G2Affine, VecG1Affine, VecG2Affine, Record, Poly}` into a context that calls `to_poly` (i.e., from `Op::Bin(Equ/Add/Sub/Mul/Dot)`, `Op::Vec`, `Op::Ram` dynamic-index fallback, `Op::Pair`, `Op::Reduce`, `Op::Evaluate`).
- **Mechanism:** `add_op`'s `Op::Value(v)` arm at lines 1282-1309 *does* guard with a `match` that routes unsupported variants to `self.np`. The sibling `to_poly` arm at line 737 has no such guard. Any literal of a non-scalar type embedded in an algebraic expression aborts the analysis with a panic.
- **Severity:** classified as termination because the immediate effect is panic; secondary concern is that surrounding error-handling code may swallow the panic and treat the analysis as silently failed (would worsen to soundness).
- **Confidence:** **high.**

### T2. Buchberger non-termination beyond `VPoly(2, 2)`

- **Hunters:** H4-F1.
- **Location:** `graph/src/analyses/groebner/buchberger.rs:176-262` (`buchberger()` main loop); manifest in `graph/src/analyses/completeness.rs:592-629` (`mle_eval_product_completeness` marked `#[ignore]`).
- **Trigger:** Any `VPoly(n, m)` completeness check with `n ≥ 2` and `m ≥ 2`. H4 reasons by pair count that `VPoly(2, 3)` and `VPoly(3, 2)` are at least as bad as the known-bad `VPoly(2, 2)`.
- **Mechanism:** Buchberger pair count is O(|G|²) and |G| grows with every non-zero S-polynomial remainder. With `n·m` variables and degree-2 generators forming products like `eq_i · x_j`, each S-polynomial can raise the working degree, and the pair-skip criteria don't fire often enough to control growth in this regime.
- **Severity:** termination, but the user's `#[ignore]` indicates this is a *known* live limit, not a regression introduced by the PR. Flagged for documentation.
- **Confidence:** **medium** (extrapolation, not measured).

### T3. Buchberger pair-skip "second criterion" fails for witnesses with `i < l` — extra work, not unsoundness

- **Hunters:** H4-F3.
- **Location:** `graph/src/analyses/groebner/buchberger.rs:282-291`.
- **Trigger:** Any input where a valid witness `g_i` for the lcm/second-criterion skip has `i < l` (the lower of the two pair indices).
- **Mechanism:** Pairs are stored in `seen` with smaller index first (set at lines 195-198, 252-255), but the check uses `seen.contains(&(l, i))` and `seen.contains(&(i, k))`. When `i < l`, the witness pair was stored as `(i, l)`, so the lookup returns false. The optimisation under-fires; valid witnesses are not recognised; pairs that could be skipped get processed; Buchberger does extra work. The resulting basis is still correct (skipping too few pairs is conservative).
- **Severity:** termination / performance regression, NOT soundness. Worth fixing because it amplifies T2 in pathological cases.
- **Confidence:** **high.**

---

## Tier 3 — completeness / spec gaps (5 findings)

### C1. `Op::Interpolate` (binary form) is opaque — no Lagrange basis row emitted

- **Hunters:** H3-F4, H6-C3 / C3b.
- **Location:** `graph/src/analyses/groebner/mod.rs:1132-1136`.
- **Trigger:** Any protocol that calls `interpolate(points, evals)` and later relies on a Lagrange identity (e.g., `eval(p, points[i]) == evals[i]`).
- **Mechanism:** The arm registers the op in `np` with no basis row. Lagrange constraints `eval(p, points[i]) = evals[i]` are absent. Two protocol families affected (per H3): sumcheck, fft_interpolate_random.
- **Type A risk (soundness):** H6-C3b sketches a round-trip protocol where the analysis may accept a false `verify(eval(interpolate(points, evals), points[0]) == claim)` because both sides become opaque vars and trivially reduce to opaque-vs-opaque. Confidence on Type A: medium — depends on whether `Op::Evaluate` falling back to opaque on an opaque `p` cancels correctly. Worth checking concretely.
- **Confidence:** **high** for the completeness/coverage gap; **medium** for the conditional Type A escalation.

### C2. `Op::Fft::typ()` and the runtime `value_fft()` disagree on output length when `m+1` is not a power of two

- **Hunters:** H3-F3 (already flagged in prior audit by user; reconfirmed).
- **Location:** type spec at `backend/src/op.rs:245` (via `coef_typ_from_poly` at lines 149-156); runtime at `backend/src/config.rs:184-186` and arkworks `Radix2::new` padding.
- **Trigger:** `Op::Fft(p)` where `p : Uni(m)` and `m + 1` is not a power of two (e.g., `Uni(2)` → 3 coefficients).
- **Mechanism:** Type says `Vec<F, m+1>`. Runtime pads coefficient vector to `(m+1).next_power_of_two()` and produces that many evaluations. For `m = 2`: type 3 vs runtime 4. The analysis layer inherits the type (3 rows emitted), but a concrete prover transcript produces 4 evaluations, so an extra evaluation is unconstrained.
- **Severity:** soundness *adjacent* (mismatched layers can mask false acceptance) — but classified as spec-mismatch / completeness here because the two recent fixture tests (`pbt_fft_poly_to_vec_per_spec`, `coef_eval_test`) were already worked around with size choices that avoid the padding interaction. The underlying inconsistency persists.
- **Confidence:** **high.**

### C3. `Op::Evaluate` arm has no `debug_assert!` that `polys.len() == num_coeffs(pr.typ)`

- **Hunters:** H2-F6, related to H2-F1 (`xs : Uni(k)` shape disagreement).
- **Location:** `graph/src/analyses/groebner/mod.rs:1239-1252`. Contrast: `Op::Poly | Op::Mle | Op::Coef` arm at lines 1196-1203 *does* have the assertion.
- **Trigger:** Any path where `eval_to_poly` returns fewer polys than `num_coeffs(pr.typ)` requires. H2 demonstrates this concretely for `xs : ATyp::Uni(k)` where `eval_to_poly` uses `k = xs_polys.len() = k + 1` (m+1 convention) but `op.rs:263` decodes `Uni(n)` as length-`n`, producing an off-by-one in expected `k`.
- **Mechanism:** When `polys.len() < num_coeffs(pr.typ)`, the loop `for (i, poly) in polys.into_iter().enumerate()` binds only the low slots; high slots of `pr` are silently unconstrained. A malicious prover can set them freely.
- **Severity:** soundness in principle, but the only documented triggering path (`xs : Uni(_)`) is not exercised by any current `.zippel` example (per H2). Listed in Tier 3 because the underlying mismatch is a latent invariant violation; promote to Tier 1 if the trigger turns out to be reachable in practice.
- **Confidence:** **medium.**

### C4. `Op::Pair` always emits a single basis row regardless of `pr.typ`'s slot count

- **Hunters:** H5-F4.
- **Location:** `graph/src/analyses/groebner/mod.rs:1342-1357` (and symmetric `to_poly` arm at 800-813).
- **Trigger:** Any future encoding that gives GT a multi-slot representation (e.g., `VecGT`, or pair-of-coords G1/G2 layouts).
- **Mechanism:** Code reads `to_poly(a).into_iter().next().unwrap_or_else(zero)` and emits one row. Today GT is single-slot, so this is correct. Latent if encoding changes.
- **Severity:** spec-mismatch (latent). Not actionable now; flagged for tracking. Comment at lines 1339-1341 ("matching pair expressions cancel under Buchberger") overstates current capability — listed for documentation accuracy.
- **Confidence:** **medium.**

### C5. `Op::Ifft` `pl[pr[j]] = var(pr[j])` self-binding looks tautological but is intentional

- **Hunters:** H3-F5 (negative result, but worth recording).
- **Location:** `graph/src/analyses/groebner/mod.rs:1158-1162`.
- **Mechanism:** The N DFT-row basis constraints carry the algebraic content; the `pl` self-binding is just visibility plumbing so `find_ref` resolves to a placeholder. No basis-level tautology — `inline` (marked `#[allow(dead_code)]`) would substitute `var(pf)` with `var(pf)`, a no-op. Confirmed correct.
- **Severity:** spec-mismatch (negative finding). Recorded for cross-reference only.
- **Confidence:** **high** (negative).

---

## Tier 4 — verified-correct items (negative findings)

Recording these explicitly so the next pass doesn't re-audit them.

| Item | Hunter | Verdict |
|---|---|---|
| Mle×Mle per-variable coefficient table `[[[1,-2,1],[0,1,-1]],[[0,1,-1],[0,0,1]]]` matches `eq(b,x)·eq(b',x)` exactly | H1-F3 | correct |
| Mle×Mle inner-loop scalar-zero short-circuit control flow | H1-F4 | correct |
| MLE eq-polynomial closure `if bi == 1 { x } else { 1-x }` | H2-F3 | correct |
| Horner-style univariate evaluation accumulator (degree-0 first) | H2-F4 | correct |
| `SparsePolynomial::pow` uses true polynomial exponentiation | H2-F5 | correct |
| Partial-VPoly "substitute first k variables" convention matches arkworks `MultilinearExtension::fix_variables` | H2-F2 | correct |
| DFT row loop bounds, `ω = get_root_of_unity(N)` indexing `ω^{i·j}` | H3-F1 | correct |
| `get_root_of_unity` returns `Some` exactly when N is a power of two ≤ 2^TWO_ADICITY (32 for BLS12-381 Fr) | H3-F2 | correct |
| `GrevLexTerm` ordering implements true grevlex (not lex) | H4-F4 | correct |
| `ElimTerm` ordering correctly places eliminate-variable monomials as leaders | H4-F5 | correct |
| `SparsePolynomial::s_poly` formula and sign | H4-F6 | correct |
| Zero-polynomial edge cases (empty terms, leading_term returns None) | H4-F7 | correct |
| Reduce non-determinism under rayon `find_any` is concurrency-safe; final-basis correctness unaffected by intermediate divisor choice | H4-F2 | correct (with caveat: intermediate non-Gröbner bases under rayon may produce structurally different reduced bases run-to-run; the *ideal* is the same; flag if observability matters) |
| VPoly×VPoly skip-guard at lines 966-968 is unreachable for well-typed input | H1-F1 | defensive only |
| VPoly×VPoly `position().expect()` at lines 970-973 cannot panic for well-typed input | H1-F5 | safe (same invariant as above) |
| Mle×Mle `mr >= 2` guard does not currently admit `mr > 2` because `ATyp::lub_mul(Mle, Mle) = vpoly(_, 2)` | H1-F2 | safe; recommend tightening to `mr == 2` |

---

## Reading the supervisor's confidence column

Two hunters converging on the same root cause (S1, S2, S3) is the strongest signal: independent reads, same conclusion. Items confirmed by only one hunter (T1, T3, C2, C3, C4) are not weaker findings per se — but they should be the first to revisit if the next phase wants to spot-check.

Negative findings in Tier 4 came from one hunter each. They are listed for future-iteration pruning, not as guarantees.

---

## Suggested next steps (for user approval, not initiated)

If you greenlight follow-up work, the natural ordering is:

1. **S1, S2, S3, S5** — patch the soundness bugs first. Each has an adversarial protocol that can be pinned as a failing regression test.
2. **T1** — adding the `Op::Value` guard parity in `to_poly` is a one-line fix; uncontroversial.
3. **S4** — add an `Op::Proj` arm (depends on choosing a record layout; coordinate with S3 fix).
4. **C1** — emit Lagrange basis rows for `Op::Interpolate(points, evals)`.
5. **C2** — reconcile `Op::Fft::typ()` with the runtime padding (either truncate output or widen type).
6. **C3** — add the missing `debug_assert!` in the `Op::Evaluate` arm.
7. **T3** — fix the `seen.contains(&(l, i))` lookup to canonicalise pair ordering.
8. **T2, C4, C5** — track but don't fix in this pass.

All of the above are deferred to a separate phase. PR #85 stays mergeable in its current shape; whether the soundness items should block merge is a *call you make*, not me.
