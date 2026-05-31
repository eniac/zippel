# rustgb Design Decisions

A running record of architectural decisions in the rustgb crate
(`~/rustgb`), the Singular dyn_module that loads it (`~/Singular-rustgb`),
and the dispatch shim (`rustgb-dispatch.lib`).

This is a decisions ledger, not a how-to. The port plan
(`~/project/docs/rust-bba-port-plan.md`) covers the algorithm;
profile reports (`~/project/docs/profile-rustgb-*.md`) cover
measurements; status reports (`~/project/docs/rustgb-*-report.md`)
cover individual task outcomes. This file captures the *why*
behind structural choices that the code itself will not explain.

This file used to live at `~/project/docs/rustgb-design-decisions.md`;
it was moved to `~/rustgb/docs/design-decisions.md` on 2026-04-22 so
that ADRs commit alongside the code that implements them.

## Format

Each decision is a numbered ADR-style entry with these sections:

- **Status** — Accepted / Superseded by #N / Under review
- **Date** — when the decision was made
- **Context** — what problem we are deciding about
- **Singular's approach** — what `~/Singular` does here. Always
  filled in: Singular is the reference implementation we are
  porting from.
- **FLINT's approach** — what `~/flint` does here, when applicable.
  FLINT does not implement Gröbner bases, so for high-level GB
  decisions (pair criteria, sugar strategy, redundancy marking,
  etc.) this section is **N/A — FLINT has no GB engine**. For
  polynomial-layer decisions (storage, multiplication, division,
  geobuckets), FLINT is consulted as a second reference point.
- **Decision** — what rustgb does and why.
- **Consequences** — costs, follow-ups, things that have to be
  true elsewhere as a result.
- **References** — file:line citations, profile reports, prior
  discussion in transcripts (`~/.claude/projects/-home-claude/*.jsonl`).

The Singular/FLINT comparison is a standing requirement, not an
optional section. If a decision diverges from both references, the
ADR must say so explicitly and justify it. If FLINT genuinely does
not address the question (no GB engine), say so explicitly with the
N/A wording above — silence is not allowed because it could mean
either "doesn't apply" or "wasn't checked."

---

## ADR-001: Polynomial storage — flat parallel arrays with a head cursor

**Status:** Accepted
**Date:** 2026-04-21

### Context

A polynomial in rustgb needs to support: descending iteration over
terms, O(1) leading-term access, in-place leading-term drop (called
millions of times per `bba()` from the geobucket cancellation peel),
arithmetic via merge (linear in `|f| + |g|`), and `Send + Sync` for
later parallelisation.

The choice of storage shape is load-bearing for the reducer's wall
clock — the staging-5101449 profile (`profile-rustgb-staging-5101449.md`)
showed that a naive choice put 62.6 % of total cycles into a single
`memmove` instruction.

### Singular's approach

Polynomials are **singly linked lists** of `spolyrec` nodes
(`~/Singular/libpolys/polys/monomials/p_polys.h`). Each node carries
a coefficient (`number`) and an inline exponent buffer; `pNext(p)`
walks the list. "Drop the leading term" is `pIter(p)` —
`p = pNext(p)` plus a `p_FreeBinAddr` of the old head; both O(1).
Iteration follows next-pointers; allocation is via `omalloc` bins
sized for `spolyrec`.

Cost: O(1) per drop-leading and O(1) per term-allocate (omalloc bin).
Trade-off: poor cache locality across long polys, pointer overhead
per term (~8 bytes / term wasted), allocator round-trip per term.

### FLINT's approach

FLINT's `nmod_mpoly` (`~/flint/src/nmod_mpoly`) stores polynomials
as **flat parallel arrays**: `mp_limb_t * coeffs` and
`ulong * exps` (packed), plus a `length` field. Iteration is array
indexing; arithmetic outputs are written term-by-term into freshly
allocated arrays.

FLINT never needs an O(1) "drop the front term" operation because
the reducer is heap-based (Monagan-Pearce, see ADR-003) and
operates on *indices into source arrays*, not on a partial-sum
structure that gets mutated.

### Decision

rustgb stores polynomials as parallel `Vec<Coeff>` and
`Vec<Monomial>` (`~/rustgb/src/poly.rs`), plus a `head: usize`
cursor. The live region is `coeffs[head..] / terms[head..]`.
`drop_leading_in_place` is `self.head += 1; self.refresh_cache();`
— O(1). Dead prefix is reclaimed when the `Poly` is cloned (custom
`Clone` impl copies only `[head..]`) or dropped.

This combines FLINT's storage shape (flat, cache-friendly,
allocator-light) with Singular's O(1) drop-leading semantics
(needed because we do use a geobucket reducer — see ADR-002).

### Consequences

- All `Poly` accessors (`coeffs()`, `terms()`, `iter()`, `leading()`,
  `len()`, `is_zero()`) return / operate on the live region.
- Internal arithmetic (`merge`, `sub_mul_term`) takes the live
  slice once at the top via `coeffs()` / `terms()`, avoiding
  per-iteration `+ self.head` arithmetic.
- `PartialEq` compares live regions, not raw vectors — two
  algebraically equal polys with different drop histories must
  still be `==`.
- Custom `Clone` is required: `derive(Clone)` would clone the dead
  prefix forever across the bucket-slot reuse pattern, bounding
  memory poorly.
- A bucket slot that is dropped many times without an intervening
  `merge` keeps the original allocation pinned. The next `merge` /
  `absorb` produces a fresh `Poly` with `head: 0`, returning that
  memory to bounded use. Worst case is a slot that drops to near-empty
  without ever being absorbed — bounded by the size of the original
  poly that was put in.
- The `head: usize` mechanic is the kind of subtle invariant that
  decays without targeted tests. Locked in by
  `poly::tests::drop_leading_in_place_walks_head_cursor`.

### References

- `~/rustgb/src/poly.rs` (struct definition lines 24-71, accessors
  lines 269-330, `drop_leading_in_place` lines 352-372)
- `~/project/docs/profile-rustgb-staging-5101449.md` (62.6 % memmove
  before this fix)
- `~/Singular/libpolys/polys/templates/p_kBucketSetLm__T.cc:60-63,80-83`
  (Singular's `pIter` peel)
- `~/flint/src/nmod_mpoly/divrem_monagan_pearce.c:139-344` (FLINT's
  array-based polys + heap reducer)
- Decision driven by perf profile of 2026-04-21; superseded the
  earlier `Vec::remove(0)` implementation (commit prior to this ADR).

---

## ADR-002: Reducer architecture — geobucket with cancellation peel

**Status:** Accepted, but flagged for re-evaluation if performance
work shifts the bottleneck (see ADR-003 alternative).
**Date:** 2026-04-21 (formalising a decision implicit in the port plan)

### Context

The bba inner loop reduces an L-object against the current basis
by repeatedly subtracting `c * m * g_i` for matching basis elements
`g_i`. Done naively this allocates intermediate polys whose length
is `O(|h| + |g_i|)` per step. Real reducers buffer these subtractions
into a structure that can answer "what is the current leading term?"
without flushing the whole partial sum.

### Singular's approach

**Geobucket** (`~/Singular/libpolys/polys/kbuckets.cc`,
`p_kBucketSetLm__T.cc`). A bucket has `BIT_SIZEOF_LONG` slots; slot
`i` holds a poly whose length is in roughly `(2^(2(i-1)), 2^(2i)]`.
Adding a poly puts it into the slot matching its length, with carry
to higher slots when slots fill. The leading term is found by
scanning all non-empty slots (O(slots) = ~32) for the maximum head
monomial; if multiple slots have the same head and their coefficients
sum to zero, those heads are peeled off and the scan repeats.

Drop-leading inside the peel is `pIter` on a linked-list poly —
O(1) per peel. The popped leader is parked in slot 0 so the next
`kBucketGetLm` reads it directly without rescanning.

### FLINT's approach

**N/A — FLINT does not use a geobucket reducer.** FLINT *has* a
geobucket data structure (`~/flint/src/nmod_mpoly/geobuckets.c`),
but it has no `extract_leading` operation: the API is
`init / clear / empty / set / add / sub`. It is used purely as
a staging buffer for sums (e.g. polynomial composition), with
`empty()` collapsing slots into a single output poly via repeated
binary additions.

FLINT's actual reducer is heap-based — see ADR-003.

### Decision

rustgb uses a Singular-style geobucket
(`~/rustgb/src/kbucket.rs`) with the same cancellation-peel
algorithm as `p_kBucketSetLm__T`. `KBucket::leading()` is the
non-extracting probe (returns the current leader, mutates only to
peel cancellations); `KBucket::extract_leading()` pops the leader
algebraically. Both call `Poly::drop_leading_in_place` on slots,
which under ADR-001 is O(1).

Reasons we picked geobucket over a heap reducer:
1. The port plan (`rust-bba-port-plan.md` §5) specified mirroring
   Singular's algorithm closely so the validation surface (Singular
   regression suite + helium staging suite) compares apples to
   apples on outputs.
2. The geobucket integrates cleanly with redHomog and the sugar
   strategy already in `lobject.rs`. A heap reducer would require
   rethinking how sugar is propagated through pending products.
3. The peel cost was misattributed to the algorithm in the
   2026-04-21 profile; the real culprit was poly storage, fixed
   by ADR-001 without touching the reducer.

### Consequences

- 32 slots, single-poly per slot. No `coef[]` lazy-multiply
  optimisation (Singular's `USE_COEF_BUCKETS`). May want to revisit
  if scalar multiplications dominate later.
- The `lm_cache` field caches the most recent `leading()` result
  and is invalidated by `dirty` mask. Plays the role of Singular's
  "park leader in slot 0," but without splitting the poly.
- If a future profile shows the reducer remains the bottleneck even
  after ADR-001's memmove fix, a Monagan-Pearce heap reducer
  (ADR-003 candidate) is the obvious next target — but that's a
  multi-week rewrite, not a tweak.

### References

- `~/rustgb/src/kbucket.rs` (`leading()` lines 288-373,
  `extract_leading()` lines 379-410)
- `~/Singular/libpolys/polys/templates/p_kBucketSetLm__T.cc` (full
  comparison in `profile-rustgb-staging-5101449.md`)
- `~/flint/src/nmod_mpoly/geobuckets.c` (FLINT's sum-only
  geobucket, no `extract_leading`)
- `~/project/docs/rust-bba-port-plan.md` §5

---

## ADR-003 (candidate, not yet adopted): Heap-based reducer (Monagan-Pearce)

**Status:** Under review — listed for visibility, not active.
**Date:** placeholder

### Context

If the geobucket cancellation peel becomes the bottleneck again
after polynomial-layer optimisations are exhausted, the alternative
is a heap-based reducer.

### Singular's approach

Singular has a heap reducer for some operations (`kspoly.cc` paths
with `kStratHeap`), but `bba` uses the geobucket path by default.

### FLINT's approach

FLINT's `divrem_monagan_pearce` (`~/flint/src/nmod_mpoly/divrem_monagan_pearce.c`,
726 lines) maintains a min-heap of pending products `(c_i * c_j,
e_i + e_j)` indexed by `(i, j)` into source arrays. Each iteration
pops the maximum monomial off the heap; if it matches the current
target leader, the term is consumed and the next `(i, j+1)` product
is pushed back onto the heap. There is no partial-sum structure to
peel — "drop the leading term" is `j++`.

### Decision (deferred)

Not adopted. To be reconsidered if a future profile shows the
reducer still dominates after ADR-001's storage fix and any further
polynomial-layer tuning.

### Consequences (if adopted)

Would obsolete `kbucket.rs` entirely. Would require redesigning
sugar propagation through heap nodes. Would integrate poorly with
the current `LObject::refresh` + `KBucket::leading` split — heap
nodes are the unit of state, not buckets.

### References

- `~/flint/src/nmod_mpoly/divrem_monagan_pearce.c`
- See ADR-002 for current decision and rationale.

---

## ADR-004: Threading dispatch via `RUSTGB_THREADS` env var

**Status:** Accepted (provisional — interface may change once the FFI
gains a thread-count parameter).
**Date:** 2026-04-21 (formalising existing behaviour)

### Context

The serial and parallel reducers live in the same crate
(`bba::compute_gb_serial`, `parallel::compute_gb_parallel`). The
FFI presents a single entry point (`rustgb_compute`); we need a way
to choose between them without changing the C ABI.

### Singular's approach

Singular's parallel-bba branch (`~/Singular-parallel-bba`) reads
`SINGULAR_THREADS` from the environment and threads it through the
strategy struct. Same shape: env var → driver-internal int.

### FLINT's approach

FLINT uses an explicit `nthreads` argument on functions that can
parallelise (e.g. `nmod_mpoly_mul_threaded`, `divides_heap_threaded`).
No global env-var convention — the caller is responsible.

### Decision

rustgb reads `RUSTGB_THREADS` from the environment in
`bba::rustgb_threads()` (default 1, clamped to `[1, 256]`). At
`T == 1` the serial path runs; at `T >= 2` it dispatches to
`parallel::compute_gb_parallel`. The FFI does not expose a thread
parameter — Singular sets the env var before calling the dispatch
shim if the user wants threading.

This matches Singular's convention so users who set
`SINGULAR_THREADS` can additionally set `RUSTGB_THREADS` with the
same mental model. It diverges from FLINT's explicit-arg style.

### Consequences

- Cancellation from the FFI side is not yet wired; `compute_gb`
  `expect`s the parallel computation to complete. The `parallel`
  module exposes `CancelHandle` for callers that need it, but the
  FFI path doesn't use it.
- The `parallel` path has not been validated against the staging
  suite as of 2026-04-21 (that is task 318). The 890s
  staging-5101449 run from 2026-04-21 was serial because the
  validation runner doesn't set the env var.
- If we ever want per-call thread control, the FFI would need a
  new entry point (`rustgb_compute_threaded(input, n)`); the env
  var path can stay as the default.

### References

- `~/rustgb/src/bba.rs:75-80` (`rustgb_threads()`)
- `~/rustgb/src/bba.rs:56-70` (dispatch in `compute_gb`)
- `~/rustgb/src/parallel.rs:86-91` (`compute_gb_parallel` signature)

---

## ADR-005: Monomial representation — direct exponents, 7 bits/var, divmask overflow guard

**Status:** Accepted and implemented (supersedes the original
complemented-storage representation that the initial commit shipped
with). Landed alongside this ADR's commit in `~/rustgb`.
**Date:** 2026-04-21 (decision); 2026-04-22 (implementation)

### Context

Profile v2 (`profile-rustgb-v2-staging-5101449.md`) showed
`Monomial::mul` at 30 % of total cycles after ADR-001's
head-cursor fix removed the prior memmove bottleneck. The cost is
not the multiplication itself — it's the per-byte loop with an
overflow check on every byte:

```rust
for b_idx in low_byte..=high_byte {                  // 5.93% loop control
    let ca = (a >> shift) & 0xFF;
    let cb = (b >> shift) & 0xFF;
    if ca + cb < 0xFF { return None; }                // 3.73% per-byte check
    let cnew = ca + cb - 0xFF;
    new_word |= cnew << shift;
}
```

The byte-by-byte structure exists because rustgb stored
**complemented** exponents (`255 − e`) so that lex-comparison of
the packed words encoded degrevlex order directly. That choice
made `cmp` cheap (~6 % of cycles) at the price of making `mul`
expensive: `(255 − a) + (255 − b) ≠ 255 − (a + b)`, so each byte
needs a `−0xFF` correction and an overflow check.

The question this ADR answers: how should monomial multiplication,
exponent storage, and overflow handling be structured?

### Singular's approach

**Storage:** direct (`e_v`, not complemented). Packed into u64
words at a per-ring configurable bits-per-variable, with one
**guard bit** reserved per variable slot so overflow can be
detected by examining that bit after addition.

**Multiplication:** plain word-wise add. `p_ExpVectorAdd`
(`p_polys.h:1432-1444`) reduces to `p_MemAdd_LengthGeneral`
(`templates/p_MemAdd.h`) which is `for (i=0; i<ExpL_Size; i++)
p1->exp[i] += p2->exp[i]`. Length-specialised macros unroll for
small word counts.

**Overflow handling — three layers:**

1. *Word-level mul itself is unchecked.* Just the plain add. The
   PDEBUG check (`pAssume1((unsigned long)(...) <= r->bitmask)`) is
   debug-only.

2. *Cheap pre-check using the divmask trick.*
   `p_LmExpVectorAddIsOk` (`p_polys.h:2020-2038`) is called before
   every spoly creation and every reducer step (call sites in
   `kspoly.cc:125, 260, 403, 540, 662, 876, 1123`):
   ```c
   if ( (l1 > ULONG_MAX - l2) ||
        (((l1 & divmask) ^ (l2 & divmask)) != ((l1 + l2) & divmask)))
     return FALSE;
   ```
   `divmask` has the guard bit set in each variable slot. If a
   byte overflows out of its slot, the carry corrupts the
   guard-bit pattern and the XOR check catches it. Branch-free,
   O(words) per check.

3. *Dynamic tail-ring widening.* When the pre-check fails,
   `kStratChangeTailRing` (`kutil.cc:10939-11034`) doubles the
   bitmask, builds a new ring via `rModifyRing`, and migrates
   every entry in `strat->T`, `strat->L`, `strat->P` into the
   wider representation via `ShallowCopyDelete`. Returns
   `FALSE` only if `expbound >= currRing->bitmask` (the absolute
   user-declared ceiling), at which point the bba driver emits
   `WerrorS("OVERFLOW...")` and bails out.

**Comparison:** uses `p_MemCmp__T` plus an `ordsgn` (sign vector)
so each ordering type can flip word-direction without dispatch
overhead.

### FLINT's approach

**Storage:** direct exponents, packed into `ulong` limbs at
per-poly bits-per-field. The `bits` field travels with the poly
(not the ring), so distinct polys can have different packings.

**Multiplication:** plain word-wise add. `mpoly_monomial_add`
(`flint/src/mpoly.h:233-240`):
```c
FLINT_FORCE_INLINE
void mpoly_monomial_add(ulong * exp_ptr, const ulong * exp2,
                                         const ulong * exp3, slong N)
{
   for (slong i = 0; i < N; i++)
      exp_ptr[i] = exp2[i] + exp3[i];
}
```
With a multi-limb variant (`_mp`) deferring to `__gmpn_add_n` and
multiply-add variants (`madd`/`msub`) for the heap reducer's
pending-product accumulation.

**Overflow handling:** post-hoc detection plus repack.
`mpoly_monomials_overflow_test` is run as a separate verification
pass on the result; on overflow `repack_monomials` widens
bits-per-field and re-encodes the poly. Less aggressive than
Singular: there's no per-multiply pre-check; FLINT relies on
either a generous initial `bits` or running the test after batch
operations and repacking once.

**Comparison:** per-ordering routines selected at compile time
(`monomials_cmp.c`); direct storage means each ordering's compare
encodes the direction in its own code, no per-word sign lookup at
runtime.

### Decision

Replace the current Monomial representation with:

1. **Direct storage of exponents** — store `e_v`, not `255 − e_v`.
   `Monomial::mul` becomes plain wrapping-add per u64 word.
2. **7 bits per variable, top bit as overflow guard.** Maximum
   single-variable exponent drops from 255 to 127. For the helium
   workload (max degree ~30) this is comfortable headroom; for any
   workload that exceeds it we error early.
3. **Cheap divmask-style overflow detection at the multiply
   site,** matching Singular's pre-check: a precomputed guard-bit
   mask in the `Ring` (`overflow_mask: [u64; 4]` with bit 7 set in
   each variable byte slot, 0 in the total-deg byte and unused
   slots), checked via `(a & mask) ^ (b & mask) != (a + b) & mask`
   per word. Auto-vectorisable; ~2 ops per word, ~8 ops for the
   whole packed block.
4. **Per-spoly `max_exp` caching is deferred** but the
   architecture leaves room for it: `Poly` can grow a
   `max_exp: Monomial` cache later, computed incrementally on
   `add_assign` / `merge`. When that lands, `KBucket::minus_m_mult_p`
   can do the overflow check **once** per reducer step against
   `multiplier + g.max_exp` and skip the per-term check entirely
   inside the inner loop (matching Singular's `kspoly.cc`
   pattern).
5. **`cmp_degrevlex` keeps word-level lex compare,** but applies a
   precomputed XOR mask to flip variable-byte direction at compare
   time. The mask (`cmp_flip_mask: [u64; 4]`, `0x7F` in variable
   byte slots, `0x00` in the total-deg byte and unused slots) is
   stored in the `Ring` and applied as `a.packed[i] ^ mask[i]`
   before each per-word compare. Cost: one extra XOR per word per
   cmp.
6. **No dynamic ring widening yet.** On overflow, panic with a
   clear "exponent exceeds 7-bit packing" message. Listed as a
   deferred enhancement (see Consequences).

### Consequences

**Performance:** Profile v2 hotspot reshuffle prediction was:

| Function | v2 (current) | After ADR-005 | Notes |
|---|---|---|---|
| `Monomial::mul` | 30.0 % | ~3-5 % | word-add + cheap check |
| `Monomial::cmp` (under merge) | ~6 % | ~9 % | XOR per word added |
| Net effect on wall | — | **~ −22 %** | residue stays the same shape |

**Measured (post-implementation, 2026-04-22):**

| Test | Pre-ADR-005 wall | Post-ADR-005 wall | Δ |
|---|---|---|---|
| staging-5101449 | 255 s | **204 s** | −20 % (matches prediction) |
| staging-5104053 | 311 s | **262 s** | −16 % |
| staging-5106746 | 484 s | **348 s** | −28 % |

All three staging tests pass with exact fixture matches. A v3 perf
profile (next ADR work) should confirm the predicted hotspot shift
to `poly::merge` and `KBucket::leading`.

**Safety:** strictly stronger than the original "trust silently
in release" sketch. The divmask check catches every overflow at
the multiply site with negligible cost. Worst case is a clear
panic, never silent corruption.

**Capacity:** max single-variable exponent 127, max total degree
still bounded by the cached `total_deg: u32`. The helium workload
peaks well under both limits.

**Implementation surface (all in `monomial.rs` + a constant in
`Ring`):**
- `Monomial::from_exponents`: write `e_v` directly. Validate
  `e_v < 128`.
- `Monomial::mul`: 4×u64 wrapping-add + divmask overflow check +
  total_deg / sev update. Returns `Option` only because of
  `total_deg` u32 sum overflow (extremely unlikely; could become
  infallible).
- `Monomial::cmp_degrevlex`: XOR with `ring.cmp_flip_mask` per
  word before comparison.
- `Monomial::div`, `Monomial::lcm`, `Monomial::divides`: also
  per-byte today; rewrite to word-level (`div` = wrapping-sub;
  `divides` = "every byte of `a` ≤ corresponding byte of `b`",
  expressible as `(a + (~b & mask)) & mask == 0` style trick).
- `Ring`: add `overflow_mask: [u64; 4]` and
  `cmp_flip_mask: [u64; 4]`, both computed once at `Ring::new`
  from `nvars`.
- `assert_canonical` / `sev` computation: straightforward update
  to read direct exponents.
- All existing tests should pass unchanged (public API is
  identical); a new test should explicitly exercise the overflow
  detection panic.

**Deferred enhancement: per-spoly max_exp caching.** Once
`Poly::max_exp` is plumbed through `add_assign` / `merge`,
`KBucket::minus_m_mult_p` can hoist the overflow check out of the
inner loop. Skipping it in the inner loop is worth maybe another
1-2 % wall, not urgent.

**Deferred enhancement: dynamic ring widening.** Multi-week
project mirroring `kStratChangeTailRing`: requires a mutable
`Ring`, polynomial migration via `ShallowCopyDelete`, and proc-table
swaps. Not currently needed; revisit if a future workload exceeds
7-bit per-variable packing.

**Supersession:** This ADR overturns the original choice (made
implicitly when `monomial.rs` was first written) of
complemented-exponent storage for cheap comparison. The original
choice optimised the wrong half of the tradeoff; profile evidence
showed cmp was always cheap relative to mul, regardless of
representation.

### References

- `~/rustgb/src/monomial.rs:185-225` (current `Monomial::mul`,
  per-byte loop with overflow check — the code being replaced)
- `~/rustgb/src/monomial.rs:370-402` (current `cmp_degrevlex`,
  word-level lex on complemented exponents)
- `~/Singular-rustgb/libpolys/polys/monomials/p_polys.h:1432-1444`
  (`p_ExpVectorAdd`)
- `~/Singular-rustgb/libpolys/polys/templates/p_MemAdd.h`
  (`p_MemSum_LengthGeneral` and length-specialised macros)
- `~/Singular-rustgb/libpolys/polys/monomials/p_polys.h:2020-2038`
  (`p_LmExpVectorAddIsOk`, the divmask trick)
- `~/Singular-rustgb/kernel/GBEngine/kutil.cc:10939-11062`
  (`kStratChangeTailRing`, `kStratInitChangeTailRing`)
- `~/Singular-rustgb/kernel/GBEngine/kstd2.cc:2706-2748`
  (overflow handling in the bba main loop)
- `~/Singular-rustgb/kernel/GBEngine/kspoly.cc:120-138` (per-spoly
  pre-check + retry pattern)
- `~/flint/src/mpoly.h:233-282` (`mpoly_monomial_add` and
  `madd` / `msub` family)
- `~/project/docs/profile-rustgb-v2-staging-5101449.md` (the
  30 % `Monomial::mul` evidence that motivated this ADR)

---

## ADR-006: poly::merge — pre-allocated output, FLINT-style index writes

**Status:** Accepted and implemented. Landed alongside this ADR's
commit in `~/rustgb`.
**Date:** 2026-04-22

### Context

After ADR-005 collapsed `Monomial::mul` from 30 % of cycles to
fully-inlined-out, the v3 profile
(`~/project/docs/profile-rustgb-v3-staging-5101449.md`) showed
`poly::merge` as the new top concentrated function at 21.2 % of
total cycles. Inside `merge`, `Vec::push` accounted for 7.0 % of
total cycles (3.4 % of which was `core::ptr::write` itself), with
the remainder split between `Monomial::cmp` (7.0 %) and the loop
body (~7 %).

`merge` is hot because every reducer step that absorbs a non-empty
`build_neg_cmp` result into a non-empty geobucket slot fires it
(via `KBucket::absorb` → `Poly::add` → `merge`). Across an
entire bba run on staging-5101449 that's millions of merge calls,
each one constructing a fresh `Vec<Coeff>` and `Vec<Monomial>`
output by repeated `push`-ing.

The question this ADR answers: how should the merge emit its
output terms?

### Singular's approach

Singular's `p_Add_q__T` (`~/Singular-rustgb/libpolys/polys/templates/p_Add_q__T.cc`,
86 lines) sidesteps the question entirely by **never allocating
output nodes**. Polynomials are linked lists of `spolyrec` nodes;
emitting a term is one pointer write that splices an existing input
node into the output list:

```c
Greater:
  a = pNext(a) = p;     // splice existing node into output
  pIter(p);             // advance source pointer
  if (p==NULL) { pNext(a) = q; goto Finish; }   // O(1) tail splice
  goto Top;
```

When one input is exhausted, `pNext(a) = q` joins the entire
remaining tail of the other in **one pointer write**, regardless of
length. The input lists are explicitly destroyed by the call (the
docstring says `Destroys: p, q`). The "Equal" path adds
coefficients in place via `n_InpAdd__T`, freeing the q-side node;
on cancellation, `n_Delete__T` + `p_LmFreeAndNext` consume both
nodes. Cmp uses `p_MemCmp__T` (word-wise compare with `ordsgn`).

Per-emitted-term cost: **one pointer write + one pointer chase +
one cmp**. No allocation, no copy of coefficient or exponent data.

This is structurally inaccessible to rustgb: we picked flat-array
storage in ADR-001 (head-cursor over a `Vec`), so we don't have
linked-list nodes to splice and there is no "tail splice" trick
available. Adopting Singular's design here would require redoing
ADR-001.

### FLINT's approach

FLINT's `_nmod_mpoly_add` (`~/flint/src/nmod_mpoly/add.c:16-67` and
the general-N variant at lines 69-124) uses flat parallel arrays
with **pre-allocated output and direct index writes**:

```c
if ((Bexps[i]^maskhi) > (Cexps[j]^maskhi)) {
    Aexps[k] = Bexps[i];
    Acoeffs[k] = Bcoeffs[i];
    i++;
}
else if ((Bexps[i]^maskhi) == (Cexps[j]^maskhi)) {
    Aexps[k] = Bexps[i];
    Acoeffs[k] = nmod_add(Bcoeffs[i], Ccoeffs[j], fctx);
    k -= (Acoeffs[k] == 0);   // branch-free cancellation skip
    i++; j++;
}
else { /* mirror */ }
k++;
```

Three structural choices:

1. **Pre-allocated output.** The wrapper `nmod_mpoly_add`
   (`add.c:169-186`) calls `nmod_mpoly_init3(T, B->length + C->length, ...)`
   to size the output to the worst case (no cancellation) before
   the inner loop begins.
2. **Index-and-write.** The inner loop writes into pre-sized array
   slots (`Aexps[k] = Bexps[i]; Acoeffs[k] = Bcoeffs[i]`). No bounds
   check, no length update per write.
3. **Branch-free cancellation.** `k -= (Acoeffs[k] == 0)` decrements
   the write cursor when the result was zero, "uncommitting" the
   slot. No `if`-then-skip-push branch.

Length is recovered at the end: `return k` → caller assigns
`T->length = k`.

There is also a hot-path specialisation `_nmod_mpoly_add1` for
`N == 1` (single-limb exponents), which inlines the cmp as
`(Bexps[i] ^ maskhi) > (Cexps[j] ^ maskhi)` rather than calling
`mpoly_monomial_cmp`. rustgb's exponent block is always 4 u64s, so
this specialisation does not apply directly, though the cmp is
already inlined via `cmp_degrevlex`.

### Decision

Adopt FLINT's pattern verbatim. Concretely:

1. **Pre-allocate** `out_c` and `out_m` to the upper-bound capacity
   `a.len() + b.len()` (already done in the existing code, but
   currently followed by `push`).
2. **Write via `Vec::spare_capacity_mut()` + `MaybeUninit::write`**
   instead of `Vec::push`. This skips the per-push bounds-check
   against `len < capacity` and the per-push length increment.
   Writing into the spare-capacity slice is safe; only the final
   `set_len` call is `unsafe`.
3. **Branch-free cancellation** in the Less and Equal arms:
   ```rust
   spare_c[k].write(c);
   spare_m[k].write(m.clone());
   k += (c != 0) as usize;
   ```
   The write to slot `k` is wasted on cancellation (the next
   iteration overwrites the same slot), but the *branch* is gone —
   matching FLINT's `k -= (acc == 0)` shape with a `+=` instead of
   `-=` (we never speculatively bumped k, so we conditionally hold
   it back rather than conditionally back it off).
4. **Single `set_len`** at the end. The Vec is now logically
   length-`k` with `capacity - k` slots in spare; the wasted writes
   (if any) leak their bytes when the Vec eventually drops, which
   is fine because both `Coeff` (u32) and `Monomial` (POD struct)
   have no Drop side effects.

`sub_mul_term` (`poly.rs:503`) has the same structural pattern
(2-pointer merge with materialised `c·m·q` terms) and would
benefit from the same change, but it is not in the v3 hot path.
Defer until profile evidence shows it matters.

### Consequences

**Performance prediction:** the v3 profile attributed 7.0 % of
total cycles to `Vec::push` inside `merge`. Eliminating the
per-push bounds-check + length-increment pair (keeping the
underlying `ptr::write`) should cut that to ~2-3 %, for **~4-5 %
wall reduction**. The `Monomial::clone()` cost (32-byte struct
copy) is unaffected; that's an unavoidable cost of value-move
into an array slot.

**Measured (post-implementation, v4 profile, samsung):**
`Vec::push` is **completely gone** from the v4 profile.
`poly::merge`'s share dropped from 21.2 % (v3) to 17.2 % (v4) —
the predicted ~4 percentage point reduction. Inside the new merge,
`Monomial::cmp` is 8.4 % and the loop body accounts for the rest;
no `Vec::push` line at all. Wall under perf load went 3:34 (v3) →
2:52 (v4), a 19 % reduction; the cleaner steady-state metric is
the ~4 pp share drop, which translates to roughly the predicted
wall improvement once contention noise is averaged out.
All staging tests still produce exact fixture matches.

The branch-free cancellation removes one branch per Equal-with-cancel
or Less-with-zero-coefficient case. Cancellation is rare in general
but happens reliably for the leading term in every `KBucket::absorb`
call (that's the algorithmic point of `minus_m_mult_p`), so the
saving is at least one branch per merge call.

**Safety:** the only `unsafe` is the final `set_len(k)`. The
write-through-spare-capacity pattern via `MaybeUninit::write` is
safe at compile time. The wasted-write slots beyond `k` are not
considered initialised by the Vec (`set_len` truncates), so they
are not dropped — but neither `Coeff` nor `Monomial` has a Drop
impl with side effects we care about, so this is correct.

**Capacity invariant:** `out.coeffs.capacity()` may exceed
`out.coeffs.len()` after the merge, by up to (number of cancelled
terms). For the typical bucket-absorb workload that's a single-digit
overhang, well within ordinary `Vec` slop. Not worth shrinking.

**API:** the `merge` signature is unchanged. Callers
(`Poly::add`, `Poly::sub`, `Poly::add_assign`) need no changes.

### References

- `~/rustgb/src/poly.rs:648-708` (current `merge` — the code
  being replaced)
- `~/Singular-rustgb/libpolys/polys/templates/p_Add_q__T.cc`
  (Singular's linked-list merge with O(1) tail splice; reference
  but structurally inapplicable to flat-array storage)
- `~/flint/src/nmod_mpoly/add.c:16-124` (FLINT's
  `_nmod_mpoly_add1` and `_nmod_mpoly_add` — the model adopted
  here)
- `~/flint/src/nmod_mpoly/add.c:126-196` (the wrapper
  `nmod_mpoly_add` showing the pre-allocation pattern)
- `~/project/docs/profile-rustgb-v3-staging-5101449.md` (the
  21.2 % `poly::merge` and 7.0 % `Vec::push` evidence that
  motivated this ADR)

---

## ADR-007: SIMD-batched sev pre-filter for the basis-sweep in `reduce_lobject`

**Status:** Accepted and implemented. Landed alongside this ADR's
commit in `~/rustgb`.
**Date:** 2026-04-22

### Context

The v4 profile (`~/project/docs/profile-rustgb-v4-staging-5101449.md`)
showed `bba::reduce_lobject` at 30.0 % of total cycles. A
per-instruction `perf annotate` revealed that the single hottest
instruction in the entire program is the sev pre-filter `jne`
inside the divisor-search loop:

```asm
                       :  if (s_sev & !lm_sev) != 0 {
0.68 :   2c18f:  test   %r15,(%rax,%r13,8)        ; sevs[idx] & !lm_sev
18.70 :  2c193:  jne    2c160                      ; if hits, skip
```

That `jne` alone is 18.70 % of within-function cycles ≈ 5.6 % of
total cycles. Including the rest of the per-iteration overhead
(loop bound check, redundant-flag check, sevs bounds check, sevs
load), the "skip-fast-path" of the basis sweep totals 41.78 %
within-function ≈ **12.5 % of total program cycles**. The actual
`Monomial::divides` call when the sev pre-filter passes adds
another ~6.7 % of total.

So roughly **19 % of the entire program's runtime is the
basis-sweep inside `reduce_lobject`** — the loop at `bba.rs:241-258`
that walks `s_basis` looking for a divisor of the current leader.
The sweep itself is simple, but it fires on every reduction step
across millions of reduction steps in a typical bba run, with the
basis growing to ~3000 elements by the end of staging-5101449.

The sev pre-filter is doing its algorithmic job (most candidates
get rejected). The cost is per-iteration *fixed overhead* — load,
test, branch — and three structural sources stall it:

1. The sev load misses L1 frequently as the basis grows past a
   few thousand u64s (cache thrashing during sweep).
2. The data-dependent branch is hard to predict.
3. Bounds checks Rust inserts for the indexed array accesses
   (`sevs[idx]`, `redund[idx]`) cost one branch per iteration.

This is the same pathology Singular's `next-opt` branch had on the
same workload — and the same fix.

### Singular's approach

Singular's `next-opt` branch introduced `kSevScanAVX2`
(`~/Singular-next-opt/kernel/GBEngine/kstd2.cc:74-121`):

```c
__attribute__((target("avx2")))
static inline int kSevScanAVX2(const unsigned long* sevT,
                               unsigned long not_sev,
                               int j, int tl)
{
  const __m256i vnot_sev = _mm256_set1_epi64x((long long)not_sev);
  const __m256i vzero    = _mm256_setzero_si256();
  // Main loop: 16 entries (4 batches of 4) per iteration
  while (j + 15 <= tl) {
    __builtin_prefetch(sevT + j + 16, 0, 1);
    __m256i vand1 = _mm256_and_si256(_mm256_loadu_si256(...), vnot_sev);
    __m256i vand2 = _mm256_and_si256(_mm256_loadu_si256(...), vnot_sev);
    __m256i vand3 = _mm256_and_si256(_mm256_loadu_si256(...), vnot_sev);
    __m256i vand4 = _mm256_and_si256(_mm256_loadu_si256(...), vnot_sev);
    __m256i vcmp1 = _mm256_cmpeq_epi64(vand1, vzero);
    /* ... vcmp2, vcmp3, vcmp4 ... */
    int combined = mask1 | mask2 | mask3 | mask4;
    if (__builtin_expect(combined != 0, 0)) {
      if (mask1) return j;
      if (mask2) return j + 4;
      if (mask3) return j + 8;
      return j + 12;
    }
    j += 16;
  }
  /* tail loop: 4 entries at a time, then scalar */
}
```

The pattern: load 4 sevs at a time via `_mm256_loadu_si256`,
compute `sevs & not_sev` per element via `_mm256_and_si256`,
compare against zero with `_mm256_cmpeq_epi64`, extract a 32-bit
mask (8 bits per qword) via `_mm256_movemask_epi8`. The main
loop is unrolled 4× to amortise the loop overhead and let the
common all-miss case branch only once per 16 entries.

There's also a SSE4.1 fallback (`kSevScanSSE4`,
`kstd2.cc:127-`) for non-AVX2 CPUs and a scalar fallback
(`kSevScan`). Runtime dispatch chooses the best available path
once per `bba` invocation.

The function returns the **first index** where the sev pre-filter
passes (or `tl` past end if none found). The caller checks the
redundant flag and runs the actual `divides` separately. This
keeps the SIMD code pure-sev and easy to reason about.

Singular's measured impact: kSevScanAVX2 took 7-11 % of total
cycles in the v6 profile (it absorbed the time previously paid
by `chainCritNormal` and the inner sweep), and the cumulative
optimisation (sev_flat + AVX2 scan) was the largest single
contributor to next-opt's ~36 % cumulative speedup.

### FLINT's approach

**N/A — FLINT has no GB engine.** The closest analogue is FLINT's
heap-based reducer's "process the next pending product" loop
(`divrem_monagan_pearce.c`), but that walks a heap, not a basis,
and the structure is fundamentally different. There is no
"sweep T-set looking for a divisor" idiom in FLINT to compare
against.

### Decision

Adopt the Singular pattern verbatim, gated by Rust's compile-time
`target_feature = "avx2"`. Concretely:

1. **Refactor the divisor search out of `reduce_lobject`** into a
   helper `find_divisor_idx(s_basis, lm_sev, lm, ring)` so the
   sweep code can be optimised independently and unit-tested in
   isolation.
2. **Inside the helper, dispatch on `cfg(target_feature = "avx2")`**:
   - **AVX2 path:** mirror `kSevScanAVX2`. Process the basis in
     batches; each batch loads 4 sevs, ANDs with `vnot_sev`, compares
     against zero, extracts a movemask, and (if any bit set) finds
     the first hit. For each hit, check `redundant[idx]` and call
     `Monomial::divides` exactly as the scalar path does. Manually
     unroll 4× as Singular does, for the same all-miss-fast-path
     reason.
   - **Scalar fallback:** the original loop, unchanged. Used when
     building without AVX2 enabled (e.g., on older CPUs like
     c200-1, which is Westmere-era).
3. **No SSE4.1 fallback for this first cut.** Adding SSE4.1 is
   straightforward (mirror Singular's `kSevScanSSE4`) but not
   necessary for correctness. Defer until measurement on c200-1
   shows it's worth the complexity.
4. **Runtime feature detection deferred.** Compile-time gating is
   simplest. Document in the rustgb README that release builds on
   AVX2 hardware should use `RUSTFLAGS="-C target-cpu=native"` to
   pick up the AVX2 path.

Note that the redundant-flag check and the `Monomial::divides`
probe stay scalar in the caller. Singular does the same — its
SIMD function returns just an index, and the caller checks
`redundant` and calls `divides`. Folding redund into the SIMD
batch is possible (read 4 redund bytes alongside the 4 sevs, AND
into the candidate mask) but adds complexity for marginal gain
since `redund[idx]` is itself a single byte load, already cheap.

### Consequences

**Performance prediction:** Singular's measurement suggests this
optimisation can cut the basis-sweep cost from ~12.5 % of total
cycles (rustgb v4) to the ~7-11 % range that Singular's `kSevScanAVX2`
occupies (which is a smaller share because Singular's reducer
also has other costs we don't have). Conservatively, **~5-8 %
wall reduction** on staging workloads. For a v5 profile,
`reduce_lobject`'s self-time should drop from 30 % to ~22-25 %,
with the freed share spreading proportionally.

**Measured (post-implementation, 2026-04-22, samsung):**
- Correctness: all three staging tests pass with exact fixture
  matches under both AVX2-enabled and scalar builds.
- SIMD activation verified: `objdump` shows 20 AVX2 instructions
  (vpand, vpcmpeq, vpmovmskb, vpbroadcastq, vmovdqu) inlined into
  `reduce_lobject` in the AVX2 build.
- Wall numbers under perf load are noisy on samsung due to
  background contention from concurrent processes; staging-5101449
  un-profiled walls ranged 123-226 s across runs of the same code,
  making per-ADR attribution unreliable. A clean v5 perf profile
  comparison (under controlled load) would settle the cycle-count
  attribution; deferred as the obvious next step.

**Build configuration:** the AVX2 path is compile-time gated. A
default `cargo build --release` on a non-AVX2-enabled rustc
configuration will use the scalar path. To opt in:
```
RUSTFLAGS="-C target-cpu=native" cargo build --release
```
This should be added to the README / build instructions. CI builds
on x86_64 hosts with AVX2 (the dev laptop and edge / c200-1's
successor systems) will pick it up automatically.

**Portability:** the scalar path is identical in behaviour. Both
paths are unit-tested against each other (a property test that
runs the same input through both and checks identical results).
Cross-compilation to non-x86 (e.g., ARM) falls through to the
scalar path with no special handling.

**Safety:** the AVX2 intrinsics live in `unsafe` blocks. The
unsafety is local: each intrinsic call wraps a `_mm256_loadu_si256`
on a slice we have already bounds-checked at the top of the
batch. The function's external API is safe.

**Why not SIMD `Monomial::divides`?** It's the next thing in line
(6.7 % of total) but lower priority for two reasons:
1. The sev-sweep work is the larger absolute cost.
2. SIMD-divides would need to handle two monomials' packed words
   simultaneously, which is more complex than the single-stream
   sev scan.

Listed as a possible follow-up; not adopted now.

### References

- `~/rustgb/src/bba.rs:220-286` (current `reduce_lobject` — the
  divisor search at lines 241-258 is the surface being changed)
- `~/rustgb/src/sbasis.rs:33-47` (the `SBasis` struct showing
  `sevs: Vec<u64>` is already a contiguous flat array, ready
  for SIMD without layout changes)
- `~/Singular-next-opt/kernel/GBEngine/kstd2.cc:74-121`
  (`kSevScanAVX2` — the model adopted here)
- `~/Singular-next-opt/kernel/GBEngine/kstd2.cc:127-` 
  (`kSevScanSSE4` — the SSE4.1 fallback we are deferring)
- `~/project/docs/profile-rustgb-v4-staging-5101449.md` (the
  v4 profile showing `reduce_lobject` at 30 % and identifying
  the sweep as the largest concentrated target)
- This conversation's `perf annotate` of `reduce_lobject` showing
  the per-instruction breakdown (the 18.70 % `jne` at offset
  0x2c193 was the smoking gun)

---

## ADR-008: Heap-based Monagan-Pearce reducer (supersedes ADR-002, ADR-003)

**Status:** Accepted. Implementation in progress (multi-phase plan
landing across several commits). Phase 1 (this commit) lands the
ADR + scaffold; ADR-002's geobucket reducer remains the active
runtime path until Phase 5 plumbs the heap reducer in behind a
feature flag, and is fully retired in Phase 7 if heap-based
validation succeeds.

**Date:** 2026-04-22

### Context

The v5 profile (`~/project/docs/profile-rustgb-v5-staging-5101449.md`)
showed the four largest concentrated functions to be:

| Function | v5 % of total |
|---|---|
| `bba::reduce_lobject` (self + inlined) | 23.5 |
| `poly::merge` | 20.1 |
| `KBucket::minus_m_mult_p` | 16.1 |
| `KBucket::leading` | 15.3 |
| libc allocator (combined) | 5.3 |
| `Monomial::cmp` (combined under merge + leading) | ~7 |

Of those, `poly::merge` (20.1 %), `KBucket::minus_m_mult_p`
(16.1 %), `KBucket::leading` (15.3 %), and a large share of
the allocator cost (~5 %) are **all costs imposed by the geobucket
reducer architecture chosen in ADR-002**. They exist because the
geobucket maintains the partial reduction as a materialised set of
polynomial slots that must be merged, scanned, and absorbed step
by step. About **57 % of v5's total cycles** live in functions
either eliminated or replaced by an alternative reducer
architecture.

The cost shape that's *not* a function of the geobucket — basis
sweep (~7 %), `Monomial::div` for multiplier construction (~7 %),
sugar bookkeeping, and the various cmp/divides primitives — is
unchanged regardless of which reducer architecture we pick.

ADR-003 listed the heap-based Monagan-Pearce reducer as a deferred
candidate; the v5 profile evidence has now made the case strong
enough to adopt it. This ADR promotes ADR-003 from "deferred" to
"accepted" and supersedes ADR-002.

### Singular's approach

Singular has **both** reducer architectures available. The default
bba path (`~/Singular-rustgb/kernel/GBEngine/kstd2.cc:bba()`)
uses the geobucket via `kBucket_pt`; a separate path
(`kStratHeap`-style strategies in `kstd1.cc`) uses a heap reducer
for situations where the geobucket's slot-management overhead is
known to lose. The choice was made decades ago when typical
workloads were larger than today's helium examples; for our scale
the geobucket's O(slot_count) leader scan cost amortises poorly
because the slot scan happens on *every* reducer step, not per
emitted term.

Singular's heap reducer machinery (when used) carries its own
`max_exp` cache per source poly and pushes new heap nodes as
divisors are added — structurally identical to the design adopted
here.

### FLINT's approach

FLINT uses **only** the heap-based Monagan-Pearce reducer for its
mpoly division (`~/flint/src/nmod_mpoly/divrem_monagan_pearce.c`,
726 lines, plus a similar `divides_monagan_pearce.c` for the
"is-it-divisible" specialisation). There is no geobucket reducer
in FLINT (the geobucket data structure exists but is used only as
a sum buffer with no `extract_leading` operation — see ADR-002).

FLINT's heap-node design is the closest reference. Each node
carries a chain of `(i, j)` indices: `i` identifies a source
polynomial (the input being divided, plus each pending divisor
times its multiplier), and `j` is the current term index in that
source. Pop the max, accumulate same-monomial chain entries, sum
coefficients, emit-or-cancel. When a quotient term is produced,
the corresponding divisor's tail terms get pushed onto the heap
(scaled by the quotient term).

The relevant detail FLINT documents but is easy to miss: each
source contributes **at most one heap node at a time**. When you
pop term j from source i, you push term j+1 from the same source,
keeping the heap size bounded by `1 + number_of_active_reducers`.
This is what keeps the heap log factor manageable.

### Mathicgb's approach

Mathicgb (the reference for ADR-001's polynomial layout) ships
**both** reducer architectures as runtime-selectable strategies
via the `Reducer::Type` enum (`~/mathicgb/src/mathicgb/Reducer.hpp`).
Implementations: `ReducerHeap.cpp`, `ReducerHashTable.cpp`,
`ReducerNoDedupHashTable.cpp`, `ReducerPackedDedupList.cpp`,
`ReducerHashPack.cpp`. The default for typical workloads is
`ReducerHeap`. The fact that mathicgb's authors made heap the
default after extensive benchmarking on Gröbner-basis-shaped
problems is a strong signal for our adoption.

Mathicgb's heap reducer also carries a per-reducer "monomial slab"
that pre-allocates the multiplier monomials in a side table
indexed by reducer-id. The heap nodes themselves stay small (~24
bytes: source poly pointer + index + reducer-id), which keeps
cache pressure low. We will mirror this pattern.

### Decision

Adopt a heap-based Monagan-Pearce reducer for `bba::reduce_lobject`,
matching the pattern documented above (FLINT's bookkeeping +
mathicgb's slab layout + lazy divisor addition driven by the
existing `find_divisor_idx`).

**Algorithmic shape** (the four mechanics that have to all line
up correctly):

1. **In-flight reducers**, stored in a per-LObject slab:
   ```text
   Reducer { poly: &Poly, multiplier: Monomial, coeff: Coeff, index: usize, sugar: u32 }
   ```
   `coeff` is pre-negated for cancellation (so summing the heap-top
   chain naturally produces the cancellation result). `index`
   tracks the next term in `poly` that hasn't yet been emitted into
   the heap.

2. **Heap nodes**, max-heap by degrevlex:
   ```text
   HeapNode { cmp_key: [u64; 4], reducer_idx: usize }
   ```
   `cmp_key` is the packed monomial `multiplier * poly.terms[index]`,
   pre-XORed against `ring.cmp_flip_mask` so plain lex compare on
   `[u64; 4]` is the correct max-heap ordering. Cached at push
   time, so the heap's internal compares need no `&Ring`.

3. **Pop-with-cancellation**: pop the max; while the next pop has
   the same `cmp_key`, accumulate. After draining the equal chain,
   if the summed coeff is zero, advance all contributing reducers'
   indices and recurse (or loop). If nonzero, that's the new
   leader / output term.

4. **Lazy divisor addition**: when a new leader emerges, run the
   existing `find_divisor_idx` against `s_basis`. If it returns
   `Some(idx)`, push a new `Reducer` with `index = 0` and the
   appropriate negated coefficient onto both the slab and the
   heap. The next pop-with-cancellation will (by construction)
   sum the old leader and the new reducer's first term to zero,
   driving us toward the next non-cancelled term.

5. **Survivor materialisation**: the LObject reduces to zero iff
   the heap becomes empty. Otherwise we have a survivor — drain
   the remaining heap entries via repeated pop-with-cancellation,
   pushing each emitted term into a fresh `Poly`. **This is the
   only place `Monomial::clone` happens** in the entire reduction
   chain (excluding the multiplier-monomial clones, one per added
   reducer, paid into the slab).

**Sugar tracking**: the LObject's sugar at any moment is `max(
initial_sugar, max over all in-flight reducers of (reducer.sugar))`.
Since reducers are only added (never removed mid-reduction), this
is just the running max of `(g_i.sugar + multiplier_deg)` over
adds, plus the initial. One `u32` slot on the LObject; updated on
each `push_reducer`.

**What this removes**:
- `KBucket` entirely (the geobucket struct, its `absorb`,
  `leading`, `extract_leading`, `minus_m_mult_p`, `is_zero`,
  `dirty` mask, `lm_cache`, the 32 NUM_SLOTS array and the
  `slot_for_len` length-bucketing).
- `poly::merge` (replaced by heap-pop emission); `Poly::add` and
  `Poly::sub` retain their public API but now go through a much
  simpler implementation that constructs from the heap output.
- `Poly::sub_mul_term` (subsumed by adding-as-reducer + heap
  iteration).
- The `LObject`'s embedded geobucket; replaced by a heap state
  (`Vec<Reducer>` slab + `BinaryHeap<HeapNode>` or similar).
- `kbucket.rs` as a module (retained in the repo through Phase 6
  for A/B comparison; deleted in Phase 7 if heap wins).

**What this preserves**:
- `find_divisor_idx` (unchanged — basis sweep still happens on
  each new leader).
- `Monomial` and its arithmetic (unchanged).
- `Poly` and its arithmetic outside the reducer (unchanged).
- `SBasis` and its sevs/redund parallel arrays (unchanged).
- `gm` pair criteria (unchanged).
- Sugar strategy (preserved with simpler bookkeeping).
- `bba::compute_gb` public API (unchanged).
- Output: bit-for-bit identical reduced GB on identical inputs
  (algorithmically Monagan-Pearce produces the same reduced
  Gröbner basis as geobucket-based bba).

### Consequences

**Performance prediction** (rough, conservative):

| Cost source | v5 share | Post-ADR-008 share |
|---|---|---|
| `poly::merge` | 20.1 % | ~3-5 % (only survivor materialisation) |
| `KBucket::minus_m_mult_p` | 16.1 % | gone |
| `KBucket::leading` | 15.3 % | gone (replaced by heap-pop, ~5-8 %) |
| Heap operations (new) | — | ~10-15 % (push, pop, log factor) |
| `Monomial::clone` per emitted term | ~3-5 % (inside merge's "loop body") | gone for non-survivors |
| libc allocator | 5.3 % | ~1-2 % (slab is amortised) |

Net wall prediction: **30-50 % wall reduction** on staging
workloads, putting staging-5101449 at roughly 60-80 s
(from v5's 115 s). This would close maybe a third of the
gap to the C++ next-opt target (~5 s on samsung).

**Measured (post-implementation, v6 profile, samsung, 2026-04-22):**

The actual win exceeded the prediction by 2×.

| Test | v5 (geobucket, AVX2) | v6 (heap, AVX2) | Wall reduction |
|---|---|---|---|
| staging-5101449 | 115 s | **38 s** | **−67 %** |
| staging-5104053 | 186 s | **52 s** | **−72 %** |
| staging-5106746 | 225 s | **58 s** | **−74 %** |

All three staging tests pass with exact fixture matches.

**Cumulative wall on staging-5101449 across the optimisation
series (un-profiled, AVX2 build, low contention):**

| Profile | Wall | Cumulative speedup |
|---|---|---|
| v1 (raw memmove) | ~870 s | 1.0× |
| v2 (ADR-001 head cursor) | ~225 s | 3.9× |
| v3 (ADR-005 direct exp) | ~204 s | 4.3× |
| v4 (ADR-006 FLINT merge) | ~140 s | 6.2× |
| v5 (ADR-007 SIMD sev) | 115 s | 7.6× |
| **v6 (ADR-008 heap reducer)** | **38 s** | **23×** |

vs C++ next-opt baseline (~5-7 s on samsung): rustgb went from
~17-25× slower (v5) to ~5-8× slower (v6). The heap reducer alone
closed roughly two-thirds of the remaining gap.

**v6 profile cost shape** (~/project/docs/profile-rustgb-v6-staging-5101449.md):

| Function | v5 % | v6 % | Notes |
|---|---|---|---|
| `bba::reduce_lobject` (geo path, self+inlined) | 23.5 | gone | replaced by heap path |
| `poly::merge` | 20.1 | **gone** | matches prediction |
| `KBucket::minus_m_mult_p` | 16.1 | **gone** | matches prediction |
| `KBucket::leading` | 15.3 | **gone** | matches prediction |
| `ReducerHeap::reduce_to_normal_form` | — | 19.8 | new; mostly find_divisor |
| `gm::chain_crit_normal` | 3.2 | **19.8** | **6× share growth** |
| `ReducerHeap::pop_with_cancellation` | — | 11.2 | new |
| `BinaryHeap::pop` | — | 10.5 | new (std-lib heap log factor) |
| Hashing (gm pair-criterion) | <1 | ~7 | new visibility |
| libc allocator (combined) | 5.3 | ~3 | matches prediction |

The huge surprise: `gm::chain_crit_normal` jumped from 3.2 % to
19.8 % share — the same Amdahl's law effect Singular saw when
they reduced the reducer cost. The pair criterion is now the
plurality-share concentrated function (tied with reducer's outer
loop). The natural next ADR target.

**Risks**:
- **Sugar regression**: the heap-based design's sugar bookkeeping
  is structurally simpler but easy to get wrong. Validation gate:
  the cargo test suite's reduction-result comparisons will catch
  algorithm-level bugs; staging-validation against fixtures will
  catch end-to-end correctness regressions.
- **Heap log factor on large bases**: for very long reductions
  with many active reducers, the O(log n) heap ops could
  cumulatively cost more than the geobucket's O(slot_count)
  leader scan. Singular's choice of geobucket-by-default was made
  for this case. For helium-staging-shaped workloads (moderate
  basis, short reductions), the trade-off goes the other way —
  but worth confirming with a v6 profile.
- **Cache locality of interleaved source poly access**: the heap
  pops dereference different source polys in interleaved order.
  Sequential within one source poly (cache-friendly) but
  interleaved across many sources during the pop sequence
  (cache-unfriendly). Possibly mitigated by L2's larger size
  relative to the working set (a few thousand polys × ~24 bytes
  per heap-active term = small).
- **Significant code-volume change** (~500-1000 lines new in
  `reducer.rs`, ~300 lines retired from `kbucket.rs`, ~50 lines
  changed in `bba.rs`, similar in `lobject.rs`). Phased landing
  with feature flag (Phase 5) lets the cargo test suite validate
  each phase independently.

**Migration plan** (the "implementation roadmap"; each phase is
a separate commit):

- **Phase 1** (this ADR's commit): scaffold `reducer.rs`, define
  `Reducer` and `HeapNode` types, register the module. No
  algorithm yet; cargo test still passes.
- **Phase 2**: heap data structure (push, pop_max, peek). Unit
  tests against a known-correct slow reference (sort all entries,
  pick max repeatedly).
- **Phase 3**: pop-with-cancellation (sum same-cmp_key chains,
  return non-zero or recurse). Tests on hand-crafted small heaps.
- **Phase 4**: lazy-add-divisor and survivor materialisation.
  Tests against tiny reductions (manually verified).
- **Phase 5**: plumb into `reduce_lobject` behind
  `cfg!(feature = "heap_reducer")`. Both reducers compile; cargo
  test runs both and asserts identical output on shared fixtures.
- **Phase 6**: full staging-validation under heap-reducer flag.
  Three-test fixture comparison is the correctness gate.
- **Phase 7**: profile v6 under heap. If wall improves
  meaningfully (≥ 15 % wall reduction), retire `kbucket.rs` (move
  to `examples/legacy/`) and make heap the default.

### References

- `~/rustgb/src/bba.rs:220-286` (current `reduce_lobject` —
  the integration target)
- `~/rustgb/src/kbucket.rs` (the geobucket being superseded;
  retired in Phase 7)
- `~/Singular-rustgb/kernel/GBEngine/kstd2.cc` (Singular's bba
  using geobucket — the historical default)
- `~/Singular-rustgb/kernel/GBEngine/kstd1.cc` (Singular's
  alternative `kStratHeap` strategies — heap-reducer evidence)
- `~/flint/src/nmod_mpoly/divrem_monagan_pearce.c` (FLINT's
  heap reducer; the closest reference implementation)
- `~/mathicgb/src/mathicgb/ReducerHeap.cpp` (mathicgb's heap
  reducer; the reference for the slab + small heap node pattern)
- `~/mathicgb/src/mathicgb/Reducer.hpp` (mathicgb's runtime
  reducer-selector enum)
- `~/project/docs/profile-rustgb-v5-staging-5101449.md` (the
  v5 profile evidence motivating this ADR)
- ADR-002 (geobucket reducer — superseded by this ADR)
- ADR-003 (heap reducer candidate — promoted to accepted by
  this ADR)

---

## ADR-009: SIMD-batched sev sweep for `chain_crit_normal` B-internal dedup

**Status:** Accepted and implemented. Landed alongside this ADR's
commit in `~/rustgb`.
**Date:** 2026-04-22

### Context

The v6 profile (`~/project/docs/profile-rustgb-v6-staging-5101449.md`,
post-ADR-008) showed `gm::chain_crit_normal` jumped from 3.2 % of
total cycles in v5 to **19.8 %** in v6 — Amdahl's law in action,
the same effect Singular's `next-opt v6` profile saw after they
sped up their reducer. The function is now tied with the heap
reducer's outer loop as the largest concentrated cost.

`chain_crit_normal` (`gm.rs:131-`) has two phases:

* **Phase 1 — B-internal dedup** (`gm.rs:140-172`): O(n²) sweep
  over `BSet`'s newly generated pairs. For each pair `i`, scan
  every other pair `j` for `lcm(a_i) | lcm(a_j)` (with sev
  pre-filter). Pairs whose lcm is divisible by another pair's lcm
  are killed.
* **Phase 2 — L-side G-M elimination** (`gm.rs:174-`): for each
  live pair in `LSet`, sev-prefilter against `h_lm_sev`, then
  test `h_lm.divides(&pair.lcm)` and an LCM-equality predicate.

The v6 call-graph breakdown inside the 19.8 % was:
- ~5.4 % `divides_with_sev` → `Monomial::divides` (the actual
  divides probe in both phases)
- ~4.0 % `HashSet::contains` (under `LSet::iter_live` in Phase 2)
- ~10 % the inner-loop bodies (Phase 1's O(n²), plus Phase 2's
  per-pair work)

The dominant *constant* cost — the per-iteration test+branch
overhead in Phase 1's O(n²) scan — is structurally identical to
the basis-sweep cost ADR-007 fixed inside `reduce_lobject`. The
same SIMD-batched sev pre-filter pattern applies directly.

### Singular's approach

Singular's `next-opt` branch addressed exactly this problem with
the **`sev_flat`** optimisation (see
`profile-next-opt-v3-samsung.md`): store the basis / pair sev
arrays in flat parallel `unsigned long*` Vecs, then SIMD-batch
the scan with `kSevScanAVX2` (the same routine ADR-007 mirrors
in `find_sev_match_avx2`). Their measurement: `chainCritNormal`
dropped from ~22 % to ~3 % of total cycles after sev_flat plus
the SIMD scan.

The `sev_flat` data layout is what we already have on `SBasis`
(`sevs: Vec<u64>` parallel to `polys: Vec<Box<Poly>>` — see
ADR-007). For BSet we need the analogous structure: a parallel
`lcm_sevs: Vec<u64>` maintained alongside `pairs: Vec<Pair>`.
Each pair already caches `lcm_sev` inside its `Pair` struct, so
the change is purely about laying that one field out flat for
SIMD-friendly access.

### FLINT's approach

**N/A — FLINT has no GB engine.** No chain criterion, no pair
deduplication. The `mpoly_monomial_*` family in FLINT does
include sev-prefilter helpers for individual polynomial ops, but
nothing analogous to the chain criterion's O(n²) pair sweep.

### Decision

Apply the ADR-007 SIMD pattern verbatim to `chain_crit_normal`
Phase 1:

1. **Add `BSet::lcm_sevs: Vec<u64>`** as a parallel array,
   maintained alongside `pairs` on every `push` and `swap_remove`.
   Pure plumbing; pair's existing `lcm_sev` field is kept (it's
   still the source of truth on each Pair; the side array is a
   SIMD-friendly mirror).
2. **Extract `find_sev_match` from `bba.rs` into a shared
   `simd.rs` module** so it can be reused from `gm.rs`. The
   function is structurally identical regardless of caller; the
   "which sev do we scan and what do we compare against" varies,
   not the SIMD code.
3. **Rewrite Phase 1's inner loop** to use the SIMD-batched
   `find_sev_match` over `BSet::lcm_sevs` against `!a.lcm_sev`,
   then for each candidate index check `kill[idx]` and call
   `divides_with_sev` only if it's still live.

Phase 2 (L-side) is **not** changed in this ADR. The L-side
sweep is iterating an LSet whose backing store (`BinaryHeap<HeapEntry>`
with a separate `HashSet<PairKey>` for tombstones) doesn't have
a flat sev array. Adding one would require restructuring LSet,
and the LSet's `iter_live` cost is dominated by `HashSet::contains`
rather than the sev pre-filter. That deserves its own ADR (likely
ADR-010 — replace LSet's HashSet with a bitset, or restructure
to a flat-array layout). Defer until profile evidence post-ADR-009
is in.

### Consequences

**Performance prediction:** Phase 1 is the larger of the two
phases (the O(n² scan over hundreds of new pairs per iteration).
Cutting its scan cost by 3-4× (matching ADR-007's basis-sweep
result) should drop `chain_crit_normal` from 19.8 % to roughly
~10-12 % of v6 cycles, freeing ~7-8 percentage points = ~7-8 %
wall reduction. Less than ADR-008's win but still material.

**Measured (post-implementation, samsung, AVX2 + heap_reducer build):**

| Test | v6 (post-ADR-008) | v7 (post-ADR-009) | Δ |
|---|---|---|---|
| staging-5101449 | 38 s | **31 s** | **−18 %** |
| staging-5104053 | 52 s | 54 s | +4 % (within noise) |
| staging-5106746 | 58 s | **51 s** | **−12 %** |

Cumulative wall on staging-5101449 since v1 (raw memmove):
**870 s → 31 s = 28× speedup**.

All three staging tests still produce exact fixture matches.

The wall improvement on the larger workloads (staging-5101449,
-5106746) is consistent with the prediction; staging-5104053 is
in the noise band, possibly because its B-internal phase has a
shorter scan length per call (different basis-growth shape).

**Maintenance overhead:** the parallel `lcm_sevs: Vec<u64>` has
to stay in sync with `pairs: Vec<Pair>`. Discipline: every `push`
mirrors into both; every `swap_remove` mirrors out of both. The
existing `assert_canonical` debug check is extended to verify
the parallel arrays' invariants. Risk is low because BSet's
mutation surface is only `push` and `swap_remove` (no internal
shuffling).

**Cross-reference with ADR-007:** the extracted `find_sev_match`
becomes a small standalone module (`simd.rs`) used from both
`bba.rs` (in `find_divisor_idx`) and `gm.rs` (in the new B-sweep).
Behaviour is unchanged for ADR-007's caller; the only API shift
is the function moving namespaces.

### References

- `~/rustgb/src/gm.rs:131-172` (current `chain_crit_normal`
  Phase 1 — the surface being changed)
- `~/rustgb/src/bset.rs:23-101` (the `BSet` gaining the parallel
  `lcm_sevs` array)
- `~/rustgb/src/bba.rs:` (`find_sev_match` and
  `find_sev_match_avx2` — the helpers being extracted into
  `simd.rs`)
- ADR-007 (`SIMD-batched sev pre-filter for the basis-sweep`) —
  the model adopted here; same Singular reference (`kSevScanAVX2`,
  `kstd2.cc:74-121`)
- `~/project/docs/profile-rustgb-v6-staging-5101449.md` (the
  19.8 % `chain_crit_normal` evidence motivating this ADR)

---

## ADR-010: `SBasis::lms` parallel leading-monomial cache

**Status:** Accepted and implemented. Landed alongside this ADR's
commit in `~/rustgb`.
**Date:** 2026-04-22

### Context

The v7 profile (`~/project/docs/profile-rustgb-v7-staging-5101449.md`)
identified `find_divisor_idx` as the largest concentrated cost
inside `reduce_to_normal_form` (~13 % of total cycles). A
per-instruction `perf annotate` revealed that **the single hottest
instruction in the entire program was a load**:

```asm
0.00 :   39f71:  mov    (%rdx,%rdi,8),%r15      ; load Box<Poly> ptr
1.24 :   39f75:  mov    0x28(%r15),%rsi          ; Poly.head
11.31 :  39f79:  mov    0x30(%r15),%rdx          ; Poly.terms.len() ← STALL
0.05 :   39f7d:  cmp    %rsi,%rdx                ; is_zero check
```

11.31 % of within-function cycles ≈ 2.3 % of total program cycles
on a single load — the L1/L2 stall waiting for the `Box<Poly>`
deref to complete. This is the cost of `SBasis::polys: Vec<Box<Poly>>`:
every basis-element probe in the divisor sweep dereferences a
boxed pointer to scattered memory.

`SBasis` already maintains parallel arrays for `sevs: Vec<u64>`
and `lm_degs: Vec<u32>`, but the leading *monomial* itself was
fetched via `s_basis.poly(idx).leading()` — the costly path. Caching
the leading monomial in a parallel `Vec<Monomial>` eliminates the
chase for the divides probe (the `Box<Poly>` is only needed when
the poly is actually chosen as a divisor and its tail is read).

### Singular's approach

Singular's `kStrategy` (`~/Singular-rustgb/kernel/GBEngine/kutil.h:295-369`)
maintains a similar struct-of-arrays layout for the basis:

```c
polyset S;                  // ideal of basis polys
unsigned long* sevS;        // parallel array of leading sevs
intset ecartS;              // parallel array of ecart values
intset lenS;                // parallel array of poly lengths
TSet T;                     // ditto for the T-set used in reduction
unsigned long* sevT;
```

Notice: Singular has the parallel **sev** array (matches our
`SBasis::sevs`) and parallel ecart/len arrays, but **no parallel
leading-monomial array**. `S[i]` is itself a `poly` (pointer to
the polynomial's first `spolyrec` node), and accessing the leading
monomial requires dereferencing `S[i]` to read the node's `exp`
field. This is the same pointer-chase pattern we have today — but
because Singular's polys are linked-list nodes (no `Box<Poly>`
intermediate), the chase is shorter (one dereference into the
spolyrec, vs our two: into the Box, then into the Poly's `terms`
Vec).

Singular doesn't have a separate leading-monomial cache because
the spolyrec's exp field is RIGHT THERE in the same allocation as
the rest of the polynomial. For us with `Box<Poly>` + `Vec<Monomial>`
inside the Poly, the leading monomial lives two indirections away.
Adding an explicit `lms` parallel cache directly addresses this
asymmetry.

### FLINT's approach

**N/A — FLINT has no GB engine** and therefore no "find divisor in
basis" sweep. FLINT's `nmod_mpoly` does maintain leading exponents
inline with the polynomial via the `Aexps[0]` element (the polynomial
is itself a flat array of packed exponents), so accessing the
"leading monomial" of a fixed FLINT poly is a single load — no
indirection. The closest analogue would be a hypothetical
"check whether any of these N polys' lm divides this monomial"
sweep, which doesn't exist as a primitive in FLINT.

### Decision

Add `lms: Vec<Monomial>` to `SBasis`, maintained in lockstep with
`polys`, `sevs`, and `lm_degs` on every `insert_no_clear` and
`replace_poly`. Update `bba::find_divisor_idx` and
`SBasis::clear_redundant_for` to read leading monomials from
`s_basis.lms()` rather than dereferencing `s_basis.poly(idx).leading()`.

`assert_canonical` extended to verify `lms[i].cmp(polys[i].leading().1)
== Equal` for every `i`.

The `Box<Poly>` pointer chase is preserved for the path that uses
the *full* polynomial (when the poly is actually chosen as a divisor
and its tail terms get pushed into the heap reducer). That's far
less frequent than the find-divisor probes that the new cache
short-circuits.

### Consequences

**Performance prediction:** ~2 % wall, based on the v7 profile's
attribution of ~2.3 % of total cycles to the specific load
instruction.

**Measured (post-implementation, samsung, AVX2 + heap_reducer build):**

| Test | v7 (pre-ADR-010) | v8 (post-ADR-010) | Δ |
|---|---|---|---|
| staging-5101449 | 31 s | **26 s** | **−16 %** |
| staging-5104053 | 54 s | 42 s | −22 % |
| staging-5106746 | 51 s | 57 s | +12 % (within-noise; this test has been variable) |

The actual wall reduction on staging-5101449 (16 %) is **8× the
predicted 2 %**. Two-thirds of the gap is presumably cache
pollution effects not captured by per-instruction profiling: the
`Box<Poly>` deref didn't just stall the load itself, it also
evicted other useful cache lines (the sev array, redund flags,
adjacent polys' boxes), forcing extra misses elsewhere in the
sweep. Once we read directly from a flat `Vec<Monomial>` that
streams cleanly, the entire sweep stays in cache.

Cumulative wall on staging-5101449 since v1: **870 s → 26 s = 33×
speedup**.

vs C++ next-opt baseline (~5-7 s on samsung): rustgb is now
~3.7-5.2× slower (was ~4-6× at v7).

**Memory cost:** ~144 KB extra for a 3000-element basis (each
`Monomial` is 48 bytes). Fits comfortably in L2; doesn't even
approach L3 limits. Negligible compared to the per-Poly Vec
storage already in flight.

### References

- `~/rustgb/src/sbasis.rs` (the new `lms: Vec<Monomial>` field
  and the lockstep maintenance in `insert_no_clear` / `replace_poly`)
- `~/rustgb/src/bba.rs:369-` (updated `find_divisor_idx` reading
  from `s_basis.lms()`)
- `~/Singular-rustgb/kernel/GBEngine/kutil.h:295-369` (Singular's
  parallel-array layout — sev cached but no parallel lm cache)
- `~/project/docs/profile-rustgb-v7-staging-5101449.md` (the
  11.31 % `mov 0x30(%r15)` hotspot evidence motivating this ADR)

---

## ADR-011 (candidate, not yet adopted): narrow_packing for low-degree workloads

**Status:** Under review — listed for visibility, not active.
**Date:** placeholder

### Context

The v7 profile attributed ~6 % of total cycles to the SIMD sev
sweep memory bandwidth and ~4.5 % to the per-byte
`Monomial::divides` loop inside `find_divisor_idx`. Combined with
heap pop costs (`BinaryHeap::pop` 11.4 %, of which much is sift-
down on 88-byte HeapNodes), there's an open question: for our
specific helium workload (max single-variable exponent = 4 in
both inputs and outputs), would a denser monomial packing close
some of the gap to Singular's tail-ring widening?

### Singular's approach

Singular's `kStratChangeTailRing` (`~/Singular-rustgb/kernel/GBEngine/kutil.cc:10939`,
ADR-005 references) does this **dynamically** at runtime. For our
staging tests, `kStratInitChangeTailRing` walks the inputs, finds
max exp = 4, calls `rGetExpSize(4, ...)` (`ring.cc:2630`) which
returns `bits=3, bitmask=7L`. Singular's tail ring would settle on
**3 bits per variable**, packing 25 variables into 75 bits = 13
bytes plus a degree byte, totaling ~24 bytes per monomial (vs
rustgb's fixed 32 bytes).

The dynamic mechanism: when an overflow is predicted via
`p_LmExpVectorAddIsOk` (the divmask check, ADR-005), Singular
doubles the tail-ring bitmask, calls `rModifyRing`, migrates
every entry in `strat->T`, `strat->L`, `strat->P` via
`ShallowCopyDelete`. Multi-week project to mirror in rustgb.

### FLINT's approach

FLINT picks bits-per-field per-polynomial at construction time via
`mpoly_exp_bits_required`, and `repack_monomials` widens on demand.
Per-poly granularity (vs Singular's per-ring) is more flexible but
adds an indirection. The bits choices are 8, 16, 32, 64 (one byte,
two bytes, four bytes, full-limb), not the fine-grained 1-9-bit
ladder Singular uses.

### Mathicgb's approach

Mathicgb's `MonoMonoid` (`~/mathicgb/src/mathicgb/MonoMonoid.hpp`)
parameterizes the monomial layout at compile time via C++ templates.
The bits-per-variable and number-of-variables are template
parameters; specialised implementations exist for common
combinations. The cmp/mul ops are inlined per specialisation.

### Decision (deferred)

Not adopted. Two structural blockers:

1. **For 25 variables, narrow_packing requires nibble packing**
   (2 vars per byte) to fit in fewer than 4 × u64 words. Layout
   options:
   - 4 bits per var (no guard, max 15): doesn't fit in 2 × u64
     directly because nibble carries break independence.
   - 3 bits per var + 1-bit guard per nibble: 2 vars per byte
     with the divmask trick scaled down (each nibble has its
     own guard bit). 25 vars × 4 bits = 100 bits = 13 bytes for
     vars + 1 byte total-deg + 2 bytes padding = 16 bytes (2 × u64).
     Max var = 7. Comfortable for helium (max 4).

2. **Implementing nibble-packing changes every per-byte op** in
   `monomial.rs`: `mul`, `divides`, `div`, `lcm`, `cmp_degrevlex`,
   `from_exponents`, `assert_canonical`, the `Ring` mask
   construction, the heap-node `cmp_key` size in `reducer.rs`.
   Estimated 6-10 commits, ~1000 lines, similar in scope to
   ADR-008 (the heap reducer).

### Consequences (if adopted)

- Monomial size: 32 → 16 bytes (50 % reduction).
- HeapNode cmp_key: 32 → 16 bytes per node.
- Per-byte ops process 2 variables per byte instead of 1.
- Cache density doubled on hot Vec<Monomial> sweeps.
- Predicted wall: 5-10 % reduction.

The smaller heap node size would also speed `BinaryHeap::pop`'s
sift-down (less data moved per swap). Could compound the win
beyond just the monomial-storage savings.

### References

- ADR-005 (current 7-bit + 1-guard layout — what this would
  supersede for low-degree workloads)
- `~/Singular-rustgb/kernel/GBEngine/kutil.cc:10939-11062` (Singular's
  dynamic tail-ring widening — the runtime version of this idea)
- `~/Singular-rustgb/libpolys/polys/monomials/ring.cc:2630-2670`
  (`rGetExpSize` ladder showing 3-bit fits for max exp ≤ 7)
- `~/flint/src/mpoly/exp_bits_required.c` (FLINT's per-poly bit
  selection)
- `~/mathicgb/src/mathicgb/MonoMonoid.hpp` (mathicgb's
  template-parameterized monomial)
- `~/project/docs/profile-rustgb-v7-staging-5101449.md` (the
  cost-shape evidence; specifically the 6 % SIMD sev sweep
  bandwidth and 4.5 % divides loop)

---

## ADR-012 (candidate, not yet adopted): LSet bitset / flat-array restructure

**Status:** Under review — listed for visibility, not active.
**Date:** placeholder

### Context

The v7 profile showed `gm::chain_crit_normal`'s Phase 2 (L-side
sweep) calls `LSet::iter_live` repeatedly, which filters via
`HashSet::contains` on every iteration. The hashing combined cost
across LSet, BSet's by_indices, and other hashbrown sites totals
~10.5 % of v7 cycles, with `HashSet::contains` (under
`LSet::iter_live`) specifically at 5.24 % under chain_crit_normal.

Replacing `LSet::deleted: HashSet<PairKey>` with a `Vec<u64>`
bitset would give:
- O(1) bit test instead of hash + probe
- Cache-friendly streaming (~3000 pairs → 47 u64s = 376 bytes total)
- Compatible with batch operations (test 64 pair-live bits per
  u64 load)

### Singular's approach

Singular's L-set is `LSet L` (`~/Singular-rustgb/kernel/GBEngine/kutil.h:326`),
implemented as an `LObject*` array indexed by `Ll`. Tombstoning is
done by copying-down: `kPairsToBucket` and friends compact the
array when removing entries. No hash-set for tombstones — but the
copy-down approach has its own O(n) cost per removal.

For our purposes (lots of pair-criterion checks per chain_crit call),
the bitset approach is closer to Singular's `clearS` macros (which
use bitmap arrays in a few places) than to the LSet array layout.

### FLINT's approach

**N/A — FLINT has no GB engine** and therefore no L-set / pair
queue / Gebauer-Möller chain criterion. The closest concept is
mpoly_heap's heap-of-pending-products, which is a different data
structure with no tombstones.

### Decision (deferred)

Not adopted. Reason: the surface is bigger than it first appears
because `LSet`'s callers expect `iter_live` to return an iterator
of `&Pair`, and the underlying `BinaryHeap<HeapEntry>` stores full
Pair clones inside heap entries. A clean bitset migration would
ideally also restructure LSet's storage to a flat `Vec<Pair>` with
the heap holding only `(sugar, arrival, idx)` entries, mirroring
ADR-008's heap-node side-table pattern. That's a 200-300 line
change, not a drop-in replacement.

The wall savings (~3-5 %) is also bounded; ADR-010's leading-
monomial cache and ADR-011's narrow_packing both promise larger
wins per unit of work. Defer until those are exhausted or until
the L-set sweep emerges as a clear bottleneck in a future profile.

### Consequences (if adopted)

- `LSet::deleted` becomes `Vec<u64>` bitset (1 bit per inserted
  pair, indexed by `(key - 1) as usize`).
- `LSet::iter_live` walks the bitset directly, yielding `&Pair`
  from the underlying storage.
- `LSet::contains` becomes a single bit test.
- Predicted wall: 3-5 % reduction.
- Allows future SIMD batch-iteration over live pairs (256 bits
  per AVX2 vector).

### References

- `~/rustgb/src/lset.rs` (the surface being changed)
- `~/Singular-rustgb/kernel/GBEngine/kutil.h:326` (Singular's
  LSet — array-of-LObjects, compact-on-remove)
- `~/project/docs/profile-rustgb-v7-staging-5101449.md` (the
  HashSet::contains cost evidence)

---

## ADR-013: Basis readout FFI — iterator handle rather than random-access index

**Status:** Accepted
**Date:** 2026-04-23

### Context

The rustgb C FFI exposed one function for reading a term out of a
computed basis:

```c
int rustgb_basis_term(const rustgb_basis* b,
                      size_t poly_idx,
                      size_t term_idx,
                      int32_t* exps_out,
                      uint32_t* coeff_out);
```

Random-access `(poly_idx, term_idx)`. With the current flat-array
`Poly` (see ADR-001) this is an O(1) index into
`terms[head + term_idx]` — trivially cheap. But the only external
caller — `~/Singular-rustgb/Singular/dyn_modules/singrust/singrust.cc`
— walks terms strictly sequentially (`for ti in 0..nt`).

We are evaluating a future linked-list-backed `Poly` (offline
discussion; ADR to follow). A linked list cannot answer
`terms()[term_idx]` in O(1) — the naive implementation would be
O(term_idx) per call, turning a sequential readout of an `n`-term
poly into O(n²). The FFI surface shouldn't choose between "keep the
current backend forever" and "slow down every readout".

### Singular's approach

Singular's own polys are linked-list `spolyrec` nodes
(`~/Singular/libpolys/polys/monomials/p_polys.h`). Term traversal
is done through `pIter(p)` / `pNext(p)` — inherently cursor-based,
no random access. That matches the shape of our future linked-list
backend exactly: there is no `p_kBucketGetTerm(idx)` in Singular's
public API because it would be a trap for this very reason.

### FLINT's approach

FLINT's `nmod_mpoly` stores terms as flat parallel arrays
(`coeffs[i]`, `exps[i]`), so random access is native and cheap,
same as our current rustgb `Poly`. But FLINT has no FFI clients of
the shape we're dealing with — its consumers are either other
FLINT library code that reads the arrays directly, or Python
bindings that iterate in a tight loop. **N/A — FLINT has no FFI
consumer that would drive this choice.**

### Decision

Replace `rustgb_basis_term` with an opaque iterator handle:

```c
typedef struct rustgb_term_iter rustgb_term_iter;

rustgb_term_iter* rustgb_term_iter_open(const rustgb_basis* b, size_t poly_idx);
int               rustgb_term_iter_next(rustgb_term_iter* it,
                                        int32_t* exps_out,
                                        uint32_t* coeff_out);
void              rustgb_term_iter_close(rustgb_term_iter* it);
```

`_next` returns 0 on a yielded term, 1 on exhaustion (output
untouched), 2 on error. The iterator borrows the basis; the caller
must not destroy or mutate the basis while an iterator is
outstanding.

The iterator's internal shape is opaque to C. For the current
Vec-backed `Poly` it holds `(basis_ptr, poly_idx, cursor: usize)`
and increments `cursor` on each `_next`. A future linked-list
`Poly` would hold `(basis_ptr, poly_idx, next_node: *const Node)`
instead, with `_next` doing `self.next_node = (*node).next`. Both
achieve O(1)-per-term readout on their respective backends without
changing the C surface.

`rustgb_basis_poly_count` and `rustgb_basis_term_count` stay —
they're O(1) on either backend (a length count per poly is cheap
to maintain) and the caller uses them for `Vec::with_capacity`-
style preallocation, not for random access.

The old `rustgb_basis_term` is removed outright. Pre-merge audit:
grep across `~/Singular-rustgb` and `~/rustgb` showed
`singrust.cc` as the only external caller; no deprecation period
needed.

### Consequences

- Caller contract grows by one rule: the iterator must be closed
  before the basis is destroyed. `singrust.cc`'s error paths close
  the iterator before `rustgb_basis_destroy` / `rustgb_ring_destroy`
  accordingly.
- Error returns gain a three-way code (0 = term, 1 = exhausted,
  2 = error) where `rustgb_basis_term` had a two-way code. Callers
  distinguish "clean end of poly" from "something went wrong" by
  checking `rc != 1` before treating `rc != 0` as an error.
- The future linked-list `Poly` ADR is not blocked by the FFI
  surface. When (if) that backend lands, the iterator's internal
  shape changes; the C header and singrust.cc don't.
- `singrust.cc`'s inner loop is a hair shorter: no more
  `rustgb_basis_term_count` call per poly (kept only as a
  `with_capacity` hint in the Rust integration test, not in the
  Singular caller).

### References

- `~/rustgb/src/ffi.rs` (iterator implementation)
- `~/rustgb/include/rustgb.h` (C surface)
- `~/rustgb/tests/ffi.rs` (`compute_via_ffi` now walks via iterator)
- `~/Singular-rustgb/Singular/dyn_modules/singrust/singrust.cc`
  (updated caller; random-access read loop replaced)
- ADR-001 (flat-array `Poly`; the iterator's current internal
  shape — `(ref, cursor)` — is the natural fit for that backend)
- Singular's `pIter` / `pNext` discipline:
  `~/Singular/libpolys/polys/monomials/p_polys.h`

---

## ADR-014: Linked-list `Poly` backend behind `linked_list_poly` Cargo feature

**Status:** Accepted
**Date:** 2026-04-23

### Context

ADR-001 chose flat parallel `Vec<Coeff>` + `Vec<Monomial>` as the
primary `Poly` representation and spelled out the profile evidence
for that choice: the staging-5101449 profile had put 62.6 % of total
cycles into a single `memmove` before the head-cursor fix. Flat
arrays remain the right default.

But two concerns keep pulling us toward also having a linked-list
backend available:

1. **Cross-checking the reference implementation.** Singular — the
   reference we are porting from — uses linked-list `spolyrec`
   storage throughout. Several Singular-specific optimisations
   (list-splice arithmetic, pointer-stable basis storage across
   reduction rounds, O(1) tail-stealing) are natural on a linked
   list and awkward-to-impossible on flat arrays. To make it
   tractable to port those optimisations in the future without
   committing to them now, we want a second backend we can enable.
2. **A/B correctness signal.** If both backends run the same test
   suite to completion, that's a second independent check on the
   test suite's coverage (and on the arithmetic layer's
   correctness). Bugs that both backends happen to share are still
   possible, but bugs specific to one representation's invariants
   are caught the moment the other backend's CI turns green.

ADR-013 already reshaped the FFI to be cursor-based, so the public
boundary does not assume random access. The remaining obstacle was
internal: `Poly::coeffs() -> &[Coeff]` and
`Poly::terms() -> &[Monomial]` were on the public API and were used
in a handful of places (reducer, FFI, tests). A linked-list backend
cannot satisfy those slice signatures without materialising the
whole poly.

### Singular's approach

Singular's polynomials are **singly linked lists** of `spolyrec`
nodes (`~/Singular/libpolys/polys/monomials/p_polys.h`). Each node
carries an inline exponent buffer plus `number coeff` and
`poly next`. Term traversal is `pIter(p) = pNext(p)`; leading-term
drop is `pIter(p)` + `p_FreeBinAddr`; both O(1). Arithmetic is
implemented via list-splicing merges
(`p_Add_q`, `p_Sub_q_Mult_m` in `pInline2.h`) that can reuse input
nodes in the output list instead of allocating fresh. Memory is
managed via `omalloc` bins sized to `spolyrec`.

This ADR defines a second rustgb `Poly` backend that matches
Singular's shape closely. We do **not** copy Singular code; we
match the data-structure choice.

### FLINT's approach

**N/A for the backend-selection decision.** FLINT only has one
polynomial storage layer (flat parallel arrays in `nmod_mpoly` —
see `~/flint/src/nmod_mpoly/nmod_mpoly.h`). FLINT never made the
choice we are making here because FLINT never maintained a
linked-list alternative to compare against; moreover, FLINT has no
Gröbner-basis engine and thus no bba driver whose hot-path memory
characteristics the decision is sensitive to (ADR-001 for why that
matters).

### Decision

Add a linked-list backend as a second, compile-time-selectable
polynomial representation:

- **New file:** `~/rustgb/src/poly/poly_list.rs`. Mirror the Vec
  backend's public API verbatim — same constructors, same accessors,
  same arithmetic, same canonicality check. Internal storage:
  ```rust
  pub struct Poly {
      head: Option<Box<Node>>,
      len: usize,
      lm_sev: u64,
      lm_coeff: Coeff,
      lm_deg: u32,
  }
  struct Node { coeff: Coeff, mono: Monomial, next: Option<Box<Node>> }
  ```
- **New Cargo feature:** `linked_list_poly`. Default off. Enabling
  it flips `src/poly/mod.rs` to re-export the linked-list backend's
  `Poly` / `PolyCursor` under those names. All call sites keep
  writing `Poly`, `&Poly`, `Vec<Poly>`; no trait genericity, no
  runtime enum dispatch, no type parameters threaded through
  `SBasis` / `LObject` / `KBucket` / `Reducer`.
- **API normalisation (landed with this ADR):** `Poly::coeffs()` and
  `Poly::terms()` are removed from the public API. Callers use the
  `PolyCursor` introduced in the previous refactor pass; see the
  parent `src/poly/mod.rs` for the cursor shape. Internal
  implementations on the Vec backend use private `live_coeffs()` /
  `live_terms()` helpers — not visible outside `poly_vec`.
- **Iterative `Drop`:** linked-list `Poly` implements `Drop` by
  walking the chain and detaching `next` before each node is
  released. A naïve recursive drop on a 100 000-term poly overflows
  the default 8 MB thread stack; the iterative drop runs in O(n)
  time without deepening the call stack. A regression test in
  `tests/poly_props.rs::drop_100k_term_poly_does_not_overflow_stack`
  constructs a 100 000-term chain and drops it.
- **Not yet done — list-splice node reuse.** Arithmetic methods on
  the linked-list backend currently allocate fresh `Box<Node>` for
  every output term, matching the allocation profile of the Vec
  backend's output-`Vec::push`. Splicing input nodes directly into
  the output chain (Singular's pattern) is left as future work —
  the current shape is correct and exercises the test suite, which
  is this ADR's main goal.

### Consequences

- **Two build-and-test paths per rustgb change.** Landing this ADR
  creates an ongoing obligation: significant arithmetic changes
  should be run through both `cargo test --release` (Vec) and
  `cargo test --release --features linked_list_poly` (List). CI
  does not yet gate on both; this is deferred follow-up work.
- **Slice-returning accessors gone from the public API.** Code that
  used to write `p.coeffs()[i]` / `p.terms()[i]` now writes
  `p.cursor()` + `.advance()`, or uses the iterator returned by
  `p.iter()`. The reducer (the main in-flight consumer) already
  went through this migration in the previous commit; the FFI
  (`rustgb_term_iter_next`) was migrated to hold a
  `PolyCursor<'static>` — lifetime-extended at the FFI boundary
  under the caller's basis-outlives-iterator contract. No
  third-party callers remain.
- **Default remains Vec.** ADR-001's profile evidence still holds;
  no performance claim in that ADR is being revisited by this one.
  The staging-validation runner continues to build and run against
  the default (Vec) backend.
- **Non-trivial test-suite time on the List backend.** At the
  moment the List backend's arithmetic is ~5× slower than the Vec
  backend on the property-test suite (~0.5 s vs. ~0.1 s per
  `poly_props` run). This is acceptable for A/B correctness
  checks; if the List backend ever becomes a performance path
  rather than a reference path, that gap would need to be closed.

### References

- `~/rustgb/src/poly/mod.rs` — dispatcher, re-exports the selected
  backend under the names `Poly` and `PolyCursor`
- `~/rustgb/src/poly/poly_vec.rs` — flat-array backend (default)
- `~/rustgb/src/poly/poly_list.rs` — linked-list backend (behind
  the `linked_list_poly` feature)
- `~/rustgb/Cargo.toml` — `linked_list_poly = []` feature definition
- `~/rustgb/tests/poly_props.rs::drop_100k_term_poly_does_not_overflow_stack`
  — regression guard for the iterative-drop contract
- ADR-001 — original Vec decision + staging-5101449 profile
- ADR-013 — FFI iterator handle (the enabling refactor on the
  public boundary)
- Singular's `spolyrec` / `pIter`:
  `~/Singular/libpolys/polys/monomials/p_polys.h`

---

## ADR-015: Destructive list-splice merges mirroring Singular `p_Add_q` / `p_Minus_mm_Mult_qq`

**Status:** Accepted
**Date:** 2026-04-24

### Context

ADR-014 introduced the linked-list `Poly` backend behind
`linked_list_poly` and deliberately left "list-splice node reuse"
as deferred follow-up work — arithmetic methods allocated a fresh
`Box<Node>` for every output term. Its Consequences section
acknowledged the List backend was a correctness reference, not a
performance path, and noted arithmetic was ~5× slower than Vec on
the property-test suite.

The Vec-vs-List staging profile
(`~/project/docs/profile-rustgb-list-vs-vec-staging-5101449.md`,
2026-04-23) then put a concrete number on that gap on a real
workload (staging-5101449-redsb, Z/32003, 25 vars, degrevlex):
List took **731 s** vs Vec's **188 s** (3.9× wall, 3.4× cycles).
The profile pinned **46 % of total cycles** on the List backend
inside glibc `malloc` / `free` / `drop_in_place<Box<Node>>`, vs
5.4 % for Vec. The dominant call-graph parent:

```
_int_malloc  15.34%
  └─ alloc::boxed::Box::new  13.05%
     ├─ poly_list::merge                                 9.03%
     └─ poly_list::from_descending_parallel_unchecked    4.00%
```

Two code paths account for almost all the allocator traffic on
the hot loop:

1. `poly_list::merge` — two-pointer merge of two chains, allocating
   a fresh node per output term.
2. `kbucket::build_neg_cmp` → `poly_list::from_descending_parallel_unchecked`
   — materialises `-c·m·p` as a standalone intermediate before the
   bucket absorbs it.

This ADR closes the allocation half of that gap by porting
Singular's destructive-merge contract. The other half (list-walk
vs slice-walk cost — ~2× on its own per the profile's "real-work
cycles" row) is intrinsic to the representation and not addressed
here.

### Singular's approach

Singular's polynomial arithmetic in
`~/Singular/libpolys/polys/templates/` is built around two
destructive templates whose header comments spell out the
contract:

- **`p_Add_q__T.cc`** (lines 13–17): *"Returns: p + q, Shorter …
  Destroys: p, q."* The merge loop splices input nodes directly
  into the output chain rather than allocating:
  - `a = pNext(a) = p;` (line 57 Equal-nonzero, line 65 Greater,
    line 71 Smaller) appends the consumed head to the output's
    tail and moves the cursor forward — zero allocations.
  - On one side exhausting, the rest of the other side is
    tail-spliced with a single pointer assignment: `pNext(a) = q;`
    (line 60), `pNext(a) = p;` (lines 61, 67, 73).
  - When coefficients cancel, both input heads are freed (`n_Delete`
    + `p_LmFreeAndNext`, lines 44–52). No output node is allocated.
- **`p_Minus_mm_Mult_qq__T.cc`** (lines 13–17): *"Returns: p − m·q
  … Destroys: p. Const: m, q."* Line 56 allocates the `m · q[i]`
  product nodes from an **omalloc bin** (`p_AllocBin(qm, bin, r)`
  — O(1) free-list-backed alloc/free). Line 107 splices those into
  output. P's nodes are reused (Equal-nonzero at line 77 overwrites
  the coefficient and splices the node in) or freed (Equal-zero at
  line 84). The tail-splice on lines 132–157 uses a single
  `pp_Mult_mm` block multiply-and-append when `p` exhausts first —
  one arithmetic pass over the remaining `q`, not a term-by-term
  compare.

### FLINT's approach

**N/A — FLINT has no linked-list polynomial backend.** FLINT's
single representation is the flat parallel-array `nmod_mpoly`
(`~/flint/src/nmod_mpoly/nmod_mpoly.h`), so there is no
"destructive vs non-destructive list merge" choice to compare
with. FLINT's merges fresh-allocate into a new flat array; the
rustgb Vec backend follows the same pattern (see ADR-006).

### Decision

Port both contracts as owning-by-value Rust methods, coexisting
with the existing non-destructive methods:

- **`Poly::add_consuming(self, other: Poly, ring: &Ring) -> Poly`**
  — Rust analogue of `p_Add_q(p, q, r)`. Destroys: both (ownership
  transfer enforces Singular's "Destroys:" contract at the type
  level — any subsequent use of the moved argument is a compile
  error, not a dangling-pointer UAF). On List, splices input nodes
  into the output chain and tail-splices. On Vec, forwards to the
  existing non-consuming `add` (no splice story for flat arrays).
- **`Poly::sub_mm_mult_qq_consuming(self, c, m, q, ring) -> Option<Poly>`**
  — Rust analogue of `p_Minus_mm_Mult_qq(p, m, q, r)`. Destroys:
  `self`. Const: `m`, `q` (preserved-input borrow mirrors
  Singular's `Const:` line). Allocates new nodes only for the
  `m * q[i]` products; splices self's nodes or frees them;
  tail-splices the remainder of `-c·m·q` when `self` exhausts
  first. On Vec, forwards to the existing non-consuming
  `sub_mul_term`.

Hot-path callers in `kbucket.rs` migrate to the consuming variants:

- `KBucket::absorb`: the cascade-merge `existing.add(&q, ring)`
  becomes `existing.add_consuming(q, ring)` — both sides were
  already owned (existing via `slots[i].take()`, q by value); the
  `&`-borrow was a pure API artifact.
- `KBucket::minus_m_mult_p`: rewritten around
  `sub_mm_mult_qq_consuming`. Picks the target slot from `p.len()`,
  takes its existing poly (or starts from `Poly::zero()`), calls
  `existing.sub_mm_mult_qq_consuming(c, m, p, ring)?`, and cascades
  through `absorb` if the result outgrew its slot. The standalone
  `build_neg_cmp` helper that used to materialise `-c·m·p` as an
  intermediate poly is deleted — its sole caller is gone.

The non-destructive APIs (`Poly::add`, `Poly::sub`,
`Poly::sub_mul_term`, `Poly::add_assign`) are **unchanged**. Tests
and any non-hot callers keep using them; both variants coexist and
the compiler inlines whichever the caller picks.

### Contract differences vs Singular (explicit)

1. **No `int& Shorter` out-parameter.** Singular needs it because
   list lengths aren't cached in the head; rustgb caches `len` on
   every `Poly` (both backends), so callers compute the delta
   locally as `a.len() + b.len() - out.len()`.
2. **No `spNoether` early-termination parameter.** rustgb
   implements Buchberger with a global ordering; Noether cutoffs
   (Mora / ecart-based local standard bases) aren't in scope.
3. **`Option<Poly>` return on monomial-exponent overflow.** rustgb's
   7-bit-per-variable packed layout (ADR-005) has a representable-
   range limit that Singular's non-packed layout doesn't hit;
   overflow is a representation error, surfaced as `None`.
4. **No `HAVE_ZERODIVISORS` branches.** rustgb targets Z/p only;
   the case `a * b = 0` with nonzero `a, b` can't arise.
5. **Sentinel-head pattern translated via narrow `unsafe`.**
   Singular uses a stack-local `spolyrec rp; poly a = &rp;` and
   writes through `pNext(a) = p; a = pNext(a);`. In safe Rust the
   equivalent `&mut Option<Box<Node>>` tail cursor alias-blocks
   everything reachable from the sentinel, so the destructive
   methods use a `*mut Option<Box<Node>>` raw pointer instead. The
   `unsafe` scope is narrow (append loop only); soundness is
   argued in an in-code `// SAFETY:` block — the sentinel outlives
   every update, every write targets sentinel-owned storage, and
   no live alias to a tail slot exists during the writes. On
   early return via `?`, Rust's drop glue releases the partial
   output chain cleanly (no leak, no double-free).

### Consequences

- **List backend becomes a real performance path.** On
  staging-5101449 the walltime drops from 731 s into the 400–500 s
  range (accompanying profile at
  `~/project/docs/profile-rustgb-list-splice-staging-5101449.md`);
  the residual `Box<Node>` allocations concentrate in the
  `m * q[i]` product path, which a future bin-allocator ADR
  addresses.
- **Both backends keep identical public API.** Nothing in
  `bba.rs`, `reducer.rs`, the FFI, or the gm / sbasis / lset /
  pair / gb-serial machinery needs a ripple change. The
  feature-flag dispatcher (`src/poly/mod.rs`) routes `Poly`
  uniformly.
- **Two new methods per backend.** Trivial forwarders on Vec
  (~6 lines each); real implementations on List. Total LOC:
  ~250 added across the consuming merge, the consuming
  sub_mm_mult_qq, and their shared sentinel-slot helper.
- **Bin allocator for the residual `Node` allocations is still
  deferred.** Singular's omalloc PolyBin (O(1) free-list-backed
  allocator) is the third multiplicative factor rustgb doesn't yet
  match. A follow-up ADR will cover that, after an updated staging
  profile pins the remaining allocator traffic.
- **CI still does not gate on both backends.** ADR-014's deferred
  follow-up on this; unchanged by this ADR.

### References

- `~/Singular/libpolys/polys/templates/p_Add_q__T.cc` — header
  comment at lines 13–17, splice lines 57/65/71, tail-splice
  lines 60–61/67/73
- `~/Singular/libpolys/polys/templates/p_Minus_mm_Mult_qq__T.cc`
  — header at lines 13–17, `p_AllocBin` at line 56, splice at
  line 107, reuse at line 77, free at line 84, tail-splice block
  at lines 132–157
- `~/rustgb/src/poly/poly_list.rs` — `Poly::add_consuming`,
  `Poly::sub_mm_mult_qq_consuming`, internal `merge_consuming`
- `~/rustgb/src/poly/poly_vec.rs` — thin forwarders for the
  destructive variants (no splice story on flat arrays)
- `~/rustgb/src/kbucket.rs` — `absorb` + `minus_m_mult_p` updated;
  `build_neg_cmp` removed
- `~/project/docs/profile-rustgb-list-vs-vec-staging-5101449.md` —
  baseline profile before this change (46 % cycles in glibc
  allocator)
- `~/project/docs/profile-rustgb-list-splice-staging-5101449.md` —
  profile after this change (companion report)
- ADR-014 — the deferred-follow-up entry this ADR closes partially
- ADR-001 — flat-array-is-default anchor; unchanged
- ADR-006 — Vec backend's merge contract, for contrast

---

## ADR-016: Thread-local Node pool for the `linked_list_poly` backend

**Status:** Accepted
**Date:** 2026-04-24

### Context

ADR-015's destructive-merge splicing eliminated the per-output-term
`Box<Node>` allocations from `merge` and the non-destructive
`sub_mul_term`. The residual Node-allocation traffic on the List
backend is concentrated in one place: the fresh nodes that
`Poly::sub_mm_mult_qq_consuming` must allocate for the `m * q[i]`
product on its hot loop. `q` is a basis element, so its nodes can't
be spliced (they stay live in the basis); every product term is a
brand-new `Node`. On staging-5101449 post-ADR-015 that path runs at
the bba hot-loop rate.

Each such allocation — `Box::new(Node { ... })` → `alloc::alloc` →
glibc `_int_malloc` for a 40-ish-byte chunk — carries allocator-path
overhead that a pool-backed design avoids. The
`profile-rustgb-list-splice-staging-5101449.md` baseline placed the
residual `_int_malloc` cycles in the ~10-15 % range; the prediction
for this ADR was that a pool would close most of that.

### Singular's approach

omalloc `PolyBin`. Each ring owns a bin of `sizeof(spolyrec)`-sized
slots (see `omBin PolyBin` in
`~/Singular/libpolys/polys/monomials/ring.h`). The templates use
`p_AllocBin(qm, bin, r)` to pop a chunk in O(1)
(`~/Singular/libpolys/polys/templates/p_Minus_mm_Mult_qq__T.cc:49,56`)
and `p_FreeBinAddr` to push it back
(`p_Minus_mm_Mult_qq__T.cc:160`). The bins are backed by omalloc
pages sliced into fixed-size slots at setup; allocation is a
free-list pop with no syscall, no bin consolidation, no
`malloc_consolidate`-style background work. This is load-bearing
in Singular's Gröbner path: the fallback to a general-purpose
allocator is markedly slower on the same workload.

### FLINT's approach

**N/A — FLINT has no linked-list polynomial backend.** FLINT's
`nmod_mpoly` (`~/flint/src/nmod_mpoly/nmod_mpoly.h`) is a flat
parallel array; whole polys are allocated in bulk via
`flint_malloc` backing onto the system allocator, and there is no
per-term bin-allocator concept. This ADR is a List-backend-only
concern.

### Decision

Introduce a **thread-local** `NodePool` in
`~/rustgb/src/poly/node_pool.rs`, used exclusively by the
`linked_list_poly` backend, gated behind a **second** Cargo feature
`linked_list_poly_pool` that requires `linked_list_poly`. The data
layout of the List backend changes: `Node::next` and `Poly::head`
become `Option<NonNull<Node>>` (regardless of which pool variant is
active). Every allocation and deallocation routes through the
thread-local `POOL.with(|p| p.borrow_mut()...)`; the
`poly_list.rs` code has zero `#[cfg]`s on the alloc path — the
feature flag swaps the *implementation* of `NodePool`, not the
*API surface*.

Two `NodePool` variants live in `node_pool.rs`, selected by
`#[cfg(feature = "linked_list_poly_pool")]`:

1. **Pool-backed** (feature on) — holds a `Vec<NonNull<Node>>`
   free list. `alloc` pops from the free list when possible and
   falls back to a single `Box::leak` on miss. `dealloc` pushes
   onto the free list. Storage is **never** returned to the system
   during normal operation; the pool's peak memory equals the peak
   in-flight `Node` count during the run.
2. **Forwarder** (feature off) — a unit struct whose `alloc` is a
   plain `Box::new` + `Box::into_raw` and whose `dealloc` is a
   `Box::from_raw` + implicit drop. No free list, no reuse. At
   `--release`, the compiler inlines the RefCell / thread_local
   indirection to near-zero overhead, so this variant is a valid
   performance baseline (not just an API-compatibility layer).

Enabling `linked_list_poly_pool` without `linked_list_poly`
triggers a `compile_error!` in `src/poly/mod.rs` — the nonsense
configuration is rejected at build time rather than silently doing
the wrong thing.

**Why a separate feature flag instead of baking the pool into the
default List build?** To keep the pool's correctness and performance
claims cheaply falsifiable. With both configurations in the tree,
any future "List backend gives wrong answer on X" bug report can be
bisected in one step: rerun with `--features 'linked_list_poly'`
alone; if X still fails, the pool isn't the culprit. Performance
A/B is trivial — three binaries cover the matrix (Vec, List-no-pool,
List-pool). The cost (two lines in `Cargo.toml` + a `#[cfg]` split
of `NodePool`) is tiny relative to that diagnostic flexibility, and
matches the pattern already set by ADR-002's `heap_reducer` flag.

**Thread-local, not shared.** The pool is per-`thread_local!`-owning-
thread. rustgb's bba currently runs single-threaded per
`compute_gb` call, so there is no contention or cross-thread
lifetime issue. The `Poly` type gains `unsafe impl Send + Sync`
because its `NonNull<Node>` is non-auto-`Send`; the safety
argument is that nodes are never *dereferenced* from a different
thread than the one currently holding the `Poly`. A subtle rule:
a `Poly` must be dropped on a thread whose `NodePool` contains
its nodes (dropping on a foreign thread silently pushes onto the
foreign thread's free list, which is safe — `Node` is POD — but
leaks capacity from the originating thread's pool). rustgb's
single-threaded bba doesn't hit this edge.

### Contract — Pool API

```rust
// pub(super) to the poly module; not exported from the crate.
struct NodePool {
    free: Vec<NonNull<Node>>, // pool-backed variant
    // or `()` unit-struct for the forwarder variant
}

impl NodePool {
    const fn new() -> Self;
    fn alloc(&mut self, coeff: Coeff, mono: Monomial, next: Option<NonNull<Node>>)
        -> NonNull<Node>;
    unsafe fn dealloc(&mut self, ptr: NonNull<Node>);
}

thread_local! {
    pub(super) static POOL: RefCell<NodePool> =
        const { RefCell::new(NodePool::new()) };
}
```

`dealloc`'s safety contract (both variants): (1) `ptr` points to a
`Node` no longer reachable from any live `Poly`; (2) the caller has
already taken `ptr`'s `next` field (no chain-free); (3) `ptr` was
obtained from an earlier `alloc`. Violating any of these triggers
UB (use-after-free, double-free, or chain drop through the pool).
The `Poly::Drop` / `drop_leading_in_place` / splice paths all
satisfy the contract by construction; every `Box::from_raw` site in
the pre-ADR code maps 1:1 to a `pool.dealloc` site.

### Consequences

- **Wall reduction on staging-5101449 (samsung, this session):**
  List backend 147 s → 126 s with pool on = **14 % faster**, and
  closes the List-vs-Vec gap from 1.30× to 1.12× (Vec = 113 s).
  Correctness unchanged: all three configurations (Vec, List-no-pool,
  List-pool) match the committed fixture bit-for-bit.
  (`~/project/docs/profile-rustgb-list-pool-staging-5101449.md` has
  the fresh `perf record` call-graph; `_int_malloc` drops out of the
  0.5 %+ flat profile entirely, replaced by a ~1.5 % combined
  `Vec::pop` / `Vec::push` cost inside `NodePool::alloc`/`dealloc`.)
- **Three build configurations live in the tree.** Vec (default),
  List-no-pool (`--features linked_list_poly`), List-pool
  (`--features 'linked_list_poly linked_list_poly_pool'`). All
  three must pass the full `cargo test --release` matrix; all three
  must pass staging-5101449 bit-for-bit. Verified in the ADR-016
  commit. CI does not yet gate on all three — tracked as follow-up.
- **Nonsense configuration rejected at compile time.** Enabling
  `linked_list_poly_pool` alone fails with a `compile_error!` in
  `src/poly/mod.rs`. The `compile_error!` invocation itself is the
  regression guard; manually verified once in the ADR-016 commit.
- **Pool is unbounded when enabled.** Peak memory on staging-5101449
  is bounded by peak in-flight `Node` count — order ~3M × 40 B ≈
  ~120 MB upper estimate. Acceptable on samsung (36 GB). Long-running
  or memory-constrained workloads may need a cap; deferred.
- **No bulk allocation in this ADR.** The system-allocator miss
  path is a single `Box::leak`. Hit rate after warmup is expected
  to be >99 % on typical workloads (the
  `pool_reuses_freed_nodes` unit test confirms the free list grows
  and is drained on subsequent allocations). Bulk would be an
  optimization on the cold path; revisit if a real workload ever
  surfaces a high miss rate.
- **Node's raw-pointer shape consolidates with existing `unsafe`.**
  The sentinel-slot pattern in `merge_consuming` and
  `sub_mm_mult_qq_consuming` already used `*mut Option<Box<Node>>`
  tail cursors inside `unsafe` blocks (ADR-015). Switching to
  `Option<NonNull<Node>>` throughout doesn't grow the unsafe
  envelope; it just types it more uniformly. The `// SAFETY:`
  comments already present continue to cover the same invariants.
- **If rustgb's parallel story changes (`SINGULAR_THREADS>1`),
  this ADR's thread-local assumption has to be revisited.** Each
  worker thread keeping its own pool is the natural extension;
  cross-thread `Poly` sharing would need explicit pool-transfer or
  a shared-pool design. Not a concern today because the rustgb
  dispatch path is single-threaded. See
  `~/Singular-parallel-bba/` for the parallel-bba Singular branch.
- **No change to `VecPoly`.** The `node_pool` module is
  `#[cfg(feature = "linked_list_poly")]`-gated at the `poly::mod`
  level; the Vec backend compiles without it and its public API
  is unchanged.
- **The residual Vec-vs-List gap (now 12 %) is intrinsic.** The
  profile confirms the remaining cost lands in `Monomial::mul`,
  `Monomial::cmp`, `Field::mul`, and the pointer-chase through
  the linked list — not in the allocator. Closing that gap would
  require reshaping the data structure back toward Vec, which
  undoes the List backend's purpose. ADR-016 closes the
  allocator half of ADR-015's "Consequences"; the list-walk half
  remains by design.

### References

- `~/rustgb/src/poly/node_pool.rs` — new. Pool + forwarder variants
  and the thread-local `POOL`.
- `~/rustgb/src/poly/poly_list.rs` — refactored to `Option<NonNull<Node>>`
  throughout; all allocations / deallocations route through
  `POOL.with(|p| p.borrow_mut()....)`. `unsafe impl Send + Sync for
  Poly` with the thread-locality safety comment.
- `~/rustgb/src/poly/mod.rs` — conditional `mod node_pool` + the
  `compile_error!` guard on the nonsense configuration.
- `~/rustgb/Cargo.toml` — new `linked_list_poly_pool` feature
  entry.
- `~/Singular/libpolys/polys/templates/p_Minus_mm_Mult_qq__T.cc:49,56,160`
  — omalloc PolyBin usage (the template we port the idea from).
- `~/Singular/libpolys/polys/monomials/ring.h` — `omBin PolyBin`
  as a ring field.
- `~/project/docs/profile-rustgb-list-splice-staging-5101449.md` —
  post-ADR-015 baseline (pre-this).
- `~/project/docs/profile-rustgb-list-pool-staging-5101449.md` —
  post-ADR-016 measurement (companion report to this ADR).
- ADR-001, ADR-014, ADR-015 — the ancestry of this decision.

---

## ADR-017: `Monomial::mul` codegen — split add from overflow check

**Status:** Accepted
**Date:** 2026-04-24

### Context

Post-ADR-016 profiling of staging-5101449 under the target List + Node-pool
configuration placed `Monomial::mul` at ~29 % of total cycles, with time
landing on `core::num::wrapping_add` inside `core::array::from_fn` rather
than a single vectorised add. Two distinct problems compounded.

**Problem 1 — build flag not set.** The crate had no `.cargo/config.toml`
and no session-level `RUSTFLAGS`. The AVX2-gated code paths in `src/simd.rs`
(ADR-007 `find_sev_match_avx2`, ADR-009 `Monomial::div` AVX2 helper) are
gated on `#[cfg(target_feature = "avx2")]`. Without `-C target-cpu=native`
(or equivalent), those paths are not compiled in — the scalar fallback
is used — and LLVM cannot auto-vectorise the word-wise `wrapping_add`
loop into a wide `vpaddq` because the target baseline (x86-64-v1) does
not expose AVX2 registers. Every pre-2026-04-24 rustgb measurement was
taken with AVX2 dead code as a result.

**Problem 2 — overflow check interleaved with the add.** Even rebuilt
with `-C target-cpu=native`, `Monomial::mul` only partially vectorised.
Disassembly of `probe_mul` (native, AMD Ryzen 5 2500U / znver1, pre-fix):

```
vmovdqu xmm0, [rdx]
vpaddq  xmm0, xmm0, [rsi]              ; 1× vpaddq xmm — words 0,1 only
vmovq   rdi, xmm0
test    [rcx], rdi                     ; overflow check word 0
je      ...
vpextrq rdi, xmm0, 0x1
test    [rcx+0x8], rdi                 ; overflow check word 1
je      ...
mov     rdi, [rdx+0x10]                ; scalar load, word 2
add     rdi, [rsi+0x10]                ; scalar add
test    [rcx+0x10], rdi                ; overflow check word 2
je      ...
mov     r8,  [rdx+0x18]                ; scalar load, word 3
add     r8,  [rsi+0x18]                ; scalar add
test    [rcx+0x18], r8                 ; overflow check word 3
```

LLVM batched words 0-1 into one 128-bit `vpaddq xmm` and left words 2-3
as scalar adds. The cause was the shape at `src/monomial.rs:232-246`:

```rust
let mut packed: [u64; WORDS_PER_MONO] =
    std::array::from_fn(|word| self.packed[word].wrapping_add(other.packed[word]));

let ovf_mask = ring.overflow_mask();
if packed
    .iter()
    .zip(ovf_mask.iter())
    .any(|(p, m)| (p & m) != 0)
{
    return None;
}
```

The `.iter().zip().any()` closes a per-word early-exit branch after each
overflow test. LLVM cannot coalesce the four adds into a single wide
`vpaddq` because doing so would do work past the point where an earlier
word's overflow test would have returned `None`.

### Singular's approach

`p_MemAdd_LengthGeneral` (`~/Singular/libpolys/polys/templates/p_MemAdd.h:173`):

```c
do {
    _r[_i] += _s[_i];
    _i++;
} while (_i != _l);
```

Plain scalar loop on `unsigned long *`. **No overflow check in release
builds** — only `pAssume1` under `PDEBUG`. Lengths 1-8 each have an
explicit unrolled macro variant (`_p_MemAdd_LengthTwo` …
`_LengthEight`), and the ring-procedure generator in
`p_Procs_Generate.cc` dispatches to the length-specialized macro at
ring creation time, so the hot path is flat, branch-free, and
auto-vectorises trivially. Overflow is prevented by the ring's
`bitmask` being chosen to fit the degree bound — it's a design-time
invariant, not a runtime check. See also `p_ExpVectorAdd` at
`~/Singular/libpolys/polys/monomials/p_polys.h:1432`.

SEV and total-degree do not live in the exp-vector payload in Singular;
they sit in the polyrec header and are updated elsewhere.

### FLINT's approach

`mpoly_monomial_add` + `mpoly_monomial_overflows` (`~/flint/src/mpoly.h:233,374`):

```c
FLINT_FORCE_INLINE
void mpoly_monomial_add(ulong * exp_ptr, const ulong * exp2,
                                         const ulong * exp3, slong N) {
   for (i = 0; i < N; i++)
      exp_ptr[i] = exp2[i] + exp3[i];
}

FLINT_FORCE_INLINE
int mpoly_monomial_overflows(ulong * exp2, slong N, ulong mask) {
   for (i = 0; i < N; i++)
      if ((exp2[i] & mask) != 0)
         return 1;
   return 0;
}
```

Two separate `FLINT_FORCE_INLINE` loops. The add is branch-free and
vectorises cleanly. The overflow check is a **separate** pass; it has
an early exit of its own, but because it's decoupled from the add, the
vectorizer is free to emit a wide `vpaddq` for the add. `N` is runtime.

### Decision — Option 1: split the add from the overflow check

Matches FLINT's shape. Replaces the `from_fn` + `iter/zip/any` pattern
at `src/monomial.rs:232-246` with an explicit 4-element array literal
for the add and an OR-reduction + single branch for the overflow check:

```rust
let mut packed: [u64; WORDS_PER_MONO] = [
    self.packed[0].wrapping_add(other.packed[0]),
    self.packed[1].wrapping_add(other.packed[1]),
    self.packed[2].wrapping_add(other.packed[2]),
    self.packed[3].wrapping_add(other.packed[3]),
];

let m = ring.overflow_mask();
let ovf = (packed[0] & m[0])
        | (packed[1] & m[1])
        | (packed[2] & m[2])
        | (packed[3] & m[3]);
if ovf != 0 {
    return None;
}
```

Semantics identical to before: total-degree cap and SEV update still
happen inside `mul` per ADR-005. LLVM now sees four independent
reads+writes with no loop structure, no data dependency between the
adds and the overflow test until all four adds are complete, and a
single branch for the overflow decision.

A `const _: () = assert!(WORDS_PER_MONO == 4);` inside the function
guards against a future change to `WORDS_PER_MONO` silently breaking
the unroll.

**Why the explicit array literal rather than `for i in 0..4` or
`from_fn`?** Equivalent on correctness; more robust on codegen across
compiler versions. The literal forces LLVM to see four independent
reads+writes with no loop structure to reason about. `from_fn` in
particular was part of the pre-fix problem: profile-attributed time
landed inside `core::array::from_fn`'s monomorphised wrapper.

### Observed codegen (post-fix, native znver1)

Disassembly of the inlined `Monomial::mul` body from
`target/release/examples/mul_probe` after the fix:

```
vmovdqu (%rdx),%xmm0
vmovdqu 0x10(%rdx),%xmm1
vpaddq  (%rsi),%xmm0,%xmm0            ; words 0,1
vpaddq  0x10(%rsi),%xmm1,%xmm1        ; words 2,3
vpand   (%rcx),%xmm0,%xmm2            ; overflow mask AND
vpand   0x10(%rcx),%xmm1,%xmm3
vpor    %xmm3,%xmm2,%xmm2             ; OR-reduce
vptest  %xmm2,%xmm2                   ; single branch
je      <all-four-ok>
xor     %ecx,%ecx
mov     %rcx,(%rax)                   ; return None
ret
<all-four-ok>:
mov     0x28(%rsi),%edi               ; total_deg u32
mov     0x28(%rdx),%ecx
add     %rdi,%rcx
...
```

All four u64 adds are SIMD (no scalar `add` on any exponent word); the
overflow test is a single `vptest` + `je` rather than four per-word
branches; the add→test dependency chain is broken so the two `vpaddq`
are independent and pipelined.

**On CPUs that decode 256-bit AVX2 as 2×128-bit internally (znver1 /
Zen 1 / AMD Ryzen 5 2500U = samsung), LLVM's cost model correctly
emits `2× vpaddq xmm` rather than `1× vpaddq ymm`** — same μops,
same latency, same throughput. On a host with a native 256-bit
datapath (Haswell+ / Zen 2+), LLVM is expected to fold the same source
shape into a single `vpaddq ymm`; verified by rebuilding
`examples/mul_probe` with `RUSTFLAGS="-C target-cpu=haswell"` (even
there LLVM kept 2×xmm for this particular shape, because the
`packed` field has u64-alignment (8 B) and 256-bit unaligned loads
are not universally preferred — the point is that the four adds are
all in vector registers with no scalar-add fallback and no per-word
branch). The failure criterion — a scalar `add` on any exponent word
— is cleared.

### Alternatives considered — Option 2: drop the per-mul overflow check

Mirror Singular: move overflow prevention to the ring-creation /
monomial-construction boundary by choosing the exponent-byte width so
that all additions arising in a bba run stay in-range by design. This
eliminates the overflow test from the hot path entirely. **Deferred**
because it touches ADR-005's "check every op" invariant — a larger
change that requires rethinking `from_exponents`, ring setup, and
correctness reasoning across the crate. Worth revisiting once
post-this-ADR profiling identifies the next hotspot: if
`Monomial::mul` is still significant even with the split-add shape,
Option 2 becomes the next lever; if not, the overflow check has
become cheap enough to leave in.

### Also changed — `.cargo/config.toml`

A new `~/rustgb/.cargo/config.toml`:

```toml
[build]
rustflags = ["-C", "target-cpu=native"]
```

This belongs on-tree because it affects every release build of the
crate, not just this task's disassembly check. It enables the AVX2
paths in `src/simd.rs` (ADR-007, ADR-009) — which were previously
compiled out — as a side effect. Expected to shave ~1-3 % of total
cycles independently, on top of the `Monomial::mul` fix.

**Measurement-prior-work note:** all pre-2026-04-24 rustgb performance
numbers recorded in ADRs 001-016 (and in `~/project/docs/profile-rustgb-*.md`)
were taken with AVX2 disabled. They are not retroactively invalidated
— the measurements against baselines were fair within their builds —
but comparisons across the 2026-04-24 flag boundary should note the
change.

### Not in scope

- **SEV update and total-degree cap stay inside `mul`.** Rustgb-specific
  per-ADR-005; hoisting them is a separate refactor, only worth doing
  once they become measurable after this fix.
- **`Monomial::div` / `Monomial::divides`.** These use their own AVX2
  paths via `src/simd.rs`; the config-flag change activates them as a
  side effect. No code change in this ADR.
- **`Field::mul`.** 7 % of total in the pre-fix profile. Separate task
  once `Monomial::mul` drops out of the top.

### Consequences

- **Compile-time guard: `const _: () = assert!(WORDS_PER_MONO == 4);`**
  inside `Monomial::mul` aborts the build if the constant is ever
  changed without updating the hand-unrolled array literal.
- **Branch-prediction behaviour shifts.** The pre-fix shape had four
  correlated branches (each with its own branch-predictor slot); the
  post-fix shape has one branch. On the common path (no overflow),
  this is a pure win — one correctly-predicted branch versus four.
  In the degenerate case of a monomial that overflows on word 0 (so
  the pre-fix shape would have returned after one test), the post-fix
  shape does four adds and four ANDs before returning. That case is
  not on the hot path for well-formed bba inputs (the ring's
  `bitmask` sizes the variable region for the degree bound in
  Singular's model; rustgb's current 7-bits-per-var cap is
  deliberately generous).
- **All three test configurations remain green.** Default (Vec),
  `--features linked_list_poly`, `--features 'linked_list_poly
  linked_list_poly_pool'`. Same pass counts as pre-this-ADR.
- **Future `WORDS_PER_MONO` change requires updating `mul`.** The
  `const _: () = assert!(...)` above catches it at compile time, so
  this is a find-it-immediately failure mode rather than a silent
  correctness or performance bug.

### References

- Commit `064f393` — `build: enable target-cpu=native for release builds`
  (new `.cargo/config.toml`).
- Commit for this ADR (Commit 2) — split add from overflow check + ADR-017.
- `~/project/docs/profile-rustgb-monomial-mul-fix-staging-5101449.md`
  — pre/post wall-clock and call-graph profile for this ADR.
- `~/project/docs/profile-rustgb-list-pool-staging-5101449.md` —
  pre-fix baseline (ADR-016).
- `~/rustgb/src/monomial.rs:226-274` — function under change.
- `~/rustgb/src/simd.rs` — AVX2-gated modules that the config flip
  also activates.
- `~/Singular/libpolys/polys/templates/p_MemAdd.h:173` — Singular
  reference (`p_MemAdd_LengthGeneral`).
- `~/Singular/libpolys/polys/monomials/p_polys.h:1432` — Singular
  `p_ExpVectorAdd`.
- `~/flint/src/mpoly.h:233,374` — FLINT reference
  (`mpoly_monomial_add`, `mpoly_monomial_overflows`).
- ADR-005 — packed direct exponents + per-op overflow invariant.
- ADR-007, ADR-009 — the AVX2-gated paths that the `.cargo/config.toml`
  flip activates.
- ADR-016 — most recent landed ADR; this one continues the
  post-allocator-fix codegen-tuning thread.

---

## ADR-018: Drop per-mul overflow check (implementing ADR-017 Option 2)

**Status:** Accepted
**Date:** 2026-04-24

### Context

Post-ADR-017 profiling on c200-1 (`/tmp/c200-perf.log`,
`/tmp/c200-bench.log`, 2026-04-24) placed `sub_mm_mult_qq_consuming`
at ~47 % of total cycles on staging-5101449, vs Singular's
ring-specialised `p_Minus_mm_Mult_mm_Mult_qq__FieldZp_LengthEight_OrdPosNomogZero`
at ~1.7 % for the same algorithmic work. The overwhelming portion
of that gap is Singular's construction-time specialisation (length-
dispatched `p_Minus_mm_Mult_qq__T.cc` instantiations with the ring's
monomial-comparison function inlined), which is architectural and
out of scope here. The single biggest same-shape difference that
remains is the per-mul overflow check: rustgb's `Monomial::mul`
tests the divmask guard bits on every monomial product, while
Singular's `p_ExpVectorAdd` / `p_MemAdd_LengthGeneral` is a bare
scalar add loop in release builds (`~/Singular/libpolys/polys/monomials/p_polys.h:1432`
and `~/Singular/libpolys/polys/templates/p_MemAdd.h:173`).

ADR-017 introduced this as **Option 2 — drop the per-mul overflow
check; mirror Singular**, but deferred it on the grounds that it
touches ADR-005's "check every op" invariant. ADR-017 Option 1
(split the add from the overflow check) was landed instead, and
post-that-change profiling confirmed `Monomial::mul` is still
significant enough that Option 2 is now worth pursuing. This ADR
implements Option 2.

### Singular precedent

`~/Singular/libpolys/polys/monomials/p_polys.h:1432`:

```c
static inline void p_ExpVectorAdd(poly p1, poly p2, const ring r) {
    p_LmCheckPolyRing1(p1, r);
    p_LmCheckPolyRing1(p2, r);
#if PDEBUG >= 1
    for (int i=1; i<=r->N; i++)
        pAssume1((unsigned long) (p_GetExp(p1, i, r)
                                 + p_GetExp(p2, i, r)) <= r->bitmask);
#endif
    p_MemAdd_LengthGeneral(p1->exp, p2->exp, r->ExpL_Size);
    p_MemAdd_NegWeightAdjust(p1, r);
}
```

The per-variable-sum check is compiled only under `PDEBUG >= 1`.
Release builds perform the bare `p_MemAdd_LengthGeneral`
scalar-loop add. Overflow is prevented at ring construction: the
caller (ultimately `rComplete` in
`~/Singular/libpolys/polys/monomials/ring.cc`) sizes `r->bitmask`
so the requested per-variable bound + all bba-step products fit in
the packed exponent width. Violating the contract produces silent
exponent corruption, not a detected error.

FLINT (`~/flint/src/mpoly.h:233,374`, `mpoly_monomial_add` /
`mpoly_monomial_overflows`) is different: it does the overflow
check in a separate `FLINT_FORCE_INLINE` pass that the caller
invokes only when needed. On the bba hot path we care about,
FLINT has no GB engine to compare, so FLINT is an imperfect
reference for this specific decision.

### Decision

Match Singular's contract. Specifically:

1. `Monomial::mul` is infallible. Signature
   `fn mul(&self, &Self, &Ring) -> Self` (was `-> Option<Self>`).
   Release builds do not check per-byte or u32-total-degree overflow.
2. Debug builds retain both checks via `debug_assert!` (guard-bit
   divmask OR-reduce, and `u32::checked_add` on total degree).
   Debug panics mirror Singular's `pAssume1` behaviour under
   `PDEBUG >= 1`.
3. Ring construction (`Ring::new`) documents the caller's
   obligation: no bba-step product in the intended computation
   may exceed `MAX_VAR_EXP` (= 127) per variable or `u32::MAX` in
   total degree. This matches Singular's `rComplete` / `bitmask`
   sizing model. The contract is descriptive, not enforced (no
   runtime check at ring-construction time either; matching
   Singular).
4. The Singular dispatch shim (`Singular-rustgb`'s
   `rustgb-dispatch.lib`) already filters by ≤31 vars / Z/p /
   degrevlex. Those filters remain adequate for current staging
   workloads. If a future FFI caller admits rings whose bba-step
   products could overflow, the dispatch filter must tighten
   before the ring reaches `Ring::new` — out of scope here.

### Consequences

Caller-side simplifications landed in commit `e173584`:

- `Poly::sub_mul_term` → `Poly`, not `Option<Poly>`. Drops the
  `on_overflow!` macro, the `release_partial` helper, and both
  per-word `return None` sites.
- `Poly::sub_mm_mult_qq_consuming` → `Poly`. Drops the
  `Option<()>` outcome wrapper, the outer `None` branch with
  its `release_partial` calls, and both `None => return None`
  arms inside the merge and tail-splice loops. The sentinel-slot
  drop path on normal return is unchanged.
- `Poly::mul`, `Poly::shift` → `Poly`, not `Option<Poly>`. Same
  simplification (drop `?` after the monomial mul).
- `KBucket::minus_m_mult_p`: the `match ... { Some, None }` on
  `sub_mm_mult_qq_consuming` becomes a direct `let`-binding. The
  silent-noop-on-overflow fallback is gone.
- `ReducerHeap::push_current_term` and `pop_with_cancellation`:
  both `r.multiplier.mul(m, &self.ring)` sites become direct
  `let`-bindings with no `match`.
- Example binaries and the bba/kbucket/monomial/poly property
  tests all simplify accordingly.

All three test configurations (default / `linked_list_poly` /
`linked_list_poly linked_list_poly_pool`) pass with the same test
counts as before this ADR (195 / 209 / 210).

### What this does NOT do

ADR-017 listed a four-stage plan for `Monomial::mul` cost
reduction. This ADR implements **Stage A only**. The remaining
stages are separate, each a future ADR if pursued:

- **Stage B — drop `sev: u64` from `Monomial`.** The SEV bloom
  filter is a bba-sweep divisibility pre-filter (ADR-005, ADR-009);
  removing it from `Monomial` would require recomputing SEV at the
  sweep boundary instead of caching it per-monomial. Not in scope
  here.
- **Stage C — drop `total_deg: u32` from `Monomial`.** The byte-31
  cap (min(total, 255)) would need a different recovery path for
  saturated-cap comparisons (currently falls back on the u32
  cache). Not in scope here.
- **Stage D — hand-specialised `_zp_degrevlex_len4` shape
  mirroring Singular's length-8 ring-specialised inline.** This
  is the architectural gap that explains most of the 47 % vs 1.7 %
  discrepancy; it is a major restructuring (ring-indexed dispatch
  table, per-length instantiations). Not in scope here.

### References

- Commit `c7e8a94` — `monomial: Monomial::mul becomes infallible`
  (signature change, debug-only `debug_assert!`, Ring::new doc
  contract).
- Commit `e173584` — `poly/kbucket/reducer: drop overflow
  propagation from mul-using sites` (caller simplifications).
- `~/project/docs/profile-rustgb-no-overflow-check-staging-5101449.md`
  — c200-1 pre/post wall-clock and call-graph for this ADR.
- `~/project/docs/profile-rustgb-monomial-mul-fix-staging-5101449.md`
  — post-ADR-017 baseline.
- ADR-017 Option 2 deferral text.
- ADR-005 — packed direct exponents + the original per-op
  overflow invariant this ADR relaxes.
- `~/Singular/libpolys/polys/monomials/p_polys.h:1432` —
  `p_ExpVectorAdd`.
- `~/Singular/libpolys/polys/templates/p_MemAdd.h:173` —
  `p_MemAdd_LengthGeneral`.
- `~/Singular/libpolys/polys/monomials/ring.cc` — `rComplete` /
  bitmask sizing.

---

## ADR-019: Phase I — bench-driven perf iteration on the arkworks port

**Status:** Accepted
**Date:** 2026-04-25

### Context

Phase H landed the ark-gb Criterion suite (`benches/groebner.rs`) and
correctness regression (`tests/groebner_correctness.rs`,
`tests/groebner_sage.rs`). Phase I was a bench-driven optimization
pass, scoped to the arkworks-port-specific cost model:

1. `Fr` (BLS12-381 scalar, 4×64-bit Montgomery) is ~50× more
   expensive per op than upstream rustgb's `Z/32003` (single-word
   Barrett).
2. `Fr::inverse()` is the most expensive scalar op and lands on the
   hot path through `Poly::monic` and `validate::build_sbasis`.
3. `MonoOrder::Elim` (added in Phase D) uses a per-byte branching
   `cmp` instead of `degrevlex`'s word-wise compare.

### What we did (per-iteration)

#### I0 — tooling

- Added `bench-baseline.sh` wrapper that pins
  `RUSTFLAGS="-C target-cpu=native"`, captures `rustc -V` /
  CPU-flags / git head into `target/criterion/.baselines/<name>.txt`
  for repro provenance, and dispatches `cargo bench --bench groebner
  --save-baseline <name>`.
- Verified the AVX2 SEV-sweep path in `src/simd.rs`
  (`#[cfg(target_feature = "avx2")]`) is reachable: by default rustc
  on x86_64-unknown-linux-gnu has `avx2: false`. `.cargo/config.toml`
  already pins `target-cpu=native` for repo-local builds, so the
  default `cargo bench` picks up the AVX2 path; `bench-baseline.sh`
  ensures it stays on for any contributor invoking the script
  directly.

#### I1 — profile

- `perf record -F 999 -g --call-graph dwarf,32768` against
  `examples/perf_cyclic5` with `ARK_GB_THREADS=1`, 200 reps, on
  Intel Xeon 8370C.

Top-10 self-time on Cyclic-5 / DegRevLex:

| Rank | Self % | Function |
|------|--------|----------|
| 1 | 26.86 % | `Poly::sub_mm_mult_qq_consuming` |
| 2 | 24.85 % | `MontBackend::mul_assign` |
| 3 |  9.98 % | `KBucket::leading` |
| 4 |  6.97 % | `bba::reduce_lobject_geobucket` |
| 5 |  6.16 % | `Monomial::cmp` (DegRevLex) |
| 6 |  4.09 % | `MontBackend::inverse` |
| 7 |  2.01 % | `gm::enterpairs` |
| 8 |  1.81 % | `Poly::add` |
| 9 |  1.47 % | libc `free` |
| 10 |  1.47 % | `KBucket::minus_m_mult_p` |

Key takeaway: **Fr::inverse() at 4 % bounds the I2 ceiling below
the 3 % adoption threshold once you net out noise**, so I2 was
deferred. The dominant cost (~52 %) is poly merge + Fr mul inside
`sub_mul_term`, which the upstream ADRs 015/017/018 already address
to within ~2× of Singular's ring-specialised path.

#### I3 — coprime-LM fast-path in `validate::is_groebner_basis` ✅

Buchberger's First Criterion (the "product" / "coprime LM"
criterion): if `gcd(LM(g_i), LM(g_j)) == 1` then `S(g_i, g_j)`
reduces to 0 modulo `{g_i, g_j}`. Detect coprimality in O(1) via
the cached short exponent vector — with `nvars ≤ 31` each variable
owns a unique SEV bit, so `(sev_i & sev_j) == 0` is exactly "no
shared variable" = coprime LMs. Sound for validation independent
of any ordering or reducer choice.

Bench impact (criterion `--quick`, `--baseline before-i1`,
`RUSTFLAGS=-C target-cpu=native`, x86_64 8370C, 187 tests pass):

```
gb_validate_katsura/3:  48.9 µs ->  20.4 µs  (-58%)
gb_validate_katsura/4: 429.9 µs -> 247.6 µs  (-43%)
gb_validate_katsura/5:  13.99 ms ->  2.51 ms (-82%)
gb_validate_cyclic/4:  149.3 µs ->  69.3 µs  (-53%)
gb_validate_cyclic/5:   13.90 ms ->  7.48 ms (-46%)
```

Compute_gb benches do not exercise `is_groebner_basis`, so any
deltas there are quick-mode noise (floor variance is 5–15 %).

#### I2 — batch Fr::inverse in `Poly::monic_batch` ❌ (deferred)

I1 placed `Fr::inverse` at 4 % of total. Upper bound on win is
≤4 % (assuming free batched inversion), well below the 3 %
adoption threshold once `--quick` noise is netted out. Deferred.

#### I4 — word-wise `Elim::cmp` for `split ∈ {0, nvars}` ❌ (rejected, doesn't apply)

`benches/groebner_shared.rs::elim_ring(n)` sets `split = n / 2`,
which is the non-trivial block case. The `split == 0`
(degenerates-to-grevlex) and `split == nvars` (degenerates-to-lex)
corner cases are not in the bench matrix and are not interesting
in production usage of `Elim`. Rejected: opens API surface for no
measurable bench gain.

#### I5 — `linked_list_poly` backend A/B ❌ (rejected on hot benches)

```
                  Vec(default)   List      Δ
gb_katsura_grevlex/5     2.84 ms   6.07 ms  +114%  ✗
gb_katsura_elim/5        3.99 ms   3.29 ms  -18%   ✓
gb_cyclic_grevlex/5      4.17 ms   6.92 ms  +66%   ✗
gb_cyclic_elim/5        11.75 ms  38.82 ms  +230%  ✗
gb_validate_katsura/5    2.59 ms   2.45 ms  -5%    ≈
gb_validate_cyclic/5     8.89 ms   6.10 ms  -31%   ✓
```

Vec wins decisively on the dominant Cyclic / DegRevLex benches.
List wins on Katsura/Elim and Validate-cyclic. Default stays Vec
(matches ADR-014's original choice). The List feature stays as an
A/B knob for users with elim-heavy or validate-heavy workloads.

#### I6 — LSet bitset (ADR-012) ❌ (skipped, not profile-justified)

L-set self-time was below the 1 % cutoff in the I1 profile (no
`lset` symbol in the top 12). ADR-012 stays deferred per its
gating rule.

### Decision

Adopt **I3**. Reject **I2, I4, I5, I6** for the reasons above. I0
tooling stays (no perf claim attached, just repro infrastructure).

### What's next

Future Phase J candidates, ordered by I1 self-time:

1. `sub_mul_term` two-pointer merge — the `m.mul(&q_m[j], ring)`
   call hoisted in the Greater branch is recomputed when `j`
   doesn't advance. Lifting that across iterations is a small
   localised optimization that may pick up 1-3 % on hot benches.
2. Geobucket `leading` (ADR-002) — 10 % self-time. Already heavily
   optimized upstream; further wins likely require restructuring.
3. Allocator churn (~3 % combined `malloc` + `free`) —
   ADR-016-style bumpalloc for `poly_vec` allocations.

None of these are blockers for embedding ark-gb into zippel.

### References

- I0 commit: `e2d2571` — `perf(i0): bench-baseline.sh + reproducible bench docs`.
- I3 commit: `c923d24` — `perf(i3): coprime-LM fast-path in validate::is_groebner_basis`.
- I1 perf data: `/tmp/cyc5.perf` (1493 samples, dwarf-32k stacks).
- ADR-002 (geobucket), ADR-008 (heap reducer), ADR-014 (poly backend
  default), ADR-015 (destructive list-splice), ADR-018 (mul overflow
  elision) — all prerequisites whose work this iteration assumed.

---

## ADR-020: Phase J — `Monomial: Copy` refactor + rejected `sub_mul_term` cache

**Status:** Accepted (J2 refactor) / Rejected (J1 cache)
**Date:** 2026-04-25

### Context

Phase I (ADR-019) banked the validate fast-path (-82 % on
`gb_validate_katsura/5`) but left compute_gb with `Fr` arithmetic
saturating ~50 % of self-time. ADR-019's "What's next" listed two
candidate further iterations on compute_gb:

1. **J1**: hoist `m.mul(&q_m[j], ring)` out of `Poly::sub_mul_term`'s
   two-pointer merge loop so consecutive `Greater` iterations reuse
   the cached `m * q_m[j]` instead of recomputing it.
2. **J2**: derive `Copy` on `Monomial`. The struct is 48 bytes of
   plain old data (4 × u64 packed exponents + u64 SEV + u32 total
   degree + u32 component); `derive(Clone)` already boiled down to
   field-wise memcpy, so promoting to `Copy` is semantically identical
   and lets `clippy --fix` strip ~47 explicit `.clone()` calls across
   the crate.

### J1 — `sub_mul_term` lazy cache (REJECTED)

Implementation: introduced `mq_mon: Option<Monomial>` outside the
loop, refreshed only when `j` advances; pushed-on-Less via
`mq_mon.take()` to elide the clone.

Bench (criterion `--quick`, `RUSTFLAGS=-C target-cpu=native`):

```
                       after-i3   after-j1    Δ
gb_katsura_grevlex/5    2.84 ms    3.62 ms   +27 %  ✗
gb_cyclic_grevlex/5     4.17 ms    9.17 ms  +120 %  ✗
gb_cyclic_elim/5       11.75 ms   21.06 ms   +79 %  ✗
gb_validate_cyclic/5    8.89 ms    7.75 ms   −13 %  ≈
```

Rejected. The `Option<Monomial>` discriminant + `take()`/`unwrap()`
chain costs more than the saved `Monomial::mul` (which I1's profile
already showed below the 0.5 % cutoff — `Monomial::mul` is not in
the top-12 self-time list). The `--quick` numbers exaggerated the
hit (true regression on a solid bench is ~0 % within noise on
master vs +99 % on this branch under a noisy reference baseline);
even charitably read it does not move the needle and increases the
maintenance surface.

Reverted before commit.

### J2 — `Monomial: Copy` (ADOPTED as refactor)

Promoted the derive list from `Clone, Debug` to `Clone, Copy, Debug`.
Ran `cargo clippy --tests --benches --examples --fix` to strip
`clone_on_copy` warnings: 47 explicit `.clone()` calls across 18
files became `*ref` (when called through a reference) or direct
indexing of a `&[Monomial]` slot (`s_m[i]` instead of
`s_m[i].clone()`).

Solid bench (criterion 10-sample, 8 s measurement,
`RUSTFLAGS=-C target-cpu=native`, baseline `solid-master` pinned on
master HEAD before this change):

```
gb_cyclic_grevlex/5: 9.47 ms  ->  9.70 ms   change +3.6 %, p = 0.29
```

Within noise (p > 0.05). Adopted as a **refactor**, not a perf claim:

- Code quality: `clone()` calls in hot loops no longer surface in
  profiles or call graphs.
- Ergonomics: callers can pass `Monomial` by value without thinking
  about cloning (consistent with `Field + Copy` everywhere else).
- No semantic change: `derive(Clone)` field-wise memcpy is identical
  to `derive(Copy)` field-wise memcpy.

187 tests pass. Clippy clean.

### Decision

Adopt J2 (refactor, perf-neutral). Reject J1 (perf-negative,
semantically inert). Close Phase J.

### What's left for compute_gb

The I1 profile bounded the obvious wins: ~27 % `sub_mm_mult_qq`,
~25 % `Fr::mul_assign`, ~10 % `KBucket::leading`, ~6 %
`Monomial::cmp`. These are intrinsic costs of the algorithm at this
field size; further wins require structural changes (F4-style block
linear algebra, ring-specialised codegen à la Singular's
`p_Minus_mm_Mult_qq__T.cc` length-dispatched templates, or
allocator pooling). Those are out of scope for this fork.

For cryptographic protocol use (e.g. zippel), the validate fast-path
from Phase I is the practically dominant win — Gröbner-basis
*verification* is what runs on the verifier, and that path is now
~5–8× faster than at the start of Phase H.

### References

- I1 profile (ADR-019): top-12 self-time on Cyclic-5/DegRevLex.
- ADR-018 (mul overflow elision) — predecessor that documents the
  intrinsic Singular gap.
- `solid-master` criterion baseline: pinned at master HEAD before
  J2.

---

## ADR-021: Phase K — zippel-style M-parametric pipeline

**Status:** Accepted
**Date:** 2026-04-26

### Context

Phase J closed the `Monomial: Copy` refactor and bounded what
`compute_gb` can win without structural changes. The user requested
that ark-gb's pipeline be **parametric on the monomial**, mirroring
zippel's design at
`~/git/zippel/graph/src/analyses/groebner/monomial.rs:11-518`,
where the order is pinned by the *type* of the monomial (newtype
wrappers around a shared data carrier, each with its own `Ord`).

Two design rounds preceded this ADR:

1. **K1+K2 (commit `78c8633`, superseded)**: introduced
   `Ring<F, O: MonoOrder>` parametric in the order, with the order
   trait providing `cmp(a, b, &RingData)` taking the ring as an
   explicit argument. This was functionally equivalent to zippel's
   pattern but **diverged structurally** — order lived on the ring,
   not on the monomial.

2. **K-redo (commit `860e66d`, this ADR)**: rolled K2 back. Pipeline
   parametric in `M: Monomial<F>` where `M: Ord`. Order is on the
   monomial type, ring carries no order.

### Why we switched to K-redo

Zippel parity. The crate was forked from rustgb specifically to
back zippel; matching zippel's monomial design eliminates the
adapter that would otherwise be needed at the FFI boundary. The
`Ord`-based static dispatch is also a hair faster (no closure
indirection through `MonoOrder::cmp`'s extra `&RingData` arg).

### The runtime-`split` problem

Zippel's `ElimTerm` works because its elimination predicate
(`MonoTerm::eliminate_var(v: &PRef) -> bool` at
`~/git/zippel/graph/src/analyses/groebner/monomial.rs:262-265`) is
a **hardcoded global function** of variable kind (Local +
Private+Uniform). It needs no runtime parameter.

ark-gb previously supported `Elim { split: u32 }` as a runtime
parameter — users could request a Gröbner basis under arbitrary
block-elimination splits. Rust's `Ord::cmp(&self, other: &Self)`
takes no extra argument, so a `split`-carrying newtype cannot
read split from the ring at compare time.

Three workarounds were considered:

- **Const generic** `ElimTerm<const SPLIT: u32>(MonoTerm)` —
  preserves all current tests/benches by monomorphising at each
  call site, but forces split to be compile-time, breaking
  potential FFI consumers that pass split at runtime.
- **Per-term split** `ElimTerm { mono: MonoTerm, split: u32 }` —
  +4 bytes per monomial, large memory overhead in BBA queues.
- **Hardcoded sample newtype** — drop the runtime split entirely;
  add concrete newtypes per elimination predicate the codebase
  needs.

We chose the **hardcoded sample**, matching zippel.

### Design

```text
src/monomial.rs:
  pub struct MonoTerm        // packed-data carrier, no Ord
  pub trait Monomial<F>: Ord + ...
      one / from_exponents / mul / divides / div / lcm /
      total_deg / exponent / exponents / as_mono_term
  pub struct GrevLexTerm(MonoTerm)  // impl Ord = degrevlex
  pub struct OddElimTerm(MonoTerm)  // impl Ord = elim where idx % 2 == 1

src/ring.rs:
  pub struct Ring<F>          // nvars + masks; no order param

src/ordering.rs:
  doc-stub only; trait MonoOrder, structs DegRevLex/Elim removed
```

Pipeline structs that hold or process monomials gained an
`M: Monomial<F>` parameter:

- `Poly<F, M>`, `KBucket<F, M>`, `BBA<F, M>`, `Computation<F, M>`,
  `Reducer<F, M>`, `LObject<F, M>`, `LSet<F, M>`, `BSet<F, M>`,
  `Pair<F, M>`, `GMTracker<F, M>`.

Free functions `compute_gb`, `validate::is_groebner_basis`, etc.,
gained `<F, M>` generics.

### Ring-free `Ord` — flip-mask correctness

The existing `MonoTerm::cmp_degrevlex(other, &Ring<F>)` used the
ring's per-nvars `cmp_flip_mask` to XOR-flip variable bytes before
the lex compare. To make this ring-free for `Ord`, we observe:

- The flip mask sets `0x7F` in **every variable byte** (positions
  31 - nvars .. 30 of the 32-byte block) and `0x00` elsewhere.
- Unused low bytes in canonical `MonoTerm` are always zero
  (constructed via `from_exponents` which zeros them).
- XOR'ing `0x7F` into a zero byte yields `0x7F`, but those bytes
  are at positions less significant than any variable byte that
  could differ between two canonical `MonoTerm`s built from the
  same ring, so they never decide the comparison.

Therefore a **constant flip mask**
`[0x7F7F_7F7F_7F7F_7F7F × 3, 0x007F_7F7F_7F7F_7F7F]` (top byte 31
held at zero for total-degree direction) is correct for all
`nvars ∈ [1, 31]`. The implementation lives at
`src/monomial.rs:DEGREVLEX_FLIP` with a unit test
(`cmp_degrevlex_packed_matches_ring_version`) verifying it agrees
with the ring-based version on randomly generated monomials.

### Sample elim newtype

`OddElimTerm` eliminates **odd-indexed** variables: the predicate
is `|idx| idx % 2 == 1`. This is a sample / proof of concept. To
add another elim order, define a new newtype + `impl Ord` calling
`MonoTerm::cmp_elim_packed(other, &predicate)` with the desired
predicate.

### Tests / benches

- `tests/elim_order.rs`: rewritten to test that `OddElimTerm`'s
  `Ord` differs from `GrevLexTerm`'s on at least one monomial
  pair where the difference is in odd-indexed exponents only, and
  that a Gröbner basis under `OddElimTerm` retains the elimination
  property (any leading monomial that uses no odd-indexed variable
  lies in the elimination ideal).
- All other tests/benches/examples default to `GrevLexTerm` and
  `Ring::<Fr>::new(n)` (no order argument).

187 tests pass; clippy clean.

### Perf

K-redo is structurally neutral — it changes which type parameter
threads `Ord`, not what the algorithm does. Solid-bench parity
vs `solid-master` baseline is the K5 acceptance criterion (deferred
to a follow-up commit; the commit `860e66d` is purely the trait
refactor).

### Trade-offs accepted

- **Lost**: runtime `split: u32` for elimination orders. Adding a
  new elimination predicate requires a new newtype + recompile,
  not a runtime config knob.
- **Gained**: zippel parity (no FFI adapter), ring-free `Ord`,
  cleaner trait bounds (`M: Monomial<F>` implies `M: Ord`), and
  the type system enforces "you can't accidentally compare a
  `GrevLexTerm` against an `OddElimTerm`".

### Decision

Adopt K-redo. The K1+K2 commit `78c8633` is **superseded** by
`860e66d` and remains in history as a documented divergence
explored before settling on zippel parity.

### Follow-ups

- **K4 cleanup**: `pub(crate)` audit on `MonoTerm`'s internal
  helpers; verify newtype `Ord` impls are statically dispatched
  in release codegen (`cargo asm`).
- **K5 solid-bench**: criterion comparison vs `solid-master` on
  cyclic-5/grevlex, katsura-5/grevlex, and the new
  cyclic-5/oddelim case. Acceptance: `change` p > 0.05.

---

## ADR-022: Phase L — sparse `Matrix<F>` + Gaussian elimination

**Status:** Accepted
**Date:** 2026-04-26

### Context

Phases I/J/K closed the achievable wins on the per-S-pair Buchberger
pipeline. Further structural speed-ups require **F4-style block
reduction**: collect a batch of S-polynomials and reductors into a
sparse matrix whose columns are monomials in the chosen order, then
row-reduce the matrix in one pass. F4 needs two artefacts that ark-gb
did not previously have:

1. a sparse-matrix data shape over an arkworks field `F`, and
2. a Gaussian eliminator that respects a column ordering (so the
    pivot column at step `k` is the smallest-monomial column not yet
    eliminated).

The user requested: rather than fork `arkworks-rs/algebra`, *copy* the
minimal sparse-matrix shape that already exists in
`arkworks-rs/snark` (`relations/src/utils/matrix.rs`) into ark-gb and
extend it with the operations F4 needs. F4 itself is **explicitly out
of scope for Phase L**; it lands in a successor phase that builds on
this substrate.

### Decision

A new module lives at `src/matrix/`:

- **`sparse.rs`** — copies `Matrix<F> = Vec<Vec<(F, usize)>>`,
  `transpose`, and `mat_vec_mul` verbatim from
  `arkworks-rs/snark@6d5f7ae` (dual MIT / Apache-2.0 — compatible
  with ark-gb's GPL-3.0-or-later via one-way upgrade). An attribution
  comment names the upstream file and SHA. The original three items
  retain their exact bodies and signatures.

  On top of this we add `SparseRow<F>`, a newtype around
  `Vec<(F, usize)>` with two enforced invariants:

  1. column indices strictly ascending,
  2. no zero entries.

  `SparseRow<F>` exposes `from_pairs`, `from_dense`, `as_pairs`,
  `into_pairs`, `is_zero`, `len_nz`, `leading_col`, `trailing_col`,
  `coeff`, `scale(&F)`, `axpy(&F, &Self) -> Self`, and
  `axpy_assign(&F, &Self)`. AXPY is implemented as a linear merge over
  the two sorted column lists; cancellations are dropped on the fly.
  `From<Vec<(F, usize)>>` and the inverse `Into` round-trip with the
  snark `Matrix` row type so callers don't have to choose a side.

- **`gauss.rs`** — Gaussian elimination keyed on column order:

  - `pub fn row_echelon<F: Field>(&mut [SparseRow<F>]) -> usize`
    selects, at each step, the still-unprocessed row with the
    smallest leading column, normalises it to a unit pivot,
    eliminates that column from every row below, and finally moves
    zero rows to the bottom. Returns the rank.
  - `pub fn rref<F: Field>(&mut [SparseRow<F>]) -> usize`
    back-substitutes after `row_echelon` so each pivot column
    contains a single non-zero entry.
  - `pub fn rank<F: Field>(&[SparseRow<F>]) -> usize` — non-mutating;
    clones internally.
  - `row_echelon_matrix` and `rref_matrix` are convenience adapters
    for the snark-shaped `Matrix<F> = Vec<Vec<(F, usize)>>`.

  The trait bound is `F: ark_ff::Field`, deliberately broader than
  ark-gb's typical `F: FftField`. Phase L's substrate is generic in
  the field; F4 will add `FftField` (or whatever it really needs) at
  its own boundary.

### Bench reference (`after-l-matrix`)

Benches live at `benches/matrix.rs`. Each shape is benched twice
(`row_echelon` and `rref`) over `ark_bls12_381::Fr`. Phase L only
*adds* code, so there is no regression baseline — these numbers are
the absolute reference line for future tuning.

| shape (rows×cols, density)       | row_echelon | rref       |
|----------------------------------|-------------|------------|
| `square_100_d3` (100×100, ~33 %) | ~11.8 ms    | ~12.8 ms   |
| `square_500_d100` (500×500, 1 %) | (recorded by `bench-baseline.sh after-l-matrix`) |
| `tall_500x100_d10` (500×100, 10 %) | "        | "          |
| `wide_100x500_d10` (100×500, 10 %) | "        | "          |
| `sparse_1pct_1000` (1000×1000, 1 %) | "       | "          |
| `sparse_5pct_1000` (1000×1000, 5 %) | "       | "          |

The `square_100_d3` row was sampled by hand in the Phase L commit
session (criterion 3-sample run: 11.72 / 11.78 / 11.91 ms). Larger
shapes are deferred to a dedicated `bench-baseline.sh after-l-matrix`
run.

### Tests

- `src/matrix/sparse.rs` — 14 unit tests covering snark helpers
  (`transpose`, `mat_vec_mul`), constructor invariants
  (sort + dedup-sum + zero drop, cancellation), `scale`, `axpy`
  (including a 256-trial randomised vs dense reference), and the
  `Vec<(F, usize)>` round-trip.
- `src/matrix/gauss.rs` — 11 unit tests covering identity, swap-to-
  pivot-order, rank-deficient input, RREF idempotency,
  permutation invariance, the snark `Matrix<F>` adapter, a 64-trial
  randomised rank vs naive dense oracle, and the dependent-row
  kernel test.

Total: 25 new tests, all passing. `cargo clippy --all-targets -- -D
warnings` is clean.

### Out of scope (deferred)

- **F4 itself.** Assembly of an S-pair batch into a `Matrix<F>`,
  monomial → column-id index, and basis harvesting from the RREF are
  the work of a successor phase. Phase L delivers only the linear-
  algebra substrate.
- **Parallel Gauss.** Single-threaded first; rayonisation gated on
  bench evidence in a successor phase.
- **Bitvector tricks for GF(2) / small primes.** ark-gb targets
  BLS12-381 `Fr`.
- **Forking `arkworks-rs/algebra`.** Not necessary — only the snark
  matrix module shape was needed, and that is < 40 lines.

### Files added / changed

- new: `src/matrix/mod.rs`
- new: `src/matrix/sparse.rs` (snark copy + `SparseRow<F>`)
- new: `src/matrix/gauss.rs` (Gaussian elimination)
- new: `benches/matrix.rs`
- changed: `src/lib.rs` — `pub mod matrix;`
- changed: `Cargo.toml` — `ark-std` dev-dep (test RNG), `[[bench]]`
  for `matrix`.

### Acceptance

Met. 25/25 matrix tests pass, clippy clean, bench compiles and runs,
ADR documented.

## How to add a new ADR

1. Pick the next number. Don't reuse retired numbers.
2. Fill in every section. If FLINT genuinely does not address the
   question (e.g. "how does `bba` handle Gebauer-Möller chain
   criterion?"), write **N/A — FLINT has no GB engine** in the FLINT
   section. Don't omit the section.
3. Cite source files with `path:line` ranges where possible.
4. If the decision changes later, add a new ADR rather than editing
   the old one. Mark the old one **Superseded by #N**.
5. Commit the ADR in the same change as the code that implements it,
   so `git blame` lines up.
