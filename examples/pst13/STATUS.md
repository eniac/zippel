# PST13 Implementation Status

## What works

- **`pst13_commit`** — generic over M (`M: 1..10`), just `dot(p, ck_N)`, no recursion needed. Compiles and runs.
- **`proto pst13`** (N=2, inline rounds) — two rounds inlined directly in the proto body. Compiles and verifies correctly.
- **`pst13_ck`** (recursive setup helper) — correct generic code, compiles in isolation.

## Blocked by a Zippel compiler bug

The compiler stack-overflows on recursive functions whose arguments have **mixed size expressions** — specifically when one parameter has size `2^K` and another has size `K` in the same function signature. For example:

```
fn pst13_open_rounds<..., K: 2..10>(
    private p_curr:      [F;  2^K],  // size 2^K
    public  ck_curr:     [G1; 2^K],  // size 2^K
    public  z_curr:      [F;  K],    // size K  ← mixed
    public  alpha_H_curr:[G2; K],    // size K  ← mixed
    ...
)
```

The same bug affects the existing IPA and Hyrax IPA examples, which also overflow.

## Current workaround

The `proto pst13` inlines the N=2 open rounds directly:

```
// Round 1
let ck_1  = ck_N[0..2] + ck_N[2..4];
...
pi1 <- dot(q1, ck_1);
...
// Round 2
let ck_0  = ck_1[0..1] + ck_1[1..2];
...
pi2 <- dot(q2, ck_0);

verify(pair(C_p - (G * y), H) == pair(pi1, alpha_H[0] - (H * z[0]))
                               + pair(pi2, alpha_H[1] - (H * z[1])))
```

To use a different N, change `N: 2` in the proto and extend the rounds manually until the compiler bug is fixed.

## Intended generic design (blocked)

Once the mixed-size recursive dispatch is fixed, the protocol should use:

- **`pst13_setup`** — generic over N via recursive `pst13_ck` helper:
  - Base case: `alpha: [F; 1]` → `[G1; 2]`
  - Recursive case N: `alpha: [F; N]` → `[G1; 2^N]` using `(prev * (1-a)) ++ (prev * a)`
- **`pst13_open_rounds`** — recursive, returns `Bool`, threads `rem: GT`:
  - Base case: `p: [F; 2], ck: [G1; 2], z: [F; 1], alpha_H: [G2; 1]`
  - Recursive case K: `p: [F; 2^K], ck: [G1; 2^K], z: [F; K], alpha_H: [G2; K]`
  - Each round subtracts its pairing contribution from `rem`; base case checks `rem == pair(pi_last, ...)`
- **`proto pst13`** — generic `N: 1..10`, calls `pst13_open_rounds` with `lhs = pair(C_p - y*G, H)`
