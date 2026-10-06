**Branch audit: `soundness-split` — 2026-10-02**

**Verdict: do not merge this branch as a trusted soundness analyzer yet.** The branch makes useful correctness and performance improvements, but its new symbolic group modes can certify an invalid protocol. Two further changes reject valid protocols. The default soundness path also retains an existing false-positive bug for vector responses. Passing the existing test suite does not establish the safety of the analysis results.

This assessment concerns the compiler's static analysis guarantees. I found no new runtime execution vulnerability in the reviewed changes; the execution engine and concrete cryptographic backend are unchanged. This is a source audit with targeted counterexamples, not a proof of the analyzer or of every example protocol.

**Scope and reference point.** Reviewed HEAD `06f393e8029afa7d729c190e106dd4b394a2f13c` against merge base/local `main` `94db2f3e619527337a74350090089b8e28d0300a`: 18 commits, 59 changed files, 4,206 insertions and 1,270 deletions. The working tree was initially clean. Remote refs were not refreshed. The supplied `~/Research/zippel/paper.pdf` path did not exist; I used `~/Research/zippel/main.pdf`, particularly §7.3–7.4 and Appendix D, to check the intended completeness and extractor-validation construction.

**What the branch contains**

| Area | Changes and implications |
| --- | --- |
| Completeness | Substitutes inputs defined by constraints, splits asserted Boolean reductions, records verifier checks and generator origins, and explains reductions. Substitution uses a constant nonzero coefficient and excludes self-dependence, which is the appropriate algebraic restriction. Runtime body assertions are explicitly excluded. |
| Soundness | Separates relation goals from validity assumptions, rejects unit validity ideals, substitutes values forced by accepting transcripts, supports chained extraction, and splits Boolean reductions. Removing the old assumption of the relation itself is an important correction to the paper's validity check. |
| New proof models | Adds `Plain`, `SymbolicGroup`, and `SymbolicGroupResponses`. Symbolic modes introduce per-generator scalar representations and conditional binding assumptions. The responses variant includes honest prover equations in candidate search; validity is constructed separately from verifier copies. The public handler still selects `Plain`. |
| Examples | Dory adds verifier-key derivation constraints and changes proving-key generators from `witness` to `extra`. ProductCheck adds the honest product-tree constraints. Permutation replaces the expanded product equality with its tree-root equality. |
| Diagnostics and benchmarks | Adds ideal dumps, explanations, custom source/size inputs, and a build-only benchmark mode. The KZH inline benchmark changes from `NX=1` to `NX=2`. |
| Language and formatter | Recognizes `Bool` as a built-in type and consumes its token correctly while formatting. This also makes `Bool` a reserved token. |
| Tests | Adds/updates completeness explanations and bases, enables Dory and ProductCheck completeness at `S=3`, and enables symbolic soundness cases for Okamoto, coin proof, and R1CS Sigma. |

The example relation edits deserve semantic review separately from optimizer review: Dory and ProductCheck now require additional input/witness consistency conditions. The added equations match the existing harness constructions on inspection. The permutation root equality follows from the retained leaf/tree equations and nonzero denominator constraints. These are bounded analysis results; the tests do not establish correctness at all sizes. HyperPlonk permutation's completeness snapshot remains ignored.

The lower-level Rust API also changes: `SoundnessInputs::grev_rel_result` is replaced by `rel_goals`, and several public structs acquire fields. Downstream callers using those fields or struct literals will require changes.

**Confirmed new findings**

**1. High / P1 — An empty generator basis erases group obligations and produces a false soundness result.**

Locations: [symbolic_group.rs](../../../analyses/src/symbolic_group.rs), lines 160–175, 217–225, 265–275 and 310–336.

`detect` can demote every group argument. `build_reps` then assigns those arguments empty coefficient vectors. `transform_poly` interprets those representations as zero and emits no equation for a group goal. Neither phase rejects the missing basis. This affects both new symbolic modes.

Reproducer:

```zippel
proto bad<G: Group, F: Scalar<G>>(
    witness x: F, instance g: G, instance h: G, instance y: F,
) where g == h && h == g * x && x == y {
    t <- g;
    c <- challenge<F>;
    z <- x + c - c;
    verify(z == y)
}
```

For public `g = h != 0` and `y = 0`, a prover sends `z = 0` and obtains acceptance for arbitrary distinct challenges, but no witness satisfies the relation: `x = 0` would require `h = 0`. `Plain` rejects this protocol. Both `SymbolicGroup` and `SymbolicGroupResponses` return `Ok(())`, report `binding w.r.t. {}`, and reduce the three relation goals to just the scalar goal. This was reproduced with both ark-gb and Singular.

Required correction: reject unsupported/missing bases for each represented group before transforming any equation, or retain a representation that faithfully preserves arbitrary group inputs. An empty representation must never silently mean an arbitrary input is the identity. Add this negative test for both models and for a missing basis in only one of several groups.

**2. Medium / P2 — Relation-local Boolean semantics are omitted from validity.**

Locations: [soundness.rs](../../../analyses/src/soundness.rs), lines 553–558, 634–640 and 934–945; [bool.rs](../../../analyses/src/ideal/ops/bool.rs), `equ_leaf`.

The new check assumes inlining resolves relation intermediates down to arguments. Equality-result Booleans are instead defined by generators, not entries in `pl`. Their defining generators never enter validity. With inlining disabled, only `pl` definitions are added, so that path fails too.

This valid protocol is rejected in both modes of inlining:

```zippel
proto valid<F: Field>(witness x: F, instance y: F)
where (x == y) == (y == y) {
    t <- x;
    c <- challenge<F>;
    z <- x + c;
    verify(t == y && z == y + c)
}
```

The extractor can simply return `y`. HEAD instead reports `ExtractorInvalid` with a difference of two unconstrained relation Boolean nodes. Both backends reproduce this. The adapted probe succeeds on the base branch with and without inlining.

Required correction: distinguish local semantic constraints from relation assertions, preserving the former in the validity construction or proving equivalent goals that eliminate their auxiliary variables. Do not restore the old merge of the entire asserted relation, which would restore circular validation. Audit division and other operators whose semantics also live outside `pl`.

**3. Medium / P2 — Constant substitution removes witnesses before extractor search.**

Locations: [symbolic_group.rs](../../../analyses/src/symbolic_group.rs), lines 117–134; call at [soundness.rs](../../../analyses/src/soundness.rs), line 676.

`pin_self_constants` is intended to collapse asserted Boolean sentinels, but it accepts any nongroup variable pinned to a constant, including a witness. It substitutes that witness out of every search polynomial without retaining its defining equation or recording a constant extractor. `run` still requires an extractor for the removed witness.

The group-free protocol below succeeds in `Plain`, but selecting `SymbolicGroup` produces `No valid extractor for witness x: NoExtractor`, with no additional group assumption involved:

```zippel
proto valid<F: Field>(witness x: F) where x == 0 {
    t <- x;
    c <- challenge<F>;
    z <- x + c;
    verify(t == 0 && z == c)
}
```

The correct extractor is the constant zero. Both backends reproduce the rejection. Protect witness variables as `pin_eligible` already does elsewhere, or carry eliminated witness definitions into candidate extraction and validate them normally.

**Existing safety problems still present on this branch**

These are reproducible at both HEAD and the base commit; they are not newly introduced defects.

| Problem | Evidence and consequence |
| --- | --- |
| High: vector responses shared across rewound transcripts | The new whole-vector renaming fallback at `soundness.rs:421` is gated on `uses_prover_responses()`. `Plain` still shares `z` for a response `z <- [r + x*c]`. For the relation `h == g*x && h == (g-g)`, ordinary Schnorr verification `g*z[0] == t + h*c` incorrectly passes soundness even though it never enforces `h == 0`. Sharing `z` across distinct challenges artificially forces `h == 0` in the model. The branch's partial fix should apply to all appropriate models. |
| High for completeness claims: prover aborts can be ignored | `where x == 0 { assert(x == 1); t <- x; verify(t == 0) }` returns completeness success although the honest prover aborts. The probe also reports `body_asserts = 0`, because the assertion is absent from the traversed closures. The new explicit omission rule does not repair that coverage gap. Either prove reachable runtime assertions or state and enforce a narrower guarantee. |

The paper requires copy-specific second messages and successful honest execution. These examples limit the reliability of an unqualified `Ok(())` even when the new symbolic modes are unused.

**Validation and reproducibility**

| Check | Result |
| --- | --- |
| `cargo test -p analyses --lib` | 333 passed, 2 ignored. |
| `cargo test --workspace` | Exit 0; 1,808 passed, 55 ignored across unit, integration and doc-test groups. |
| Gröbner-basis snapshot binary within workspace tests | 37 passed, 47 ignored; Singular was installed and used. Dory and ProductCheck at `S=3`, and the newly enabled soundness examples, passed. |
| `cargo fmt --all -- --check` | Passed on the branch before audit artifacts. |
| `cargo clippy --workspace --all-targets` | Passed; two warnings in unchanged `benchmarks/src/dekart_upstream/mod.rs` (type complexity and `ck_S` naming). |
| `cargo zfmt --check examples/*/*.zippel` | Passed. |
| Windows reserved filenames | Equivalent Python scan passed. The repository shell script could not run under macOS's old system Bash because it uses `${component,,}`. |
| Targeted audit probes | One positive control passed; five safety/correctness assertions failed as described above. Soundness failures reproduced with both ark-gb and Singular. |
| Base comparison | An archived copy of `94db2f3` passed the Boolean relation probe and reproduced the vector-response and prover-assertion false positives. |

The full workspace run covered the branch's existing tests, before the temporary audit target was added. The initial sandboxed workspace attempt could not unpack a missing Cargo dependency; the approved rerun completed successfully. No ignored tests were forced, no exhaustive size exploration was performed, and the full example drivers were not run separately. No performance speedup figures were independently measured.

The audit test source is preserved as [reproductions.rs](reproductions.rs), outside Cargo's normal test discovery. Its assertions express the behavior a correct analyzer should have. To reproduce from the repository root:

```sh
cp docs/audits/soundness-split/reproductions.rs analyses/tests/branch_audit.rs
cargo test -p analyses --test branch_audit -- --nocapture
ZIPPEL_AUDIT_SINGULAR=1 cargo test -p analyses --test branch_audit -- --nocapture
```

The five failures are expected at the audited revision. Remove the copied temporary test target after use. The environment variable switches the soundness probes to Singular; completeness probes continue using ark-gb. Recorded outputs: [ark-gb](reproductions-ark-gb.log), [Singular](reproductions-singular.log), and [adapted base-branch probes](baseline.log).

Before trusting the branch's results, fix finding 1 and the vector-copy problem, preserve relation-local semantics without assuming relation assertions, and retain constant witnesses for extraction. Add these counterexamples to the permanent suite. Symbolic successes should also expose and test their exact assumptions; the current protocol soundness snapshots record the search basis but not the assumption label.

Only this report and its evidence files were left in the working tree. No implementation changes or commits were made.
