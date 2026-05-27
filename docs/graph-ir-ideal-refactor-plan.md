# Plan: Refactor Graph IR-to-Ideal Encoding and Analysis APIs

  ## Summary

  Implement the refactor in dependency order, starting with TransClos as requested. The
  goal is to make full-DAG closures the source of truth, then introduce a shared Groebner
  namespace, then fix logical vs physical indexing, and finally tighten encoding
  coverage.

  ## Implementation Steps

  1. Refactor TransClos first
      - Rename TransClos::args to prefs.
      - Keep from_input temporarily as a compatibility wrapper, but add clearer
        constructors:
          - TransClos::input(dag)
          - TransClos::relation(dag)
          - TransClos::prover(dag)
          - TransClos::verifier(dag)
      - Implement extractors against the full annotated DAG rather than projected DAGs
        where possible.
      - Add TransClos::remap(&Fn(&PRef) -> PRef) that remaps both prefs and clos PRefs.
      - Update current call sites to use prefs and the new constructors.
      - Remove StaticAnalysis only after confirming no remaining users.
  2. Introduce GroebnerNamespace without changing encoding behavior
      - Add a namespace struct owning:
          - prefs
          - pl
          - np
          - ref_aliases
          - div_wit
          - sentinel counter/allocation state
      - Move GroebnerBuilder fields into the namespace, leaving builder responsible for
        basis.
      - Update find_ref, vars, merge, remap_vars, and add_tc to operate through the
        namespace.
      - Keep existing behavior and tests passing before changing indexing semantics.
  3. Centralize sentinel allocation
      - Replace hard-coded offsets for __g1__, __g2__, __gt__, __div_q_*__, and
        __div_r_*__.
      - Add namespace APIs:
          - sentinel(name, typ) -> PRef
          - g1_pref(), g2_pref(), gt_pref()
          - div_witnesses(a, b)
      - Use reserved synthetic names such as __zippel::gb::gt and
        __zippel::gb::div_q::<n>.
      - Ensure multiple builders sharing one namespace cannot mint colliding sentinels.
  4. Add type-layout APIs
      - Add ATyp::logical_len().
      - Add ATyp::logical_slot_type(i).
      - Add ATyp::logical_slot_offset(i).
      - Add ATyp::physical_slot_type(i).
      - Define physical_slot_type(i) as: “the leaf type stored at flattened physical slot
        offset i.”
        Example: [ [F; 2]; 2 ] has logical length 2, physical size 4, and every physical
        slot has type F.
      - Use ATyp::size() as the physical slot count.
  5. Split PRef indexing APIs
      - Change PRef::with_index(i) to logical indexing using logical_slot_offset and
        logical_slot_type.
      - Add PRef::with_slot(i) for flattened physical slots using physical_slot_type.
      - Add PRef::slots() returning all flattened slot-level PRefs.
      - Audit all call sites:
          - IR indexing and literal RAM use with_index.
          - Groebner coefficient rows, witness links, to_poly(Op::Ref), and vector
            flattening use with_slot/slots.
  6. Replace Groebner-local slot counting
      - Remove or deprecate num_coeffs.
      - Replace slot counts with typ.size() for physical encoding.
      - Keep polynomial enumeration helpers like multi_indices and hypercube; only remove
        duplicated count logic.
      - Update tests currently asserting num_coeffs to assert ATyp::size() instead.
  7. Fix to_poly around nested operations
      - Make to_poly(Op::Ref) return physical slot variables via find_ref(...).slots().
      - Ensure nested Div/Rem returns witness slot variables, so (b / c) / d composes.
      - Make unsupported nested operations explicit opaque/failure cases rather than
        returning silent empty vectors.
      - Add regression tests for nested division and nested vector expressions.
  8. Make add_op exhaustive and explicit
      - Replace the final wildcard op => np.insert(...) with explicit arms for every Op
        variant.
      - For each unsupported variant, insert into np deliberately with a short comment
        explaining why it is opaque.
      - Explicitly handle or mark opaque:
          - Concat
          - Pow
          - Marginalize
          - Proj
          - Record
          - Interpolate
          - Random
          - Challenge
      - The compiler should force review when new Op variants are added.
  9. Update analyses to use full-DAG closures and shared namespace
      - Refactor completeness analysis to avoid projected-DAG remap glue where
        TransClos::prover can extract directly from the full DAG.
      - Refactor knowledge setup to pass a shared GroebnerNamespace to
        related builders.
      - Remove external sentinel offsets and duplicated arg-registration logic.
      - Keep register_input_args only if still useful as a compatibility wrapper;
        otherwise remove it.
  10. Documentation and cleanup

  - Write this plan to docs/graph-ir-ideal-refactor-plan.md.
  - Extend docs/poly-encoding.md with the logical-vs-physical indexing invariant.
  - Remove dead typ.inner_type code if still present.
  - Remove unused StaticAnalysis.
  - Replace inefficient num_coeffs references with ATyp::size().

  ## Test Plan

  - Run focused unit tests after each stage:
      - cargo test -p graph trans_clos
      - cargo test -p graph groebner
      - cargo test -p backend typ
  - Add layout tests for:
      - scalar, polynomial, vector, nested vector, and record physical slots.
      - PRef::with_index vs PRef::with_slot.
  - Add Groebner regressions for:
      - nested vector addition.
      - literal RAM into nested vectors.
      - (b / c) / d.
      - shared div/rem witnesses.
  - Add analysis regressions for:
      - completeness with relation/prover/verifier in one namespace.
      - multiple builders sharing sentinels without collisions.

  ## Assumptions

  - Step 1 changes TransClos before touching Groebner internals.
  - Existing local commits d712420 and 110ddda are reference material only.
  - ATyp::size() is the canonical physical slot count.
  - PRef::with_index becomes logical indexing; all flattened encoding code must move to
    with_slot or slots.