//! SIMD helpers shared across the crate.
//!
//! Currently a single primitive: [`find_sev_match`], the
//! batched sev pre-filter scan introduced in ADR-007 for the
//! basis sweep inside `bba::reduce_lobject` and reused in ADR-009
//! for `gm::chain_crit_normal`'s B-internal pair dedup. The
//! function takes a flat `&[u64]` of sevs and a "not_sev" mask
//! (the negation of the candidate sev), returning the first index
//! where `(sevs[i] & not_sev) == 0` — i.e. the candidate's set
//! bits are a subset of `sevs[i]`'s. That's exactly what both
//! "candidate divides current" (ADR-007) and "outer-pair sev fits
//! inside inner-pair sev" (ADR-009) need.
//!
//! Mirrors Singular's `kSevScanAVX2` from
//! `~/Singular-next-opt/kernel/GBEngine/kstd2.cc:74-121`.
//!
//! AVX2 path: 16-entry-per-iteration unrolled main loop (4 batches
//! of 4-wide loads, AND + CMPEQ_EPI64 + MOVEMASK), 4-wide tail,
//! scalar tail. Compiled in only when `target_feature = "avx2"` is
//! enabled (typically via `RUSTFLAGS="-C target-cpu=native"` on
//! AVX2-capable hosts).
//!
//! Scalar fallback: plain linear scan, used when AVX2 is not
//! available at compile time and as the reference for unit tests
//! of the AVX2 path.

/// Return the smallest index `i >= start` with
/// `(sevs[i] & not_sev) == 0`, or `sevs.len()` if no such index
/// exists.
///
/// Dispatches to [`find_sev_match_avx2`] (when built with AVX2)
/// or [`find_sev_match_scalar`] (otherwise). Both paths produce
/// identical results on identical inputs; the cargo test suite
/// asserts agreement via the property test in `bba::tests`
/// (also referenced from `gm::tests` once ADR-009 lands).
#[cfg(target_feature = "avx2")]
#[inline]
pub(crate) fn find_sev_match(sevs: &[u64], not_sev: u64, start: usize) -> usize {
    // SAFETY: caller passes a valid slice; we bounds-check every load
    // against `len` before issuing it.
    unsafe { find_sev_match_avx2(sevs, not_sev, start) }
}

#[cfg(not(target_feature = "avx2"))]
#[inline]
pub(crate) fn find_sev_match(sevs: &[u64], not_sev: u64, start: usize) -> usize {
    find_sev_match_scalar(sevs, not_sev, start)
}

/// Scalar implementation of [`find_sev_match`]. Used as the
/// non-AVX2 build path and as the reference for unit tests of the
/// AVX2 path.
#[inline]
pub(crate) fn find_sev_match_scalar(sevs: &[u64], not_sev: u64, start: usize) -> usize {
    let len = sevs.len();
    let mut idx = start;
    while idx < len {
        if (sevs[idx] & not_sev) == 0 {
            return idx;
        }
        idx += 1;
    }
    len
}

/// AVX2 implementation of [`find_sev_match`]. Mirrors Singular's
/// `kSevScanAVX2` (`~/Singular-next-opt/kernel/GBEngine/kstd2.cc:74`).
///
/// # Safety
/// Requires AVX2 available at runtime. Guaranteed by the
/// `cfg(target_feature = "avx2")` gate on the caller. All loads are
/// bounds-checked against `sevs.len()` before being issued.
#[cfg(target_feature = "avx2")]
#[target_feature(enable = "avx2")]
#[inline]
pub(crate) unsafe fn find_sev_match_avx2(sevs: &[u64], not_sev: u64, start: usize) -> usize {
    use std::arch::x86_64::*;
    let len = sevs.len();
    let mut j = start;
    let ptr = sevs.as_ptr();

    // SAFETY of all the unsafe blocks below: every load is bounded
    // by the surrounding `while j + N <= len` check before issuing,
    // so the AVX2 256-bit loads stay inside the slice.
    unsafe {
        let vnot_sev = _mm256_set1_epi64x(not_sev as i64);
        let vzero = _mm256_setzero_si256();

        // Main loop: 16 entries per iteration. Singular's pattern:
        // four 4-wide AND+CMPEQ operations, OR the masks together,
        // and only branch out when *some* batch matched.
        while j + 16 <= len {
            let v1 = _mm256_loadu_si256(ptr.add(j) as *const __m256i);
            let v2 = _mm256_loadu_si256(ptr.add(j + 4) as *const __m256i);
            let v3 = _mm256_loadu_si256(ptr.add(j + 8) as *const __m256i);
            let v4 = _mm256_loadu_si256(ptr.add(j + 12) as *const __m256i);
            let a1 = _mm256_and_si256(v1, vnot_sev);
            let a2 = _mm256_and_si256(v2, vnot_sev);
            let a3 = _mm256_and_si256(v3, vnot_sev);
            let a4 = _mm256_and_si256(v4, vnot_sev);
            let c1 = _mm256_cmpeq_epi64(a1, vzero);
            let c2 = _mm256_cmpeq_epi64(a2, vzero);
            let c3 = _mm256_cmpeq_epi64(a3, vzero);
            let c4 = _mm256_cmpeq_epi64(a4, vzero);
            let m1 = _mm256_movemask_epi8(c1) as u32;
            let m2 = _mm256_movemask_epi8(c2) as u32;
            let m3 = _mm256_movemask_epi8(c3) as u32;
            let m4 = _mm256_movemask_epi8(c4) as u32;
            if (m1 | m2 | m3 | m4) != 0 {
                // Find the first matching qword across the four batches.
                // Each set qword has all 8 of its movemask bits set,
                // so trailing_zeros / 8 is the qword index.
                if m1 != 0 {
                    return j + (m1.trailing_zeros() / 8) as usize;
                }
                if m2 != 0 {
                    return j + 4 + (m2.trailing_zeros() / 8) as usize;
                }
                if m3 != 0 {
                    return j + 8 + (m3.trailing_zeros() / 8) as usize;
                }
                return j + 12 + (m4.trailing_zeros() / 8) as usize;
            }
            j += 16;
        }

        // Tail: one 4-wide batch at a time.
        while j + 4 <= len {
            let v = _mm256_loadu_si256(ptr.add(j) as *const __m256i);
            let a = _mm256_and_si256(v, vnot_sev);
            let c = _mm256_cmpeq_epi64(a, vzero);
            let m = _mm256_movemask_epi8(c) as u32;
            if m != 0 {
                return j + (m.trailing_zeros() / 8) as usize;
            }
            j += 4;
        }
    }

    // Scalar tail (0..3 elements).
    find_sev_match_scalar(sevs, not_sev, j)
}

// =====================================================================
// Superset variant for "subset_mask ⊆ sevs[idx]" — used by ADR-009's
// chain-criterion sweep, where the question is "does fixed pair a's
// sev fit inside iterating pair c's sev" (i.e., a divides c). This is
// the dual of `find_sev_match` and uses `_mm256_andnot_si256` to test
// `(~c_sev & subset_mask) == 0` per qword.
// =====================================================================

/// Return the smallest index `i >= start` with
/// `(subset_mask & !sevs[i]) == 0`, or `sevs.len()` if no such index
/// exists.
///
/// Equivalent to "find the first `sevs[i]` that is a *superset* of
/// `subset_mask`" — every set bit in `subset_mask` is also set in
/// `sevs[i]`. This is exactly the sev pre-filter for the divides
/// predicate `subset_mono.divides(sevs_mono[i])`: a candidate may
/// pass divides only if its sev superset's the divider's sev.
///
/// Used by `gm::chain_crit_normal`'s ADR-009 B-internal sweep,
/// where the question per inner-loop iteration is "does the fixed
/// outer pair's lcm divide the iterating inner pair's lcm".
#[cfg(target_feature = "avx2")]
#[inline]
pub(crate) fn find_sev_superset_match(sevs: &[u64], subset_mask: u64, start: usize) -> usize {
    // SAFETY: caller passes a valid slice; we bounds-check every load
    // against `len` before issuing it.
    unsafe { find_sev_superset_match_avx2(sevs, subset_mask, start) }
}

#[cfg(not(target_feature = "avx2"))]
#[inline]
pub(crate) fn find_sev_superset_match(sevs: &[u64], subset_mask: u64, start: usize) -> usize {
    find_sev_superset_match_scalar(sevs, subset_mask, start)
}

/// Scalar implementation of [`find_sev_superset_match`].
#[inline]
pub(crate) fn find_sev_superset_match_scalar(
    sevs: &[u64],
    subset_mask: u64,
    start: usize,
) -> usize {
    let len = sevs.len();
    let mut idx = start;
    while idx < len {
        if (subset_mask & !sevs[idx]) == 0 {
            return idx;
        }
        idx += 1;
    }
    len
}

/// AVX2 implementation of [`find_sev_superset_match`].
///
/// Same overall shape as [`find_sev_match_avx2`] (16-entry unrolled
/// main loop, 4-wide tail, scalar tail) but the per-batch op is
/// `_mm256_andnot_si256(c_sev_vec, vsubset)` (computes
/// `~c_sev & subset_mask`), which is zero per qword iff
/// `subset_mask`'s bits are a subset of that qword's bits.
///
/// # Safety
/// Same as [`find_sev_match_avx2`].
#[cfg(target_feature = "avx2")]
#[target_feature(enable = "avx2")]
#[inline]
pub(crate) unsafe fn find_sev_superset_match_avx2(
    sevs: &[u64],
    subset_mask: u64,
    start: usize,
) -> usize {
    use std::arch::x86_64::*;
    let len = sevs.len();
    let mut j = start;
    let ptr = sevs.as_ptr();
    unsafe {
        let vsubset = _mm256_set1_epi64x(subset_mask as i64);
        let vzero = _mm256_setzero_si256();

        while j + 16 <= len {
            let v1 = _mm256_loadu_si256(ptr.add(j) as *const __m256i);
            let v2 = _mm256_loadu_si256(ptr.add(j + 4) as *const __m256i);
            let v3 = _mm256_loadu_si256(ptr.add(j + 8) as *const __m256i);
            let v4 = _mm256_loadu_si256(ptr.add(j + 12) as *const __m256i);
            // _mm256_andnot_si256(a, b) = (~a) & b. With a = sevs and
            // b = vsubset, the result per qword is `~sevs & subset_mask`,
            // which is zero iff `subset_mask` ⊆ `sevs` per qword.
            let a1 = _mm256_andnot_si256(v1, vsubset);
            let a2 = _mm256_andnot_si256(v2, vsubset);
            let a3 = _mm256_andnot_si256(v3, vsubset);
            let a4 = _mm256_andnot_si256(v4, vsubset);
            let c1 = _mm256_cmpeq_epi64(a1, vzero);
            let c2 = _mm256_cmpeq_epi64(a2, vzero);
            let c3 = _mm256_cmpeq_epi64(a3, vzero);
            let c4 = _mm256_cmpeq_epi64(a4, vzero);
            let m1 = _mm256_movemask_epi8(c1) as u32;
            let m2 = _mm256_movemask_epi8(c2) as u32;
            let m3 = _mm256_movemask_epi8(c3) as u32;
            let m4 = _mm256_movemask_epi8(c4) as u32;
            if (m1 | m2 | m3 | m4) != 0 {
                if m1 != 0 {
                    return j + (m1.trailing_zeros() / 8) as usize;
                }
                if m2 != 0 {
                    return j + 4 + (m2.trailing_zeros() / 8) as usize;
                }
                if m3 != 0 {
                    return j + 8 + (m3.trailing_zeros() / 8) as usize;
                }
                return j + 12 + (m4.trailing_zeros() / 8) as usize;
            }
            j += 16;
        }
        while j + 4 <= len {
            let v = _mm256_loadu_si256(ptr.add(j) as *const __m256i);
            let a = _mm256_andnot_si256(v, vsubset);
            let c = _mm256_cmpeq_epi64(a, vzero);
            let m = _mm256_movemask_epi8(c) as u32;
            if m != 0 {
                return j + (m.trailing_zeros() / 8) as usize;
            }
            j += 4;
        }
    }
    find_sev_superset_match_scalar(sevs, subset_mask, j)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Property test: SIMD and scalar `find_sev_superset_match`
    /// produce identical results across diverse inputs and start
    /// indices, exercising the unrolled main loop, 4-wide tail,
    /// and scalar tail.
    #[test]
    fn find_sev_superset_match_simd_matches_scalar() {
        // Pseudo-random sev array spanning all three loop bodies.
        let len = 200;
        let mut sevs: Vec<u64> = Vec::with_capacity(len);
        let mut state: u64 = 0x00c0_ffee_d00d_face;
        for _ in 0..len {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            sevs.push(state);
        }

        for subset_mask in [
            0u64,
            !0u64,
            0x0000_0000_FFFF_FFFFu64,
            0xAAAA_AAAA_5555_5555u64,
            0x0000_0000_0000_0001u64,
        ] {
            for start in [0usize, 1, 7, 16, 17, 32, 96, 192, 196, 199] {
                let scalar = find_sev_superset_match_scalar(&sevs, subset_mask, start);
                let dispatch = find_sev_superset_match(&sevs, subset_mask, start);
                assert_eq!(
                    scalar, dispatch,
                    "mismatch at subset_mask = {subset_mask:#x}, start = {start}"
                );
            }
        }

        // Edge cases.
        assert_eq!(find_sev_superset_match(&[], 0u64, 0), 0);
        assert_eq!(find_sev_superset_match(&[5u64], 0u64, 0), 0); // empty mask ⊆ anything
        assert_eq!(find_sev_superset_match(&[5u64], !0u64, 0), 1); // full mask ⊄ partial
        assert_eq!(find_sev_superset_match(&[7u64, 5u64], 1u64, 0), 0); // 1 ⊆ 7
        assert_eq!(find_sev_superset_match(&[7u64, 5u64], 2u64, 0), 0); // 2 ⊆ 7
        assert_eq!(find_sev_superset_match(&[7u64, 5u64], 4u64, 0), 0); // 4 ⊆ 7
        assert_eq!(find_sev_superset_match(&[2u64, 5u64], 4u64, 0), 1); // 4 ⊄ 2; 4 ⊆ 5
    }
}
