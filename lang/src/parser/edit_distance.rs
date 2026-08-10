//! Restricted Damerau-Levenshtein edit distance for "did you mean" suggestions.
//!
//! Ported from rustc's `compiler/rustc_span/src/edit_distance.rs`.
//! "Restricted" means transpositions are allowed but a transposed character
//! cannot be modified again (no substring of length 2 is edited twice).

use std::cmp;

/// Compute the restricted Damerau-Levenshtein edit distance between `a` and `b`.
///
/// Returns `None` if the distance exceeds `limit`.
///
/// Operations counted (each cost 1):
/// - insertion, deletion, substitution, transposition of adjacent chars.
pub fn edit_distance(a: &str, b: &str, limit: usize) -> Option<usize> {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();

    // Ensure `b` is the shorter string for memory efficiency.
    let (a, b) = if a.len() < b.len() {
        (&b, &a)
    } else {
        (&a, &b)
    };

    let min_dist = a.len() - b.len();
    if min_dist > limit {
        return None;
    }

    // Strip common prefix.
    let mut start = 0;
    while start < b.len() && a[start] == b[start] {
        start += 1;
    }
    // Strip common suffix.
    let mut end = 0;
    while end < b.len() - start && a[a.len() - 1 - end] == b[b.len() - 1 - end] {
        end += 1;
    }

    let a = &a[start..a.len() - end];
    let b = &b[start..b.len() - end];

    if b.is_empty() {
        return Some(a.len());
    }

    let b_len = b.len();
    let mut prev_prev = vec![usize::MAX; b_len + 1];
    let mut prev = (0..=b_len).collect::<Vec<_>>();
    let mut curr = vec![0; b_len + 1];

    for i in 1..=a.len() {
        curr[0] = i;
        for j in 1..=b_len {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            curr[j] = cmp::min(prev[j] + 1, cmp::min(curr[j - 1] + 1, prev[j - 1] + cost));
            // Transposition.
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                curr[j] = cmp::min(curr[j], prev_prev[j - 2] + 1);
            }
        }
        std::mem::swap(&mut prev_prev, &mut prev);
        std::mem::swap(&mut prev, &mut curr);
    }

    let dist = prev[b_len];
    if dist <= limit {
        Some(dist)
    } else {
        None
    }
}

/// Find the best matching candidate for `lookup` from `candidates`.
///
/// Uses the same threshold as rustc: `max(lookup.len(), 3) / 3`.
/// Returns the closest candidate if one is within the threshold.
pub fn find_best_match<'a>(candidates: &[&'a str], lookup: &str) -> Option<&'a str> {
    if candidates.is_empty() || lookup.is_empty() {
        return None;
    }

    let max_dist = cmp::max(lookup.len(), 3) / 3;

    // Exact case-insensitive match takes priority.
    let lookup_lower = lookup.to_lowercase();
    for &cand in candidates {
        if cand.to_lowercase() == lookup_lower {
            return Some(cand);
        }
    }

    // Edit distance match.
    let mut best: Option<(usize, &str)> = None;
    for &cand in candidates {
        if let Some(dist) = edit_distance(lookup, cand, max_dist) {
            if best.is_none_or(|(bd, _)| dist < bd) {
                best = Some((dist, cand));
            }
        }
    }
    best.map(|(_, cand)| cand)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_match() {
        assert_eq!(edit_distance("abc", "abc", 0), Some(0));
    }

    #[test]
    fn one_substitution() {
        assert_eq!(edit_distance("abc", "abd", 1), Some(1));
    }

    #[test]
    fn one_transposition() {
        // "ab" -> "ba" is 1 transposition, not 2 substitutions.
        assert_eq!(edit_distance("ab", "ba", 1), Some(1));
    }

    #[test]
    fn beyond_limit() {
        assert_eq!(edit_distance("abc", "xyz", 1), None);
    }

    #[test]
    fn best_match_keyword() {
        let kws = ["where", "let", "fn", "proto", "type"];
        assert_eq!(find_best_match(&kws, "wher"), Some("where"));
    }

    #[test]
    fn best_match_no_result() {
        let kws = ["where", "let", "fn", "proto", "type"];
        assert_eq!(find_best_match(&kws, "xyz"), None);
    }

    #[test]
    fn best_match_case_insensitive() {
        let kws = ["Field", "Group", "Size"];
        assert_eq!(find_best_match(&kws, "field"), Some("Field"));
    }
}
