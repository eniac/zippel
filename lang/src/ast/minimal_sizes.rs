//! Bounded size search, using compiler validation and resolved-call coverage.

use std::cell::RefCell;
use std::collections::BTreeMap;

use share::traversal::ToTraversal1;
use share::{Ctx, Set};
use thiserror::Error;

use super::exp::ExpTraversal;
use super::module::{ExpandedModule, ExpansionFailure, UModule};
use super::{Sig, Size};
use crate::ast::module::DeclId;
use crate::diagnostic::{Diagnostic, Phase, Severity};
use crate::id::{Tid, Vid};

/// The largest value searched for an unset `Size` parameter.
pub const MAX_DEFAULT_SIZE: usize = 16;

// Bundled baseline: 39 sources need at most 6 candidates and 29 instances
// in any successfully expanded candidate before acceptance (2026-10-14).
const MAX_CANDIDATES: usize = 4096;
const MAX_INSTANCES: usize = 4096;

/// Validation progress of a representative rejected candidate, in stage order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SizeSearchStage {
    /// Declaration-range evaluation or nonemptiness failed.
    Ranges,
    /// Concrete declarations could not be assembled.
    Concretization,
    /// An expanded declaration failed type checking.
    Typecheck,
    /// A type-valid candidate did not cover every required source overload.
    Coverage,
}

/// Rejection of one candidate, not a proof that all configurations share its error.
#[derive(Debug)]
pub struct SizeRejection {
    /// Candidate values, including supplied sizes.
    pub candidate: Ctx<Tid, usize>,
    /// Validation stage that rejected this candidate.
    pub stage: SizeSearchStage,
    /// Source diagnostics explaining this rejection.
    pub diagnostics: Vec<Diagnostic>,
}

/// A finite search work budget that was reached before completing the search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SizeSearchLimit {
    /// Maximum number of completely checked candidates.
    Candidates(usize),
    /// Maximum instances emitted while expanding one candidate.
    Instances {
        /// The configured maximum.
        limit: usize,
        /// Instances emitted before stopping expansion.
        expanded: usize,
    },
}

impl std::fmt::Display for SizeSearchLimit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Candidates(limit) => write!(f, "candidate budget ({limit})"),
            Self::Instances { limit, expanded } => {
                write!(f, "instance budget ({expanded}/{limit})")
            }
        }
    }
}

/// A bounded search failure, preserving the furthest representative rejection.
#[derive(Debug, Error)]
pub enum SizeSearchError {
    /// Every candidate allowed by the value bound was rejected.
    #[error("No valid size configuration found within the search bound")]
    Exhausted {
        /// Number of candidates checked.
        candidates_checked: usize,
        /// Furthest rejection; ties retain the first candidate in search order.
        rejection: SizeRejection,
    },
    /// A work budget stopped the search; untested candidates may succeed.
    #[error(
        "Size search stopped at a work limit after {candidates_checked} checked candidates: {limit}"
    )]
    WorkLimit {
        /// Work budget that stopped the search.
        limit: SizeSearchLimit,
        /// Number of completely checked candidates.
        candidates_checked: usize,
        /// Furthest completed rejection, if any.
        rejection: Option<SizeRejection>,
    },
}

#[derive(Clone, Copy)]
struct Limits {
    candidates: usize,
    instances: usize,
}

/// Dense identity of a concrete instance, independent of source locations.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct InstanceId(usize);

struct Source<'a> {
    signature: &'a Sig<Size>,
    /// Index shared by all source overloads with the same function/protocol name.
    group: usize,
    protocol: bool,
}

struct Sources<'a> {
    declarations: Vec<Source<'a>>,
    group_count: usize,
}

impl<'a> Sources<'a> {
    fn new(module: &'a UModule) -> Self {
        let mut group_ids = BTreeMap::<Vid, usize>::new();
        let declarations = module
            .iter()
            .map(|(sig, body)| {
                let next = group_ids.len();
                Source {
                    signature: sig,
                    group: *group_ids.entry(sig.name.node.clone()).or_insert(next),
                    protocol: body.is_proto(),
                }
            })
            .collect();
        Self {
            declarations,
            group_count: group_ids.len(),
        }
    }
}

/// Extends `fixed` with minimal values for the module's other `Size` parameters.
///
/// Unset values are bounded by `1..=MAX_DEFAULT_SIZE`. Smallest means the least sum,
/// with ties broken by values in name order. Fixed values are preserved, even above the
/// search bound.
/// When `fixed` supplies every declared `Size` parameter, only that assignment is
/// validated; no alternatives are searched and no supplied values are replaced.
///
/// Each assignment must satisfy both compiler validation and overload coverage:
///
/// - Expand every declaration and require every branch of its type-variable ranges to
///   produce instances. Type-check every expanded instance, including unused helpers,
///   using the ordinary rules for calls, vector lengths, indexing and other operators.
///   Unused helpers can therefore still constrain sizes through their types and ranges.
///   Only error diagnostics reject an assignment; warnings allow coverage checking to continue.
/// - Start coverage only from concrete protocol instances. Follow the actual function
///   calls selected during type checking, including calls in protocol relations.
/// - Group source declarations by function name. Follow the recorded calls between these
///   groups from protocol groups, using calls from all checked instances. Every source
///   overload in a group reached this way must have at least one concrete instance
///   reached from a protocol in the instance graph. All its other instances must still
///   typecheck, but need not be reached.
/// - Groups outside that protocol-reachable group graph have no coverage requirement.
///   Unused helpers are never additional starting points, and their calls cannot supply
///   coverage for overloads that protocols miss.
///
/// For example, if a protocol calls `weights` with a vector of length `N`, and `weights`
/// has a base definition at length 1 and a recursive definition at `2..5` that calls the
/// preceding length, `N=1` typechecks but misses the recursive definition. `N=2` reaches
/// both definitions and satisfies coverage. If only an unused helper calls `weights`,
/// those definitions have no coverage requirement.
///
/// Coverage visits each graph vertex at most once, so function and protocol call cycles
/// do not require special entry rules. This checks static calls, not runtime execution
/// or termination, and does not guarantee Graph IR construction or projection succeeds.
///
/// # Errors
/// Returns [`SizeSearchError`] on exhaustion or a search work limit, preserving one
/// failed assignment's stage and diagnostics. This does not establish whether sizes
/// outside the bound would succeed or whether an error is size-independent.
pub fn minimal_sizes(
    module: &UModule,
    fixed: &Ctx<Tid, usize>,
) -> Result<Ctx<Tid, usize>, SizeSearchError> {
    search_with_limits(
        module,
        fixed,
        Limits {
            candidates: MAX_CANDIDATES,
            instances: MAX_INSTANCES,
        },
    )
}

fn parameters(module: &UModule, fixed: &Ctx<Tid, usize>) -> (Ctx<Tid, usize>, Vec<Tid>) {
    let mentioned = RefCell::new(Set::new());
    let record = |size: Size| {
        let mut vars = mentioned.borrow_mut();
        *vars = vars.clone().union(size.free_vars());
        Ok::<_, ()>(size)
    };
    for (sig, body) in module.iter() {
        let _ = sig.clone().traverse1(&mut &record);
        let _ = body.clone().traverse_exp(&mut &record, &mut &record);
    }
    let mut base = fixed.clone();
    let mut searched = Vec::new();
    for name in module
        .size_params()
        .iter()
        .filter(|name| !fixed.contains(name))
    {
        if mentioned.borrow().contains(name) {
            searched.push(name.clone());
        } else {
            base.insert(name, &1);
        }
    }
    (base, searched)
}

fn search_with_limits(
    module: &UModule,
    fixed: &Ctx<Tid, usize>,
    limits: Limits,
) -> Result<Ctx<Tid, usize>, SizeSearchError> {
    let sources = Sources::new(module);
    let (base, searched) = parameters(module, fixed);
    let mut best: Option<SizeRejection> = None;
    let mut checked = 0;
    let n = searched.len();
    for values in (n..=n.saturating_mul(MAX_DEFAULT_SIZE))
        .flat_map(|total| Compositions::new(total, n, MAX_DEFAULT_SIZE))
    {
        if checked == limits.candidates {
            return Err(SizeSearchError::WorkLimit {
                limit: SizeSearchLimit::Candidates(limits.candidates),
                candidates_checked: checked,
                rejection: best,
            });
        }
        let mut sizes = base.clone();
        for (name, value) in searched.iter().zip(&values) {
            sizes.insert(name, value);
        }
        match check_candidate(module, &sources, &sizes, limits.instances) {
            Ok(()) => return Ok(sizes),
            Err(CandidateFailure::Instances(expanded)) => {
                return Err(SizeSearchError::WorkLimit {
                    limit: SizeSearchLimit::Instances {
                        limit: limits.instances,
                        expanded,
                    },
                    candidates_checked: checked,
                    rejection: best,
                });
            }
            Err(CandidateFailure::Rejected(stage, diagnostics)) => {
                checked += 1;
                if best.as_ref().is_none_or(|previous| stage > previous.stage) {
                    best = Some(SizeRejection {
                        candidate: sizes,
                        stage,
                        diagnostics,
                    });
                }
            }
        }
    }
    Err(SizeSearchError::Exhausted {
        candidates_checked: checked,
        rejection: best.expect("positive bounded search evaluates at least one candidate"),
    })
}

enum CandidateFailure {
    Rejected(SizeSearchStage, Vec<Diagnostic>),
    Instances(usize),
}

fn check_candidate(
    module: &UModule,
    sources: &Sources<'_>,
    sizes: &Ctx<Tid, usize>,
    max_instances: usize,
) -> Result<(), CandidateFailure> {
    let expanded =
        module
            .expand(sizes, true, Some(max_instances))
            .map_err(|failure| match failure {
                ExpansionFailure::Substitutions(error) => {
                    CandidateFailure::Rejected(SizeSearchStage::Ranges, vec![error.into()])
                }
                ExpansionFailure::Concretization(error) => {
                    CandidateFailure::Rejected(SizeSearchStage::Concretization, vec![error.into()])
                }
                ExpansionFailure::Limit { expanded } => CandidateFailure::Instances(expanded),
            })?;
    let instances: BTreeMap<_, _> = expanded
        .module
        .iter()
        .enumerate()
        .map(|(id, (sig, _))| (sig.clone(), InstanceId(id)))
        .collect();
    let edges = RefCell::new(vec![Set::new(); instances.len()]);
    let diagnostics = expanded.module.typecheck_with_calls(&|caller, callee| {
        edges.borrow_mut()[instances[caller].0].insert(instances[callee]);
    });
    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return Err(CandidateFailure::Rejected(
            SizeSearchStage::Typecheck,
            diagnostics,
        ));
    }
    check_coverage(&expanded, sources, edges.into_inner())
        .map_err(|diagnostics| CandidateFailure::Rejected(SizeSearchStage::Coverage, diagnostics))
}

/// Checks source-overload coverage after all concrete instances have passed type checking.
///
/// `sources` describes the original declarations and groups overloads by name. `expanded`
/// maps each concrete signature back to its source `DeclId`. `instance_calls[caller]`
/// contains the selected callee instances, including relation calls. Instance IDs follow
/// `expanded.module.iter()` order, matching the enumeration in `check_candidate`.
///
/// Two traversals answer different questions:
///
/// - The group graph combines calls from every checked instance. Traversing it from
///   protocol groups determines which groups' source overloads require coverage.
/// - The instance graph follows concrete calls only from protocol instances. Reaching
///   any instance of a source declaration covers that declaration, not its sibling overloads.
///
/// For example, a protocol calling `weights(1)` makes all `weights` source overloads
/// required, but covers only the definition selected for length 1. Calls recorded while
/// checking an unreached `weights(2)` cannot cover its definition unless a protocol reaches it.
/// Unused groups have no coverage requirement. Both traversals use visited sets for cycles.
///
/// Returns one diagnostic per required source declaration with no reached instance.
fn check_coverage(
    expanded: &ExpandedModule,
    sources: &Sources<'_>,
    instance_calls: Vec<Set<InstanceId>>,
) -> Result<(), Vec<Diagnostic>> {
    // Indexed by InstanceId: multiple range expansions can share one source DeclId.
    let source_by_instance: Vec<DeclId> = expanded
        .module
        .iter()
        .map(|(sig, _)| expanded.origins[sig])
        .collect();

    // Each concrete caller -> callee edge also contributes a group -> group edge.
    let mut group_calls = vec![Set::new(); sources.group_count];
    let mut protocol_groups = Vec::new();
    let mut protocol_instances = Vec::new();
    for (instance_id, source_id) in source_by_instance.iter().enumerate() {
        let caller_source = &sources.declarations[source_id.0];
        if caller_source.protocol {
            protocol_groups.push(caller_source.group);
            protocol_instances.push(instance_id);
        }
        for callee_id in instance_calls[instance_id].iter() {
            let callee_source = &sources.declarations[source_by_instance[callee_id.0].0];
            group_calls[caller_source.group].insert(callee_source.group);
        }
    }

    let group_calls: Vec<Vec<usize>> = group_calls
        .into_iter()
        .map(|callees| callees.into_iter().collect())
        .collect();
    // Indexed by group: true means every source overload in that group needs coverage.
    let required_groups = reachable(&group_calls, protocol_groups);
    let instance_calls: Vec<Vec<usize>> = instance_calls
        .into_iter()
        .map(|callees| callees.into_iter().map(|id| id.0).collect())
        .collect();
    let reached_instances = reachable(&instance_calls, protocol_instances);

    // Indexed by DeclId: one reached expansion is enough to cover a source declaration.
    let mut covered_sources = vec![false; sources.declarations.len()];
    for (instance_id, source_id) in source_by_instance.into_iter().enumerate() {
        if reached_instances[instance_id] {
            covered_sources[source_id.0] = true;
        }
    }
    let diagnostics: Vec<_> = sources
        .declarations
        .iter()
        .enumerate()
        .filter(|(source_id, source)| required_groups[source.group] && !covered_sources[*source_id])
        .map(|(_, source)| {
            let sig = source.signature;
            Diagnostic::error(
                Phase::Type,
                sig.name.span.clone(),
                &format!(
                    "Function overload `{}` is not covered by candidate sizes",
                    sig.name.node
                ),
            )
            .note("this candidate typechecks but does not cover this source declaration")
        })
        .collect();
    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

fn reachable(graph: &[Vec<usize>], roots: impl IntoIterator<Item = usize>) -> Vec<bool> {
    let mut reached = vec![false; graph.len()];
    let mut pending: Vec<_> = roots.into_iter().collect();
    while let Some(node) = pending.pop() {
        if !reached[node] {
            reached[node] = true;
            pending.extend(graph[node].iter().copied());
        }
    }
    reached
}

/// One fixed-sum tuple at a time, in lexicographic order.
struct Compositions {
    values: Option<Vec<usize>>,
    max: usize,
}

impl Compositions {
    fn new(total: usize, parts: usize, max: usize) -> Self {
        let values = if total < parts || total > parts.saturating_mul(max) {
            None
        } else {
            let mut values = vec![1; parts];
            Self::fill(&mut values, total, max);
            Some(values)
        };
        Self { values, max }
    }

    fn fill(values: &mut [usize], mut total: usize, max: usize) {
        let count = values.len();
        for (id, value) in values.iter_mut().enumerate() {
            *value = total
                .saturating_sub((count - id - 1).saturating_mul(max))
                .max(1);
            total -= *value;
        }
    }
}

impl Iterator for Compositions {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        let values = self.values.as_mut()?;
        let result = values.clone();
        let mut suffix = values.last().copied().unwrap_or(0);
        for id in (0..values.len().saturating_sub(1)).rev() {
            if values[id] < self.max && suffix > values.len() - id - 1 {
                values[id] += 1;
                Self::fill(&mut values[id + 1..], suffix - 1, self.max);
                return Some(result);
            }
            suffix += values[id];
        }
        self.values = None;
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compositions_match_exhaustive_order() {
        for parts in 0..=4 {
            let mut all = vec![vec![]];
            for _ in 0..parts {
                all = all
                    .into_iter()
                    .flat_map(|prefix| {
                        (1..=3).map(move |value| {
                            let mut tuple = prefix.clone();
                            tuple.push(value);
                            tuple
                        })
                    })
                    .collect();
            }
            for total in 0..=parts * 3 + 1 {
                let expected: Vec<_> = all
                    .iter()
                    .filter(|tuple| tuple.iter().sum::<usize>() == total)
                    .cloned()
                    .collect();
                assert_eq!(
                    Compositions::new(total, parts, 3).collect::<Vec<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn compositions_do_not_materialize_a_large_sum_batch() {
        let values: Vec<_> = Compositions::new(128, 64, 16).take(3).collect();
        assert_eq!(values.len(), 3);
        for tuple in &values {
            assert_eq!(tuple.len(), 64);
            assert_eq!(tuple.iter().sum::<usize>(), 128);
        }
        assert!(values.windows(2).all(|pair| pair[0] < pair[1]));
    }

    #[test]
    fn reachability_handles_cycles_and_multiple_roots() {
        let graph = vec![vec![1], vec![2], vec![1], vec![3], vec![]];
        assert_eq!(reachable(&graph, [0]), vec![true, true, true, false, false]);
        assert_eq!(
            reachable(&graph, [0, 4]),
            vec![true, true, true, false, true]
        );
        assert_eq!(reachable(&graph, []), vec![false; 5]);
    }

    #[test]
    fn candidate_budget_is_not_reported_as_exhaustion() {
        let module = UModule::parse(
            r"
proto p<F: Field, N: Size>(instance a: [F; N], instance b: [F; 17]) where dot(a, b) == a[0] {
    verify(dot(a, b) == a[0])
}
",
        )
        .0
        .unwrap();
        let error = search_with_limits(
            &module,
            &Ctx::new(),
            Limits {
                candidates: 2,
                instances: 10,
            },
        )
        .unwrap_err();
        match error {
            SizeSearchError::WorkLimit {
                limit,
                candidates_checked,
                rejection,
            } => {
                assert_eq!(limit, SizeSearchLimit::Candidates(2));
                assert_eq!(candidates_checked, 2);
                let rejection = rejection.unwrap();
                assert_eq!(rejection.stage, SizeSearchStage::Typecheck);
                assert_eq!(rejection.candidate.get(&Tid::new("N")), Some(&1));
            }
            SizeSearchError::Exhausted { .. } => panic!("search stopped before exhaustion"),
        }
    }

    #[test]
    fn exact_candidate_budget_can_complete_exhaustion() {
        let module = UModule::parse(
            r"
proto p<F: Field, N: Size>(instance a: [F; N], instance b: [F; 17]) where dot(a, b) == a[0] {
    verify(dot(a, b) == a[0])
}
",
        )
        .0
        .unwrap();
        let error = search_with_limits(
            &module,
            &Ctx::new(),
            Limits {
                candidates: 16,
                instances: 10,
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            SizeSearchError::Exhausted {
                candidates_checked: 16,
                ..
            }
        ));
    }

    #[test]
    fn huge_range_stops_without_allocating_all_instances() {
        let src = format!(
            "fn f<F: Field, K: 0..{}>(instance a: [F; K+1]) -> F {{ a[0] }}\nproto p<F: Field, N: Size>(instance a: F) where a == a {{ verify(a == a) }}",
            usize::MAX
        );
        let module = UModule::parse(&src).0.unwrap();
        let error = search_with_limits(
            &module,
            &Ctx::new(),
            Limits {
                candidates: 10,
                instances: 2,
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            SizeSearchError::WorkLimit {
                limit: SizeSearchLimit::Instances {
                    limit: 2,
                    expanded: 2
                },
                candidates_checked: 0,
                rejection: None,
            }
        ));
    }
}
