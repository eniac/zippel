//! `benchmarks::mem` counts transient heap. Its own test binary, so no
//! other test allocates while the counter is on.

use benchmarks::mem::{Counting, peak_of};

#[global_allocator]
static ALLOC: Counting = Counting;

#[test]
fn peak_counts_transient_allocations() {
    let before = vec![0u8; 8 << 20];
    let ((), peak) = peak_of(|| {
        let transient = vec![1u8; 4 << 20];
        std::hint::black_box(&transient);
        drop(transient);
        let kept = vec![2u8; 1 << 20];
        std::hint::black_box(&kept);
    });
    // The 4 MiB buffer counts though it was freed; `before` does not.
    assert!((4 << 20..5 << 20).contains(&peak), "peak = {peak}");
    drop(before);
}
