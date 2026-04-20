use log::debug;
use petgraph::graph::NodeIndex;
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};

// ---------------------------------------------------------------------------
// SyncQueue — thread-safe queue for sync (sponge-requiring) nodes
// ---------------------------------------------------------------------------

/// A thread-safe queue for sync nodes that must be processed on the
/// main thread. Pool tasks push ready sync nodes here, and the main
/// thread pops them for sequential sponge processing.
pub struct SyncQueue {
    inner: Mutex<SyncQueueInner>,
    cvar: Condvar,
    /// Shared reference to the pool's `used` counter, so that
    /// `pop()` can detect when the pool is truly idle.
    used: Arc<AtomicUsize>,
}

struct SyncQueueInner {
    /// FIFO queue of ready sync nodes.
    queue: VecDeque<NodeIndex>,
}

impl SyncQueue {
    fn new(used: Arc<AtomicUsize>) -> Self {
        Self {
            inner: Mutex::new(SyncQueueInner {
                queue: VecDeque::new(),
            }),
            cvar: Condvar::new(),
            used,
        }
    }

    /// Push a sync node onto the queue and notify the main thread.
    pub fn push(&self, node: NodeIndex) {
        let mut inner = self.inner.lock().unwrap();
        inner.queue.push_back(node);
        self.cvar.notify_one();
    }

    /// Notify the main thread that the pool has become idle (no running
    /// or pending tasks remain).
    ///
    /// Must hold the inner lock to avoid lost wakeups: if the main
    /// thread is between checking `used` and calling `wait()`, this
    /// lock ensures it enters `wait()` before we notify.
    fn notify_pool_idle(&self) {
        let _guard = self.inner.lock().unwrap();
        self.cvar.notify_one();
    }

    /// Pop a sync node from the queue. Returns `None` if the queue is
    /// empty AND the pool is truly idle (`used == 0`). Otherwise blocks
    /// until either a node is available or the pool becomes idle.
    pub fn pop(&self) -> Option<NodeIndex> {
        let mut inner = self.inner.lock().unwrap();
        loop {
            if let Some(node) = inner.queue.pop_front() {
                return Some(node);
            }
            if self.used.load(Ordering::SeqCst) == 0 {
                return None;
            }
            inner = self.cvar.wait(inner).unwrap();
        }
    }
}

// ---------------------------------------------------------------------------
// PoolManager — capacity-managed thread pool with per-task thread allocation
// ---------------------------------------------------------------------------

struct PendingTask {
    cost: usize,
    task: Box<dyn FnOnce() + Send>,
}

/// Shared state protected by the pool-state mutex.
struct PoolState {
    /// FIFO queue of tasks waiting for capacity.
    ///
    /// TODO: can we optimize the execution order of tasks?
    queue: VecDeque<PendingTask>,
}

/// Manages a pool of worker threads with capacity-based task scheduling.
///
/// Each task declares a `cost` (the number of threads it needs, from
/// `thread_num`). The PoolManager ensures that the sum of costs of
/// concurrently running tasks does not exceed `total_capacity`. When
/// capacity is available, tasks start immediately; otherwise they are
/// queued until capacity is freed by completed tasks.
///
/// Per-cost thread pools are cached for reuse. When a task of a given
/// cost is submitted, the manager checks for a free pool of that size;
/// if none is available, a new one is created. When the task completes,
/// the pool is returned to the cache.
///
/// Completed tasks can submit new tasks (e.g., when a node finishes and
/// its successors become ready) via the `submit` method on the shared
/// `Arc<PoolManager>`, enabling successor-driven scheduling.
///
/// Sync nodes (sponge-requiring nodes) discovered by pool tasks are
/// pushed onto a `SyncQueue` so the main thread can process them
/// sequentially. When all pool work is finished, the main thread is
/// notified via `SyncQueue::notify_pool_idle()`.
pub struct PoolManager {
    total_capacity: usize,
    used: Arc<AtomicUsize>,
    pool_cache: Mutex<HashMap<usize, Vec<Arc<rayon::ThreadPool>>>>,
    state: Mutex<PoolState>,
    /// TODO: what if we replace SyncQueue with a per-task channel?
    sync_queue: SyncQueue,
}

impl PoolManager {
    pub fn new(total_capacity: usize) -> Arc<Self> {
        let used = Arc::new(AtomicUsize::new(0));
        Arc::new(Self {
            total_capacity,
            used: Arc::clone(&used),
            pool_cache: Mutex::new(HashMap::new()),
            state: Mutex::new(PoolState {
                queue: VecDeque::new(),
            }),
            sync_queue: SyncQueue::new(used),
        })
    }

    /// Get a reference to the sync queue for pushing sync nodes
    /// or waiting for them.
    pub fn sync_queue(&self) -> &SyncQueue {
        &self.sync_queue
    }

    /// Atomically try to reserve `cost` units of capacity in `used`.
    ///
    /// `credit` represents capacity that will be freed but is still
    /// counted in `used` (e.g., a completing task's cost). The check
    /// becomes `current + cost <= total_capacity + credit`, which is
    /// equivalent to `current + cost - credit <= total_capacity`.
    ///
    /// Returns `true` if the reservation succeeded (`used += cost`).
    fn try_reserve(&self, cost: usize, credit: usize) -> bool {
        loop {
            let current = self.used.load(Ordering::SeqCst);
            if current + cost > self.total_capacity + credit {
                return false;
            }
            match self.used.compare_exchange_weak(
                current,
                current + cost,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return true,
                Err(_) => continue,
            }
        }
    }

    /// Submit a task with its thread cost.
    ///
    /// Fast path: atomically reserve capacity via CAS and start
    /// immediately. Slow path: queue the task, then try to drain
    /// in case capacity has become available since the CAS loop
    /// exited.
    pub fn submit(
        self: &Arc<Self>,
        cost: usize,
        task: Box<dyn FnOnce() + Send>,
    ) {
        // Fast path: atomically reserve capacity and start immediately.
        if self.try_reserve(cost, 0) {
            self.spawn_task(cost, task);
            return;
        }
        // Slow path: queue the task, then try to drain in case
        // capacity has become available since the CAS loop exited.
        let mut state = self.state.lock().unwrap();
        state.queue.push_back(PendingTask { cost, task });
        self.drain_pending(&mut state, 0);
    }

    /// Spawn a task on a rayon pool.
    ///
    /// The caller must have already reserved `cost` units in `used`
    /// via `try_reserve`. Unlike the old `start_task`, this does NOT
    /// increment `used` — the reservation is already accounted for.
    fn spawn_task(
        self: &Arc<Self>,
        cost: usize,
        task: Box<dyn FnOnce() + Send>,
    ) {
        let pool = self.get_or_create_pool(cost);
        let pm = Arc::clone(self);
        let closure_pool = Arc::clone(&pool);
        // The sender clone is moved into the closure so that the
        // channel stays open while the task is running.  When the
        // task finishes the clone is dropped; if this was the last
        // sender the channel closes and `pop()` returns `None`.
        pool.spawn(move || {
            task();
            pm.on_task_completed(cost, closure_pool);
        });
    }

    fn get_or_create_pool(&self, cost: usize) -> Arc<rayon::ThreadPool> {
        let mut cache = self.pool_cache.lock().unwrap();
        if let Some(pools) = cache.get_mut(&cost) {
            if let Some(pool) = pools.pop() {
                return pool;
            }
        }
        drop(cache);
        Arc::new(
            rayon::ThreadPoolBuilder::new()
                .num_threads(cost.max(1))
                .build()
                .expect("Failed to create thread pool"),
        )
    }

    /// Drain pending tasks that fit within capacity.
    ///
    /// Must be called while holding the `state` lock. `credit`
    /// represents capacity in `used` that will be freed (e.g., a
    /// completing task's cost that is still counted in `used`).
    fn drain_pending(
        self: &Arc<Self>,
        state: &mut PoolState,
        credit: usize,
    ) {
        while let Some(pending) = state.queue.front() {
            if self.try_reserve(pending.cost, credit) {
                let PendingTask { cost, task } = state.queue.pop_front().unwrap();
                self.spawn_task(cost, task);
            } else {
                break;
            }
        }
    }

    fn on_task_completed(self: &Arc<Self>, completed_cost: usize, pool: Arc<rayon::ThreadPool>) {
        debug!("[on_task_completed] cost={}", completed_cost);

        // Drain queued tasks that now fit within capacity.
        // `completed_cost` provides virtual credit: it is still in
        // `used` but will be freed once draining is complete, so
        // the capacity check accounts for it.
        //
        // We maintain the invariant that `used` is only decremented
        // after draining, so `used > 0` reliably indicates that at
        // least one task has not yet completed its on_task_completed.
        // This ensures SyncQueue::pop() does not return None while
        // pending tasks remain that could be started.
        loop {
            let mut state = self.state.lock().unwrap();
            if let Some(pending) = state.queue.front() {
                if self.try_reserve(pending.cost, completed_cost) {
                    let PendingTask { cost, task } = state.queue.pop_front().unwrap();
                    drop(state);
                    self.spawn_task(cost, task);
                    continue;
                }
            }

            // A task is considered ended once it drained the queue.
            // This provides a way for sync queue to examine if pool is empty.
            //
            // - `used` is non-zero <-> At least one task is not ended
            let prev_used = self.used.fetch_sub(completed_cost, Ordering::SeqCst);

            // As long as used is zero after sub, we need to notify main thread
            if prev_used == completed_cost {
                self.sync_queue.notify_pool_idle();
            }
            break;
        }

        // Return the pool to the cache for reuse.
        let mut cache = self.pool_cache.lock().unwrap();
        cache.entry(completed_cost).or_default().push(pool);
    }
}
