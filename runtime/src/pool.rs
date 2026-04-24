use log::debug;
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

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
    /// TODO: current FIFO ordering suffers from head-of-line blocking:
    /// if the task at the front requires more capacity than available,
    /// smaller tasks behind it that *could* fit are also blocked.
    /// Consider priority-based or best-fit scheduling to improve throughput.
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
/// pushed onto the sync channel so the main thread can process them
/// sequentially. When all pool work is finished the channel closes
/// (all sender clones dropped) and `SyncReceiver::pop()` returns
/// `None`, signalling that the pool is idle.
pub struct PoolManager {
    total_capacity: usize,
    used: AtomicUsize,
    pool_cache: Mutex<HashMap<usize, Vec<Arc<rayon::ThreadPool>>>>,
    state: Mutex<PoolState>,
}

impl PoolManager {
    pub fn new(total_capacity: usize) -> Arc<Self> {
        Arc::new(Self {
            total_capacity,
            used: AtomicUsize::new(0),
            pool_cache: Mutex::new(HashMap::new()),
            state: Mutex::new(PoolState {
                queue: VecDeque::new(),
            }),
        })
    }

    /// Atomically try to reserve `cost` units of capacity in `used`.
    ///
    /// Returns `true` if the reservation succeeded (`used += cost`).
    /// Uses a CAS loop to handle concurrent reservations.
    fn try_reserve(&self, cost: usize) -> bool {
        loop {
            let current = self.used.load(Ordering::SeqCst);
            if current + cost > self.total_capacity {
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
    /// immediately. Slow path: queue the task, then drain any tasks
    /// that now fit within capacity. Drained tasks are collected
    /// under the state lock and spawned after releasing it, so that
    /// pool creation (which may be slow) does not block other
    /// submitters.
    pub fn submit(self: &Arc<Self>, cost: usize, task: Box<dyn FnOnce() + Send>) {
        // Fast path: atomically reserve capacity and start immediately.
        if self.try_reserve(cost) {
            self.spawn_task(cost, task);
            return;
        }
        // Slow path: queue the task, then drain any that now fit.
        // Tasks are collected while holding the lock, then spawned
        // after releasing it to avoid holding the state mutex during
        // pool creation.
        let to_spawn = {
            let mut state = self.state.lock().unwrap();
            state.queue.push_back(PendingTask { cost, task });
            self.drain_pending_locked(&mut state)
        };
        for PendingTask { cost, task } in to_spawn {
            self.spawn_task(cost, task);
        }
    }

    /// Spawn a task on a rayon pool.
    ///
    /// The caller must have already reserved `cost` units in `used`
    /// via `try_reserve`. This method does NOT increment `used` —
    /// the reservation is already accounted for.
    fn spawn_task(self: &Arc<Self>, cost: usize, task: Box<dyn FnOnce() + Send>) {
        let pool = self.get_or_create_pool(cost);
        let pm = Arc::clone(self);
        let closure_pool = Arc::clone(&pool);
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
    /// Must be called while holding the `state` lock. Returns a vec of
    /// tasks that were successfully reserved, with their queue entries
    /// removed. The caller should drop the state lock before spawning
    /// these tasks to avoid holding the mutex during pool creation.
    fn drain_pending_locked(self: &Arc<Self>, state: &mut PoolState) -> Vec<PendingTask> {
        let mut to_spawn = Vec::new();
        while let Some(pending) = state.queue.front() {
            if self.try_reserve(pending.cost) {
                to_spawn.push(state.queue.pop_front().unwrap());
            } else {
                break;
            }
        }
        to_spawn
    }

    fn on_task_completed(self: &Arc<Self>, completed_cost: usize, pool: Arc<rayon::ThreadPool>) {
        debug!("[on_task_completed] cost={}", completed_cost);

        // Free the capacity held by this task.
        self.used.fetch_sub(completed_cost, Ordering::SeqCst);

        // Return the pool to the cache for reuse before draining so
        // that drained tasks needing the same pool size can reuse it
        // instead of creating a new one.
        {
            let mut cache = self.pool_cache.lock().unwrap();
            cache.entry(completed_cost).or_default().push(pool);
        }

        // Drain queued tasks that now fit within capacity. Capacity
        // has been freed by the fetch_sub above, so try_reserve may
        // now succeed for waiting tasks. Tasks are collected under
        // the lock and spawned after releasing it.
        let to_spawn = {
            let mut state = self.state.lock().unwrap();
            self.drain_pending_locked(&mut state)
        };
        for PendingTask { cost, task } in to_spawn {
            self.spawn_task(cost, task);
        }
    }
}
