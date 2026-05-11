use crossbeam_channel as channel;
use petgraph::graph::NodeIndex;

// ---------------------------------------------------------------------------
// SyncSender / SyncReceiver — MPSC channel for sync (sponge-requiring) nodes
// ---------------------------------------------------------------------------

/// Messages sent through the sync channel.
///
/// Each node message carries a sender clone so that the receiver
/// (main thread) can keep the channel alive while processing the
/// node.  When all sender clones are dropped — meaning no pool
/// tasks remain — the channel closes and `pop()` returns `None`,
/// signalling that the pool is idle.
pub struct SyncMessage {
    /// A sync node ready for sequential sponge processing,
    /// together with a sender clone that keeps the channel open
    /// until the node has been consumed.
    pub node_idx: NodeIndex,
    pub tx: SyncSender,
}

/// Sender half of the sync channel.
///
/// Held by pool tasks (and the main thread when it needs to push
/// sync nodes).  Cloning creates a new sender that shares the
/// same underlying channel, so every clone keeps the channel open.
#[derive(Clone)]
pub struct SyncSender {
    tx: channel::Sender<SyncMessage>,
}

impl SyncSender {
    /// Push a sync node onto the queue.
    ///
    /// The node is sent together with a clone of the sender so that
    /// the channel stays open until the receiver has consumed it.
    /// Safe to call from any thread.
    pub fn push(&self, node_idx: NodeIndex) {
        self.tx
            .send(SyncMessage {
                node_idx,
                tx: SyncSender {
                    tx: self.tx.clone(),
                },
            })
            .ok();
    }
}

/// Receiver half of the sync channel.
///
/// Held exclusively by the main thread.  Only stores the `rx`
/// handle; no sender clones are kept here.  When all senders
/// (including those embedded in in-flight `Node` messages) have
/// been dropped, the channel closes and `pop()` returns `None`,
/// signalling that no pool tasks remain.
pub struct SyncReceiver {
    rx: channel::Receiver<SyncMessage>,
}

impl SyncReceiver {
    /// Pop a sync node from the queue.
    ///
    /// Blocks until a node is available or the channel closes.
    /// Returns `None` when the channel is closed, which means no
    /// pool tasks remain and no more sync nodes will arrive.
    ///
    /// The sender clone carried by each `SyncMessage` is returned
    /// to the caller (the main thread) and stays alive for the
    /// duration of sync-node processing.  When the caller finishes
    /// processing the node and drops the `SyncMessage` (or moves
    /// the `tx` into successor pushes), the sender clone is
    /// released.  This keeps the channel open during processing,
    /// which matters because:
    ///
    /// * Every running pool task holds its own `SyncSender` clone
    ///   for the entire lifetime of the task, so the channel stays
    ///   open as long as any task is running.
    ///
    /// * Messages already buffered in the channel are delivered
    ///   before `RecvError` even after all senders are dropped, so
    ///   no sync nodes are lost when the last task finishes.
    pub fn pop(&self) -> Option<SyncMessage> {
        self.rx.recv().ok()
    }
}

/// Create a new sync channel.
///
/// Returns a `(SyncSender, SyncReceiver)` pair.  The sender can be
/// cloned and shared across threads; the receiver should be kept on
/// the main thread.
pub fn sync_channel(n: usize) -> (SyncSender, SyncReceiver) {
    let (tx, rx) = channel::bounded(n);
    (SyncSender { tx }, SyncReceiver { rx })
}
