//! Variable-ring intern table.
//!
//! ark-gb's `Ring<F, W>` packs each variable into a fixed byte slot whose
//! offset depends on `nvars` at construction time. Adding a variable
//! invalidates every previously-packed monomial. To bridge that against
//! Zippel's `PRef`-keyed sparse polynomials (where new variables can appear
//! at any time during graph construction), we keep an intern table here and
//! defer constructing the underlying `Ring` until the first time we need to
//! materialise into ark-gb form.
//!
//! See the module-level docs in [`super`] for the full design.

use crate::pref::PRef;
use ark_ff::Field;
use ark_gb::ring::Ring;
use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use super::W;

/// PRef ↔ ark-gb variable-index interner plus a lazily-built `Ring<F, W>`.
///
/// Cloning is cheap (`Arc`-shared internals).
#[derive(Debug, Clone)]
pub struct VarRing<F: Field + Copy + Send + Sync> {
    inner: Arc<VarRingInner<F>>,
}

#[derive(Debug)]
struct VarRingInner<F: Field + Copy + Send + Sync> {
    /// PRef → dense u32 index. `Mutex` because new vars can appear during
    /// construction; finalised once `ring` is initialised.
    pref_to_idx: std::sync::Mutex<HashMap<PRef, u32>>,
    /// idx → PRef. Same Mutex protocol.
    idx_to_pref: std::sync::Mutex<Vec<PRef>>,
    /// Materialised ark-gb ring. Built lazily on first `ring()` call.
    /// Once built, `pref_to_idx` and `idx_to_pref` are frozen — adding a new
    /// variable after this point is a programming error.
    ring: OnceLock<Arc<Ring<F, W>>>,
}

impl<F: Field + Copy + Send + Sync> VarRing<F> {
    /// Create an empty interner.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(VarRingInner {
                pref_to_idx: std::sync::Mutex::new(HashMap::new()),
                idx_to_pref: std::sync::Mutex::new(Vec::new()),
                ring: OnceLock::new(),
            }),
        }
    }

    /// Intern a `PRef`, returning its dense u32 index.
    ///
    /// Panics if called after [`Self::ring`] has materialised — by that point
    /// the variable count is locked in for the underlying `Ring`.
    pub fn intern(&self, _p: &PRef) -> u32 {
        unimplemented!("VarRing::intern — implemented in P2")
    }

    /// Look up the index for an already-interned `PRef`. `None` if absent.
    pub fn get(&self, _p: &PRef) -> Option<u32> {
        unimplemented!("VarRing::get — implemented in P2")
    }

    /// Reverse map: dense index → `PRef`. `None` if out of range.
    pub fn pref_of(&self, _idx: u32) -> Option<PRef> {
        unimplemented!("VarRing::pref_of — implemented in P2")
    }

    /// Number of variables interned so far.
    pub fn nvars(&self) -> u32 {
        self.inner
            .idx_to_pref
            .lock()
            .expect("VarRing mutex poisoned")
            .len() as u32
    }

    /// Materialise (or return) the ark-gb `Arc<Ring<F, W>>`.
    ///
    /// Freezes the variable set: subsequent [`Self::intern`] calls panic.
    pub fn ring(&self) -> Arc<Ring<F, W>> {
        self.inner
            .ring
            .get_or_init(|| {
                let n = self.nvars().max(1);
                Arc::new(
                    Ring::<F, W>::new(n)
                        .expect("VarRing nvars exceeds ark-gb cap (W*8 - 1)"),
                )
            })
            .clone()
    }
}

impl<F: Field + Copy + Send + Sync> Default for VarRing<F> {
    fn default() -> Self {
        Self::new()
    }
}
