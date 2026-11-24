-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemLife
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings

@[expose] public section

/-! # What the thread layer exports for the memory regions and the statistics counts

The threads' own accesses of memory and their counts of statistics-barrier events, which the
protocols of the base word, the rings, the output and the statistics barriers take:

* **The threads' accesses** (`access_shared`, `access_low`): every memory access of a thread is a
  shared access (the kernel's only generic accesses are `ld.shared` and `st.shared`), below the
  ring regions (offset `68608`): the base word, the statistics words and the staging buffers.
* **The base word** (`base_write`, `base_written`, `base_read`): only warp 12 accesses the base
  word `+328`. Lane 0 writes it once, the four bytes of its allocation's address, as the event
  right after its allocation (PTX 714) and before its first event on barrier 2; every lane reads
  it after its `bar.sync 2` of ordinal 0 (PTX 715, 716).
* **The statistics counts** (`soft_stats_exit`, `corr_stats_sync`): every item makes
  `kvBlocks + 1` generations of each statistics barrier (an arrival of the softmax warp per credit
  poll, a `bar.sync` of the correction warp per load of the stage's word). At its exit a softmax
  thread has made them all for every item that passed the loop test; a correction thread's
  `bar.sync` on a statistics barrier is of such an item. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The thread layer's facts for the memory regions and the statistics counts. -/
structure OlderFacts (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- A thread's memory access is of shared memory. -/
  access_shared : ∀ {g k : Nat} {a : Acc} {w : Bool}, X.Access (g, k) a w →
    a.loc.space = .shared
  /-- A thread's access lies below the ring regions. -/
  access_low : ∀ {g k : Nat} {a : Acc} {w : Bool} {l : Loc}, X.Access (g, k) a w → a.Covers l →
    l.addr < L.sharedBase + 68608
  /-- A thread's write of a base-word byte is lane 0 of warp 12's write of its CTA's whole base
  word, four bytes, the event right after an allocation and before the thread's first event on
  barrier 2. -/
  base_write : ∀ {g k : Nat} {a : Acc} {bs : List Byte} {l : Loc}, X.Writes (g, k) a bs →
    a.Covers l → L.sharedBase + 328 ≤ l.addr → l.addr < L.sharedBase + 332 →
      g % L.block = 384 ∧ a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4 ∧ bs.length = 4 ∧
        barOrd X g k 2 = 0 ∧
        ∃ j pc grp dst n, k = j + 1 ∧
          X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩
  /-- Lane 0 of warp 12 writes its CTA's base word, four bytes, before its first event on
  barrier 2. -/
  base_written : ∀ {g i pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
    g % L.block = 384 → X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩ →
      ∃ k < i, ∃ a bs, X.Writes (g, k) a bs ∧ a.loc = baseLoc L (ctaOf L g) ∧ a.size = 4
  /-- A thread's read of a base-word byte is a thread of warp 12's, after its `bar.sync 2` of
  ordinal 0. -/
  base_read : ∀ {g k : Nat} {a : Acc} {bs : List (Option Byte)} {l : Loc}, X.Reads (g, k) a bs →
    a.Covers l → L.sharedBase + 328 ≤ l.addr → l.addr < L.sharedBase + 332 →
      warpOf L g = 12 ∧ ∃ b < k, Bar2Sync X g b 0
  /-- At its exit, a softmax thread has made `kvBlocks + 1` events on its statistics barrier for
  every item up to each one that passed the loop test. -/
  soft_stats_exit : ∀ {g k pc u : Nat}, g < L.threads → warpOf L g < 8 →
    X.get (g, k) = some ⟨pc, .exit⟩ → workOf L g u < totOf L →
      (kvBlocks P + 1) * (u + 1) ≤ barOrd X g k (warpOf L g + 3)
  /-- A correction thread's `bar.sync` on a statistics barrier is of an item that passed the loop
  test: it has fewer earlier events on the barrier than `kvBlocks + 1` per item up to that
  one. -/
  corr_stats_sync : ∀ {g j pc id : Nat} {cnt : Option Nat}, g < L.threads → 8 ≤ warpOf L g →
    warpOf L g < 12 → X.IsBarrier (g, j) id cnt pc → id ≠ 2 →
      ∃ u, workOf L g u < totOf L ∧ barOrd X g j id < (kvBlocks P + 1) * (u + 1)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
