-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Index
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexLive
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Addr

@[expose] public section

/-! # The index warp's memory accesses

`memRow_index` (`MemRow.Index`): from the shape table (`Index/Ev.lean`, through `ev_at` and
`index_state`), case by site; the store words are workspace offsets by `Index/Addr.lean`, the
element of a pair below 2 (`ix_ok`). The consumers' fact `ix_mem_noMbar`: no access of the index
warp covers an mbarrier's bytes (the index part of `bytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A memory event is no undefined behaviour. -/
private theorem memEvent_ub {e : Event} (hm : MemRow.MemEvent e) : ∀ f, e.kind ≠ .ub f := by
  rcases hm with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, o, n, h⟩ <;> intro f hf <;>
    rw [h] at hf <;> cases hf

/-- **Row `MemRow.Index`**. -/
theorem memRow_index (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Index P L X := by
  intro g k e _ he hat hm
  obtain ⟨-, hr1, hr2⟩ := hat
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (memEvent_ub hm)
  obtain ⟨d, n, rfl, -, ⟨-, hE⟩, -⟩ := index_state hJ hi hev hpc ⟨hr1, hr2⟩
  obtain ⟨site, el, ac, c'⟩ := d
  obtain ⟨-, hel, -⟩ := ix_ok hp hX hσ _ n rfl
  have hpl := Index.pair_loc (g := g) hp c'
  have hbl := Index.byte_loc (g := g) hp c'
  simp only [tidOf] at hpl hbl
  obtain ⟨pc, kd⟩ := e
  rcases hm with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ <;>
    cases site <;> simp [Index.EvK, Index.NcEv, Index.NcAt, Index.PollEv, Index.ShflEv,
        Index.StoreEv] at hE ⊢
  all_goals
    obtain ⟨hl, hsz⟩ := hE
    simp only [IxSite.elems] at hel
  · exact .inl ⟨c'.slot.val, c'.slot.isLt, el, hel, by
      rw [hl, hpl]; simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]; omega, hsz⟩
  · exact .inr ⟨c'.slot.val, c'.slot.isLt, by rw [hl, hbl]; simp [wsLoc, Loc.at], hsz⟩
  · exact .inl ⟨c'.slot.val, c'.slot.isLt, el, hel, by
      rw [hl, hpl]; simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]; omega, hsz⟩
  · exact .inr ⟨c'.slot.val, c'.slot.isLt, by rw [hl, hbl]; simp [wsLoc, Loc.at], hsz⟩

/-- **No access of the index warp covers an mbarrier's bytes** (the index part of `bytes`): it is
a non-coherent read, or a shared write that ends at or below the first mbarrier of the lane's
CTA. -/
theorem ix_mem_noMbar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hat : MbarRow.IndexAt L g e.pc) (hm : MemRow.MemEvent e) :
    (∃ a bs, e.kind = .nc a bs) ∨ ∃ a : Acc, (∃ bs, e.kind = .wr a bs) ∧
      a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  rcases memRow_index hp hX hFw hg he hat hm with h | ⟨a, bs, hk, h⟩
  · exact .inl h
  · exact .inr ⟨a, ⟨bs, hk⟩, MemRow.ixWr_below h⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
