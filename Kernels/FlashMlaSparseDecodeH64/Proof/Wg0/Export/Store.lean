-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
public import Lemmas.Protocol.Region

@[expose] public section

/-! # Warpgroup 0's tensor stores: their footprints

An output tensor store of a lane of warpgroup 0 (chunk `c`, the lane's warp `w`) reads only the
8192 bytes at `65536 + 16384 w + wg0OutOff c` of the lane's CTA (`wg0_store_read`, from the O
map's box `wg0_tensorStore_slot`), all of them below the mbarriers (`wg0_store_below`); it writes
global memory only (`store_writeLoc_global`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The source box of an output tensor store**: byte `(x, y, j)` of chunk `c`'s store of a lane
of warpgroup 0 is read from the 8192 bytes at `65536 + 16384 w + wg0OutOff c` of its CTA. -/
theorem wg0_store_read (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.Wg0At L g e.pc) {a : Nat} {s : TensorStore.Spec}
    (hk : e.kind = .tensorStore a s) {x y j : Nat} {l : Loc}
    (hl : TensorStore.readLoc s x y j = some l) :
    ∃ c < 4, e.pc = [1358, 1516, 1673, 1831].getD c 0 ∧ l.space = .shared ∧
      l.cta = g / L.block ∧
      L.sharedBase + (65536 + 16384 * MbarRow.warp L g + MemRow.wg0OutOff c) ≤ l.addr ∧
      l.addr < L.sharedBase + (65536 + 16384 * MbarRow.warp L g + MemRow.wg0OutOff c) + 8192 := by
  obtain ⟨c, hc, hpc, hslot⟩ := wg0_tensorStore_slot hp hX hFw he hat hk
  unfold TensorStore.readLoc at hl
  obtain ⟨slot, -, rfl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨h, hh, q, hq, el, hel, b, hb, hloc⟩ := hslot slot
  have hx := MemRow.swz_lt (t := h) hq
  rw [hloc]
  refine ⟨c, hc, hpc, rfl, rfl, ?_, ?_⟩ <;> simp only [wsLoc] <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
