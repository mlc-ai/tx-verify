-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Export.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Export.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Nc

@[expose] public section

/-! # The non-coherent reads of the kernel are allocated

A `.nc` read of a launched lane is its role's: warpgroup 0's (`wg0_ncAlloc`), the MMA warp's
(`mma_ncAlloc`), the TMA warp's (`tma_ncAlloc`), the index warp's (`index_ncAlloc`) or warpgroup
2's (`dequant_ncAlloc`) or the idle code's (`wg1_ncAlloc`); the startup makes none. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every `.nc` read covers allocated input bytes**. -/
theorem nc_alloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X)
    {g k : Nat} {e : Event} (he : X.get (g, k) = some e) {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .nc a bs) (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hg := Frame.lt_of_get hX he
  have hm : MemRow.MemEvent e := .inr (.inl ⟨a, bs, hk⟩)
  rcases (mem_rows hp hX hFw).place hg he hm with h | h | h | h | h | h | h
  · obtain ⟨a', hk', -⟩ := startup_mem_noMbar hp hX hFw hg he h hm
    rcases hk' with ⟨_, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;> cases h'
  · exact wg0_ncAlloc hp hX hFw hnu he h hk l hc
  · exact wg1_ncAlloc hp hX hFw he h hk l hc
  · exact mma_ncAlloc hp hX hFw he h hk l hc
  · exact tma_ncAlloc hp hX hFw he h hk l hc
  · exact index_ncAlloc hp hX hFw he h hk l hc
  · exact dequant_ncAlloc hp hX hFw he h hk l hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
