-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Nc

@[expose] public section

/-! # The length loads of warpgroup 0 read words

The `.nc` reads at pcs 168 and 181 return the four bytes of the lane's row of the top-k length
array and of the extra length array (`Pre.paramTopkLen`, `paramExtraTopkLen`: the bytes are the
launch content), so they rebuild to a word. Only the lane's events before the read are assumed
to be no undefined behaviour. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A length load's bytes rebuild to a word** (pcs 168 and 181). -/
theorem wg0_len_word_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} (hal : LaneUbFree X g k) {e : Event}
    (he : X.get (g, k) = some e) (hat : Wg0At L g e.pc) (hpc : e.pc = 168 ∨ e.pc = 181)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs) :
    ∃ v, rebuild 3 bs = .ok v := by
  have hrow := (ctaid_lt hp g).2
  rcases wg0_nc_reads_pre hp hX hFw hal he hat hk with
    ⟨x, hx, h156, hr⟩ | ⟨x, hx, -, hr⟩ | ⟨x, hx, -, hr⟩
  · omega
  · have hm := hp.paramTopkLen
    rw [hx] at hm
    obtain ⟨-, -, hmem⟩ := hm
    exact ⟨_, rebuild_word hX he hr fun j hj => (hmem _ hrow j hj).1⟩
  · have hm := hp.paramExtraTopkLen
    rw [hx] at hm
    obtain ⟨-, -, hmem⟩ := hm
    exact ⟨_, rebuild_word hX he hr fun j hj => (hmem _ hrow j hj).1⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
