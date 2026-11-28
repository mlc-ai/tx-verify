-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccPc

@[expose] public section

/-! # The block's sites stay in the block

A step of warpgroup 0's control machine from a site of the block (pc 566 to 1121) goes to a site of
pc at most 1122: the block ends at the softmax-ready arrival, never in the epilogue. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {c c' : D} {e : Event}

/-- **A step inside the block stays in the block** (pc at most 1122). -/
theorem succ_loop (h : succ P L g w c e = some (some c')) (h1 : 566 ≤ c.site.pc)
    (h2 : c.site.pc ≤ 1121) : c'.site.pc ≤ 1122 := by
  cases hs : c.site <;> simp only [hs, Site.pc] at h1 h2
  all_goals try (exfalso; omega)
  all_goals try (rename_i arm k; cases arm <;> fin_cases k <;> simp at h1; done)
  all_goals try (rename_i k; fin_cases k <;> simp at h2; done)
  all_goals try (rename_i cc k; fin_cases cc <;> simp [ost2Base] at h2 h1 <;> omega)
  case mst | bar2 | arrV | rsf | rsfb | fpx =>
    simp only [succ, hs] at h
    cases h
    simp [Site.pc]
  case mld =>
    simp only [succ, hs, dataRd] at h
    split at h <;> cases h <;> simp [Site.pc]
  case vote =>
    simp only [succ, hs] at h
    split at h <;> cases h
    simp [Site.pc]
  case ost k =>
    simp only [succ, hs, elemNext] at h
    split at h <;> cases h
    · have := k.isLt
      simp only [Site.pc]
      omega
    · rcases site_afterOst c with h | h <;> fin_cases k <;> simp [h, Site.pc]
  case rld k =>
    simp only [succ, hs, tcLoad] at h
    split at h <;> cases h
    fin_cases k <;> simp [Site.pc]
  case rldw k | rst k | rstw k =>
    simp only [succ, hs] at h
    cases h
    fin_cases k <;> simp [Site.pc]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
