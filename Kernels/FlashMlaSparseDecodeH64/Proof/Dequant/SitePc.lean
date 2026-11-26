-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Sites

@[expose] public section

/-! # Warpgroup 2's sites below pc 2695

The set-up's sites and the block's two waits are the only sites below pc 2695 (`small_site`); for
the role's time exports (`Dequant/Export/Time.lean`, `Dequant/Export/Wait.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant

/-- A site below pc 2695 is one of the set-up's or the block's two waits. -/
theorem small_site {s : Site} (h : s.pc < 2695) :
    s = .smr ∨ s = .lenA ∨ s = .lenB ∨ s = .wq ∨ s = .wraw ∨ s = .wsv := by
  cases s with
  | scale r => have := r.isLt; simp only [Site.pc, rowBase] at h; omega
  | raw r i =>
    have := r.isLt; have := i.isLt
    simp only [Site.pc, rowBase] at h
    split_ifs at h <;> omega
  | store r i =>
    have := r.isLt; have := i.isLt
    simp only [Site.pc, rowBase] at h
    split_ifs at h <;> omega
  | smr | lenA | lenB | wq | wraw | wsv => simp
  | _ => simp [Site.pc] at h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
