-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites

@[expose] public section

/-! # The site of a score load's pc -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

/-- The site at the pc of a score load is one of the four loads. -/
theorem site_sld_of_pc (s : Site)
    (h : s.pc = 278 ∨ s.pc = 280 ∨ s.pc = 283 ∨ s.pc = 285) :
    s = .sld false 0 ∨ s = .sld false 1 ∨ s = .sld true 0 ∨ s = .sld true 1 := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
