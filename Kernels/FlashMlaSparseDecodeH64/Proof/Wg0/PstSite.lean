-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites

@[expose] public section

/-! # The site of a peer store's pc -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- The site at the pc of a peer store is that store's. -/
theorem site_pc_pst {s : Wg0.Site} {k : Nat} (hk : k < 8) (h : s.pc = 403 + 10 * k) :
    s = .pst ⟨k, hk⟩ := by
  by_cases hs : ∃ j, s = .pst j
  · obtain ⟨j, rfl⟩ := hs
    have := j.isLt
    simp only [Wg0.Site.pc] at h
    exact congrArg Wg0.Site.pst (Fin.ext (by simp only; omega))
  · exfalso
    cases s
    all_goals first
      | exact absurd ⟨_, rfl⟩ hs
      | (simp only [Wg0.Site.pc] at h; omega)
      | (rename_i j; fin_cases j <;> (simp [Wg0.Site.pc] at h; omega))
      | (rename_i a j; fin_cases a <;> fin_cases j <;>
          (simp [Wg0.Site.pc, Wg0.ost2Base] at h; omega))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
