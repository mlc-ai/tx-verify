-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollGen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.RefNext

@[expose] public section

/-! # The startup's sites at collectives

A startup state at a collective is at one of the two shuffles (pcs 6 and 9) or, on warp 0, at an
election; `sh_site`: off warp 0 it is at a shuffle. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {L : Launch} {x : Nat}

/-- The startup's sites at collectives. -/
theorem startup_coll_site {d : Startup.D} {sh : Nat} (hW : Startup.RefW L x d sh)
    (hc : d.site.pc ∈ collPcs) : (∃ j, d.site = .sh j) ∨ ∃ j, d.site = .elect j := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => exact .inl ⟨j, rfl⟩
  | elect j => exact .inr ⟨j, rfl⟩
  | init n => exact absurd hc (by simp only [Startup.Site.pc]; fin_cases n <;> decide)
  | enter q => exact absurd hc (by simp only [Startup.Site.pc]; cases q <;> decide)
  | _ => exact absurd hc (by simp [Startup.Site.pc]; decide)

theorem collPcs_lt : ∀ c ∈ collPcs, c < 2557 := by decide

/-- A collective startup state off warp 0 is at a shuffle. -/
theorem sh_site {d : Startup.D} {sh : Nat} (hw : warpOf L x ≠ 0)
    (hW : Startup.RefW L x d sh) (hc : d.site.pc ∈ collPcs) : ∃ j, d.site = .sh j := by
  rcases startup_coll_site hW hc with h | ⟨j, hj⟩
  · exact h
  · exfalso
    obtain ⟨site, x1, x2⟩ := d
    simp only at hj
    subst hj
    obtain ⟨-, -, -, this⟩ := hW
    simp only [warpOf, tidOf] at this hw
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
