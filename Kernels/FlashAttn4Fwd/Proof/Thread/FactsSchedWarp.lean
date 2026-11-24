-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedWarpQuiet

@[expose] public section

/-! # `Cross.WarpSched` from the roles' schedules

The warp collectives' schedule of all threads joins the schedules of the warps of each role
(`warpSchedG_union`, the role a function of the warp): the store and idle warps'
(`quietWarpSched`, proved), and the softmax, correction, MMA and loader warps', premises of
`warpSched` until their counts' inversions to the site tables are written (`WarpRoleSched`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A schedule of the warp collectives of the warps `G` selects (a role's warps). -/
def WarpRoleSched (L : Launch) (X : Execution) (G : Nat → Prop) : Prop :=
  ∃ S, WarpSchedG L X (fun g => G (warpOf L g)) S

theorem warp_lt (hpre : Pre P L mem0) (g : Nat) : warpOf L g < 16 := by
  unfold warpOf; rw [hpre.block]; omega

/-- **`Cross.WarpSched`** from the softmax, correction, MMA and loader warps' schedules. -/
theorem warpSched (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
    (hsoft : WarpRoleSched L X (· < 8)) (hcorr : WarpRoleSched L X (fun w => 8 ≤ w ∧ w < 12))
    (hmma : WarpRoleSched L X (· = 12)) (hload : WarpRoleSched L X (· = 14)) :
    ∃ S, WarpSched L X S := by
  obtain ⟨S1, h1⟩ := hsoft
  obtain ⟨S2, h2⟩ := hcorr
  obtain ⟨S3, h3⟩ := hmma
  obtain ⟨S4, h4⟩ := hload
  have h5 := quietWarpSched hpre hX ht hok
  refine ⟨_, WarpSchedG.toWarpSched (warpSchedG_union (Q := fun c : Nat × Nat => c.2 < 8)
    (h1.mono fun g h => h.2)
    (warpSchedG_union (Q := fun c : Nat × Nat => c.2 < 12) (h2.mono fun g h => ⟨?_, h.2⟩)
      (warpSchedG_union (Q := fun c : Nat × Nat => c.2 = 12) (h3.mono fun g h => h.2)
        (warpSchedG_union (Q := fun c : Nat × Nat => c.2 = 14) (h4.mono fun g h => h.2)
          (h5.mono fun g h => ?_)))))⟩
  · have := h.1.2; simp only [warpKey] at this; omega
  · have := warp_lt hpre g
    have := h.1.1.1.2; have := h.1.1.2; have := h.1.2; have := h.2
    simp only [warpKey] at *
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
