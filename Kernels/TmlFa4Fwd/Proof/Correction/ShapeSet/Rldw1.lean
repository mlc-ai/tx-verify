-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The correction warps' shapes

The sites of this group: the implicit waits of stage 1's rescale loads. One group of sites of
`site_shape`, a file per group so that each is checked in its own process (`Shapes.lean`
dispatches). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_Rldw1 (_hp : Pre p L m) (d : D) (hk : d.k = 1)
    (hs : d.site ∈ [Site.rldw 1 0, Site.rldw 1 1, Site.rldw 1 2, Site.rldw 1 3, Site.rldw 1 4,
      Site.rldw 1 5, Site.rldw 1 6, Site.rldw 1 7]) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  dsimp only at hs
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try dsimp only [Fin.reduceFinMk, Fin.isValue]
  · corr_step
  · corr_step
  · corr_step
  · corr_step
  · corr_step
  · corr_step
  · corr_step
  · corr_step

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
