-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Correction.Loads
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # The correction warps' shapes

The sites of this group: stage 0's rescale stores. One group of sites of `site_shape`, a file per
group so that each is checked in its own process (`Shapes.lean` dispatches). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_Rst0 (_hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : d.site ∈ [Site.rst 0 0, Site.rst 0 1, Site.rst 0 2, Site.rst 0 3, Site.rst 0 4,
      Site.rst 0 5, Site.rst 0 6, Site.rst 0 7]) :
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
