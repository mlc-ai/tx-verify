-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' shapes

The sites of this group: stage 0's final stores 8 to 15, half 0. One group of sites of `site_shape`,
a file per group so that each is checked in its own process (`Shapes.lean` dispatches). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_Fst010 (_hp : Pre p L m) (d : D)
    (hs : d.site ∈ [Site.fst 0 8 0, Site.fst 0 9 0, Site.fst 0 10 0, Site.fst 0 11 0,
      Site.fst 0 12 0, Site.fst 0 13 0, Site.fst 0 14 0, Site.fst 0 15 0]) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k⟩ := d
  dsimp only at hs
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try dsimp only [Fin.reduceFinMk, Fin.isValue]
  · corr_sst
  · corr_sst
  · corr_sst
  · corr_sst
  · corr_sst
  · corr_sst
  · corr_sst
  · corr_sst

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
