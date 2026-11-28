-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Rescale
public import Kernels.InklingRelDecode.Proof.Lib.RescaleWord
public import Kernels.InklingRelDecode.Proof.Lib.RescaleSkip
import Lemmas.Flow.MinSwap
import Lemmas.Flow.Step.RuleStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof PTX.Assumption

private theorem minWord_comm (x y : Value) : Lib.minWord x y=Lib.minWord y x := by
  unfold Lib.minWord
  rcases h : MinCore.minE [x,y] with e | v
  · rcases h' : MinCore.minE [y,x] with e' | v'
    · rfl
    · exact absurd ((MinCore.minE_comm y x v').1 h') (by simp [h])
  · rw [(MinCore.minE_comm x y v).1 h]

private theorem skip_comm (a b : Value) :
    ((MinCore.minE [a,b]).bind fun m =>
        setpE (.unord .ge) false m (b32 1065353216)).toOption.getD false =
      ((MinCore.minE [b,a]).bind fun m =>
        setpE (.unord .ge) false m (b32 1065353216)).toOption.getD false := by
  rcases h : MinCore.minE [a,b] with e | v
  · rcases h' : MinCore.minE [b,a] with e' | v'
    · rfl
    · exact absurd ((MinCore.minE_comm b a v').1 h') (by simp [h])
  · rw [(MinCore.minE_comm a b v).1 h]

/-- The compare at pc 2257 gives every lane of a four-lane group the same answer: the first
exchange pairs the words `{0,2}` and `{1,3}`, the second combines the two pair minima in either
order, and `min.f32` is symmetric in its sources whatever their values (NaN included). -/
theorem rescale_four {L g g'} (w : Nat → Value) {j : Nat} (hj : j<4) :
    skipRescale L g (Lib.minWord (w j) (w (j ^^^ 2)))
      (Lib.minWord (w (j ^^^ 1)) (w ((j ^^^ 1) ^^^ 2))) =
    skipRescale L g' (Lib.minWord (w 0) (w 2)) (Lib.minWord (w 1) (w 3)) := by
  rw [skipRescale_eq,skipRescale_eq (L := L) (g := g')]
  rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3) with rfl|rfl|rfl|rfl <;>
    simp only [Nat.reduceXor]
  all_goals first
    | exact skip_comm _ _
    | (rw [minWord_comm (w 2) (w 0),minWord_comm (w 3) (w 1)]; done)
    | (rw [minWord_comm (w 3) (w 1),minWord_comm (w 2) (w 0)]; exact skip_comm _ _)

set_option maxRecDepth 10000 in
/-- The decision does not depend on the lane. -/
theorem skip_free (L : Launch) (g : Nat) (sent recv : Value) :
    skipRescale L g sent recv=Lib.rescaleSkip L sent recv := by
  rw [skipRescale_eq]
  have : skipRescale L 0 sent recv=Lib.rescaleSkip L sent recv := by
    unfold skipRescale Lib.rescaleSkip
    rfl
  rw [←this,skipRescale_eq]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
