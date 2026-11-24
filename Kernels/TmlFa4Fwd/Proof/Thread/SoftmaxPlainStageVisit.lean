-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLoopTransitions

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Thread Correction

/-- A warp at the heads of the same repeated plain visit, whose score is ready for waiting
lanes, reaches the correction join in one history with the same traces. -/
theorem warpPlainJoinsOfHeads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {lead : Nat} (hLead : warpIndex l lead < 8)
    (visit tc bars elects : Nat) (counter : Nat → Nat) (maximum : Nat → Option ℝ)
    (sum : Nat → ℝ)
    (heads : ∀ g, SameWarp l lead g → PlainLoopAt p l X g (warpOf l lead) 6661 visit (counter g)
      tc bars elects (maximum g) (sum g))
    (hScore : ∀ g, SameWarp l lead g →
      okPolls (Scores.scoreReadyObject l (g/l.block) (stageOf (warpOf l lead))) (X.tr g) =
        visit →
      OpeningPollReady X (Scores.scoreReadyObject l (g/l.block) (stageOf (warpOf l lead)))
        (visit%2)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      ∀ g (hw : SameWarp l lead g), ∃ start,
        ∃ J : PlainVisitJoin p l X Y g (warpOf l lead) visit start (counter g) tc bars elects
          (maximum g) (sum g),
          (heads g hw).cursor.pos < J.join.cursor.pos ∧ (heads g hw).cursor.pos ≤ start := by
  classical
  have hWarp (g : Nat) (hw : SameWarp l lead g) : (warpOf l lead).val = warpIndex l g := by
    rw [warpOf_val hLead]; exact hw.2
  have returned (g : Nat) (hw : SameWarp l lead g) :=
    (heads g hw).scoreReturnedOfPending hp hMax hw.1.2.1 (hWarp g hw) (hScore g hw)
  let R (g : Nat) (hw : SameWarp l lead g) := Classical.choice (returned g hw)
  obtain ⟨Y,hY,hTrace,hObjects,joins⟩ := warpPlainJoinOfReturned hp hMax frame (warpOf l lead)
    (warpOf_val hLead).symm visit tc bars elects counter maximum sum R
  refine ⟨Y,hY,hTrace,hObjects,?_⟩
  intro g hw
  obtain ⟨J⟩ := joins g hw
  refine ⟨_,J,?_,?_⟩
  · apply lt_of_tcCount_lt (X := X)
    have hHead := (heads g hw).counts.1
    have hJoin := J.counts.1
    rw [hTrace] at hJoin
    rw [hHead,hJoin]
    omega
  · apply Nat.le_of_lt
    apply lt_of_countP_take_lt (X := X) (mark := scoreAcquired)
    rw [(heads g hw).counts.2.2.2.2.2,(R g hw).counts.2.2.2.2.2]
    omega

end PTX.Kernels.TmlFa4Fwd.Softmax
