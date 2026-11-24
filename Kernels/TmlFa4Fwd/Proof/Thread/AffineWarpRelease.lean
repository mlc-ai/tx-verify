-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AffineCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsRelease
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedNumeric

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {lead : Nat}
    (hWarp : Prologue.warpIndex l lead < 8) (mode : Repeated) (ordinal : Nat)
    (input : ∀ g, SameWarp l lead g → AffineCursor l X g mode.affineStart)
    (hNotice : ∀ g (hw : SameWarp l lead g),
      let i := (g,(input g hw).pos-1)
      Publishes X i (if mode = .biased then .biased else .plain) ∧
        (before X i).notices = ordinal)
include hp hMax hFrame hWarp mode ordinal input hNotice

/-- A single maximal history with the same traces resumes all reached affine
lanes of the warp, preserving their numerical states and continuation positions. -/
theorem resumeAffineWarpWithObjects :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      ∀ g (hw : SameWarp l lead g), ∃ u : OpeningTripCursor l Y g mode.affineStart [],
        u.pos = (input g hw).pos ∧ u.ready = (input g hw).ready ∧
        u.ending = (input g hw).ending := by
  classical
  let pos g := if hw : SameWarp l lead g then (input g hw).pos-1 else 0
  have hPos g (hw : SameWarp l lead g) : pos g = (input g hw).pos-1 := by
    simp only [pos,dite_eq_left hw]
  obtain ⟨Y,hY,hTrace,hObjects,hRelease⟩ :=
    statisticsWarpReleasedHistoryWithObjects hp hMax hFrame hWarp
    (if mode = .biased then .biased else .plain) ordinal pos (fun g hw => by
      simpa only [hPos g hw] using hNotice g hw)
  refine ⟨Y,hY,hTrace,hObjects,?_⟩
  intro g hw
  let c := input g hw
  have hReleased (hEnd : c.pos = (X.tr g).length) : Step.Released l Y g := by
    apply hRelease g hw
    rw [hPos g hw]
    have hPositive := c.positive
    change (input g hw).pos = _ at hEnd
    change 0 < (input g hw).pos at hPositive
    omega
  exact ⟨c.resume hTrace hReleased,rfl,rfl,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
