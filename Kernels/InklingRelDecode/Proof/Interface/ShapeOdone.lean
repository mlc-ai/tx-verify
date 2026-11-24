-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Thread.ShapeSmWait
public import Kernels.InklingRelDecode.Proof.Safety.Barriers

@[expose] public section

/-!
# The `o_done` poll names `o_done`

`Safety.OdoneWait`, the one barrier operand without an event shape in the safety layer: at the
softmax region's `waitO` the event is a poll of `Bar.oDone` of the thread's CTA
(`Sm.shape_waitO`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Safety.OdoneWait`**: the softmax region's `o_done` poll names `o_done` of its CTA. -/
theorem odoneWait (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : Safety.OdoneWait Q L X := by
  intro g k pc q m ok acq sc d hσ hs he
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨ok', h⟩ := Sm.shape_waitO (ProA.sharedOk_of_pre hpre) (fired_sm hF) hs
  exact (Kind.wait.inj (Event.mk.inj h).2).1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
