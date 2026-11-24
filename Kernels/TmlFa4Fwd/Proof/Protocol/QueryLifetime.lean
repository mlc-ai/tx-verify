-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedQueryOperand
import Kernels.TmlFa4Fwd.Proof.Thread.QueryLifetime
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread

/-- Every actual Q input transfer has notified before its owner CTA exits. The successful
query acquire enables an initial MMA that the correction role's final output wait observes. -/
theorem queryNotificationFinishedAtExit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {input : EvId}
    {stage plane : Fin 2} {spec : TensorCopy.Spec}
    (hBox : Loader.QuerySubbox p l X input stage plane spec)
    (hExit : CtaExited l X (input.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async input (.notify .load))
      (input.1 / l.block) := by
  have hGrid : input.1 / l.block < l.grid := by
    obtain ⟨_, he⟩ := hBox.1
    exact NamedBar.cta_lt (PTX.Proof.event_thread_lt hX he)
  obtain ⟨wait, e, finish, hOwner, he, hk, hFinish, hPath⟩ :=
    queryAcquireEnablesExit hp hX hGrid (hBox.active hp hX hCuQ) hExit stage
  obtain ⟨hAcquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e, he, hk⟩
  obtain ⟨tensor, s, hSame, hOtherBox, hNote⟩ :=
    hAcquire.observedSubbox hp hX hPhase plane
  have hSameInput := Loader.querySubboxUnique hp hX (hOwner.symm.trans hSame.symm) hBox hOtherBox
  subst tensor
  obtain ⟨_, _, ⟨rfl, o, _, ho, _, _, hNoteDone⟩, hUpdate⟩ :=
    hAcquire.observesTensor hp hX hOwner.symm hPhase hNote
  exact SharedFinished.of_completedBefore ⟨o, ho, hNoteDone⟩ hFinish
    (CompletedBefore.of_before hUpdate.before hPath)

end PTX.Kernels.TmlFa4Fwd.Protocol
