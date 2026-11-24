-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReturnObservation
public import Lemmas.Kernel.ExitChain
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarRingRound
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

/-- An observer of the Bias completion in the owning CTA reaches its actual exit. -/
theorem biasNotificationFinishedOfObservation {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} {tensor wait : EvId}
    (hOwner : wait.1 / l.block = cta) (hExit : CtaExited l X cta)
    (hObserve : MbarObserved X (.async tensor (.notify .load)) (.thread wait)) :
    SharedFinished l kernel Assumptions.all X (.async tensor (.notify .load)) cta := by
  obtain ⟨hPresent,w,loc,acquire,scope,hEq,hWait,_⟩ := hObserve
  obtain rfl := Ref.thread.inj hEq
  obtain ⟨site,parity,hGet⟩ := hWait.1
  have hw := Step.CtaBar.thread_lt_of_get hX hGet
  obtain ⟨returnSite,hLast⟩ := hExit wait.1 hw hOwner
  let finish := ((X.tr wait.1).length-1)
  have hReturn : X.get (wait.1,finish) = some ⟨returnSite,.exit⟩ := by
    change (X.tr wait.1)[finish]? = _
    rwa [← List.getLast?_eq_getElem?]
  have hLen : wait.2 < (X.tr wait.1).length := (List.getElem?_eq_some_iff.mp hGet).1
  have hLt : wait.2 < finish := by
    by_contra! h
    have hSame : wait.2 = finish := by dsimp [finish] at *; omega
    have hEq : wait = (wait.1,finish) := Prod.ext rfl hSame
    rw [hEq,hReturn] at hGet
    cases hGet
  have hLater : finish < (X.tr wait.1).length := (List.getElem?_eq_some_iff.mp hReturn).1
  obtain ⟨branch,hSpin⟩ := actualCanonicalPoll hX hGet
  have hResume : Resumes kernel X wait (wait.1,finish) := Resumes.of_spin hGet hSpin rfl hLt hLater
  exact SharedFinished.of_completedBefore (finish := (wait.1,finish)) hPresent ⟨hw,hOwner,_,hReturn⟩
    (CompletedBefore.of_before hWait.before
      (Relation.TransGen.single (DepStep.of_resumes l hResume)))

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta i phase : Nat} (stage : Fin 2)
    {r : Record Ref} {old : EvId} (hi : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (hId : r.id = .async old (.notify .load)) (hAction : r.action = .completeTx 16384)
    (hPhase : phaseAt (X.objects (biasReadyObject l cta stage)) i = some phase) {g j : Nat}
    {half : Fin 2} {spec : TensorCopy.Spec} (hOwner : g / l.block = cta)
include hp hX stage hi hId hAction hPhase hOwner

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta i phase : Nat} (stage : Fin 2)
    {r : Record Ref} {tensor : EvId} (hi : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (hId : r.id = .async tensor (.notify .load)) (hAction : r.action = .completeTx 16384)
    (hPhase : phaseAt (X.objects (biasReadyObject l cta stage)) i = some phase) {g : Nat}
    (hCta : g/l.block = cta) (hWarp : Prologue.warpIndex l g < 8)
include hp hX stage hi hId hAction hPhase hCta hWarp

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
