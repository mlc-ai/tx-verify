-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasFirstVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasRendezvous
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReturnObservation
import Lemmas.Order.WaitOrderObject

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.AsyncCopy PTX.MBarrier Softmax Thread.Scores Thread.Loader Prologue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A selected lane's first Bias wait observes the opening box pair.
A reused pair needs the same lane's first rendezvous, following this wait. -/
theorem firstBiasAcquirePhaseZeroInPrefix (hCuQ : Epilogue.DrainCuQProtected p X) {g wait : Nat}
    {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hWarp : warpIndex l g < 8) :
    FirstBiasAcquirePhase l X g wait stage 0 := by
  obtain ⟨phase,_,hSeen⟩ := firstBiasAcquirePhase hp hX hWait
  have hZero : phase = 0 := by
    by_contra! hNonzero
    obtain ⟨n,r,hr,hId,hPhase⟩ := hSeen
    obtain ⟨j,poll,hRecord,hPollId,_,_,hOk⟩ := hWait.pollRecord hp hX
    have hSame := ObjectInit.checked_record_index_eq (X.objects_checked hX (waitLoc l g stage 2))
      hr hRecord (hId.trans hPollId.symm)
    subst n
    obtain rfl := Option.some.inj (hRecord.symm.trans hr)
    obtain ⟨tensor,spec,hOwner,hBox,hOrdinal,hNotify⟩ :=
      biasReadyObservedHalfOwner hp hX stage (0 : Fin 2) hr hOk hPhase
    rw [hId] at hNotify
    obtain ⟨loader,index⟩ := tensor
    have hReused : 0 < biasTensorOrdinal l X stage (0 : Fin 2) (loader,index) := by omega
    obtain ⟨empty,k,hEmpty,_,_,_,hObserve,hResume⟩ :=
      biasTensorReuseOfConsumerWarp hp hX (0 : Fin 4) hBox hReused
    have hCircuit := hWait.beforeBiasReturnInPrefix hp hX hCuQ hWork hWarp
      (hOwner ▸ hEmpty)
    have hBefore := (hCircuit.tail (DepStep.of_witness l (Witness.of_mbarObserved hObserve))).tail
      (DepStep.of_resumes l hResume)
    have hAfter := biasNotificationAfterIssue hX hBox hNotify.1
    exact hX.depAcyclic _
      ((hBefore.trans hAfter).tail (DepStep.of_witness l (Witness.of_mbarObserved hNotify)))
  exact hZero ▸ hSeen

/-- Every half of the observed opening generation is an actual loader subbox,
with its precise source identity retained for the word ordering proof. -/
theorem firstBiasAcquiredHalfInPrefix (hCuQ : Epilogue.DrainCuQProtected p X) {g wait : Nat}
    {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hWarp : warpIndex l g < 8) (half : Fin 2) :
    ∃ tensor o, AcquiredBiasBox p l X stage g wait tensor half o ∧
      biasTensorOrdinal l X stage half tensor = 0 := by
  have hZero := firstBiasAcquirePhaseZeroInPrefix hp hX hCuQ hWait hWork hWarp
  obtain ⟨i,current,hi,hId,hPhase⟩ := hZero
  have hPhaseZero : FirstBiasAcquirePhase l X g wait stage 0 := ⟨i,current,hi,hId,hPhase⟩
  obtain ⟨j,poll,hj,hPoll,_,_,hOk⟩ := hWait.pollRecord hp hX
  let loc := waitLoc l g stage 2
  have hIndex := ObjectInit.checked_record_index_eq (X.objects_checked hX loc) hj hi
    (hPoll.trans hId.symm)
  subst j
  obtain rfl := Option.some.inj (hj.symm.trans hi)
  obtain ⟨tensor,spec,hSub,hOrd,hNotify⟩ :=
    biasReadyObservedHalf hp hX stage half hi hOk hPhase
  rw [hId] at hNotify
  obtain ⟨n,j,r,record,q,hr,hNotifyId,hClean,hRecord,hJ,_,_,_,hN,hP,_⟩ :=
    (hWait.ownObservation hNotify).2
  have hj := ObjectInit.checked_record_index_eq (X.objects_checked hX loc) hRecord hi
    (hJ.trans hId.symm)
  subst j
  rw [hPhase] at hP
  obtain rfl := Option.some.inj hP
  have hNote : BiasNotifyPhase l X g stage 0 tensor := ⟨n,r,hr,hNotifyId,hClean,hN⟩
  obtain ⟨actual,o,hAcquired⟩ := acquiredBiasBoxOfNotification hp hX hWait hPhaseZero hNote
  obtain ⟨_,hGet⟩ := hSub.1
  obtain ⟨_,hSeen⟩ := hAcquired.issue
  have hSpec := (Kind.tensorIssue.inj (congrArg Event.kind
    (Option.some.inj (hGet.symm.trans hSeen)))).2
  have hShared := hAcquired.destination
  rw [← hSpec,hSub.2.2.1] at hShared
  have hAddr := congrArg Loc.addr hShared
  have hHalf : actual = half := Fin.ext (by
    change l.sharedBase+(166912+32768*stage.val+16384*half.val) =
      biasBoxStart l stage actual.val at hAddr
    unfold biasBoxStart at hAddr
    omega)
  exact ⟨tensor,o,hHalf ▸ hAcquired,hOrd⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
