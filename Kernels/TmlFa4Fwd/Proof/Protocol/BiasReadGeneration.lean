-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReadOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasNotificationOrder
import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.AsyncCopy PTX.Flow PTX.MBarrier Thread Thread.Scores Thread.Loader Prologue

/-- An actual Bias word observes its exact stage rendezvous generation. A
higher phase would depend on the read's own downstream return credit. -/
theorem biasReadReadyPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {read : EvId} {repeated : Bool} {v : Fin 16} {a : Acc}
    {bytes : List (Option Byte)} (hRead : BiasVectorRead X read repeated v a bytes)
    (hWarp : warpIndex l read.1 < 8) (hStage : warpIndex l read.1/4 = stage.val)
    {wait index phase : Nat} {r : Record Ref}
    (hRecord : (X.objects (biasReadyObject l (read.1/l.block) stage))[index]? = some r)
    (hId : r.id = .thread (read.1,wait)) (hSuccess : r.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l (read.1/l.block) stage)) index =
      some phase)
    (hLower : observedBarrierOrdinal X read (11+stage.val) ≤ phase)
    (hBefore : TraceBefore X (read.1,wait) read) :
    phase = observedBarrierOrdinal X read (11+stage.val) := by
  by_contra hNe
  have hGreater : observedBarrierOrdinal X read (11+stage.val) < phase := by omega
  obtain ⟨tensor,box,hOwner,hBox,hOrdinal,hNotice⟩ :=
    biasReadyObservedHalfOwner hp hX stage (0 : Fin 2) hRecord hSuccess hPhase
  obtain ⟨g,j⟩ := tensor
  rw [hId] at hNotice
  have hLater : observedBarrierOrdinal X read (11+stage.val) <
      biasTensorOrdinal l X stage (0 : Fin 2) (g,j) := hOrdinal ▸ hGreater
  obtain ⟨ret,guard,hRet,hCta,_,hCount,hObserve,hResume⟩ :=
    biasTensorReuseOfConsumerWarp hp hX 0 hBox (by omega)
  have hEnough : observedBarrierOrdinal X read (11+stage.val) ≤
      arrivals (biasEmptyObject l (read.1/l.block) stage) ((X.tr ret.1).take ret.2) := by
    rw [hOwner] at hCount
    change arrivals (biasEmptyObject l (read.1/l.block) stage)
      ((X.tr ret.1).take ret.2) + 1 = _ at hCount
    omega
  obtain ⟨_,own,other,_,_,_,_,hOwn,hWitness,hPass⟩ :=
    biasReadReturnRendezvous hp hX stage hRead hWarp hStage (hOwner ▸ hRet)
      (hOwner.symm.trans hCta.symm) hEnough
  have hn := hNotice
  obtain ⟨_,_,_,acq,scope,hNoticeId,hWait,_⟩ := hn
  obtain rfl := Ref.thread.inj hNoticeId
  have hTrace : TraceBefore X (read.1,wait) (read.1,own) := by
    exact ⟨rfl,hBefore.2.1.trans hOwn.2.1,hOwn.2.2⟩
  have hOpened := biasAcquireResumes hX hWait hTrace
  have hPath := ((Relation.TransGen.single (DepStep.of_resumes l hOpened)).tail
    (DepStep.of_witness l hWitness)).tail (DepStep.of_resumes l hPass)
  have hReuse := (hPath.tail (DepStep.of_witness l (Witness.of_mbarObserved hObserve))).tail
    (DepStep.of_resumes l hResume)
  have hCycle := (hReuse.trans (biasNotificationAfterIssue hX hBox hNotice.1)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hNotice))
  exact hX.depAcyclic _ hCycle

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
