-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasReady
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadRendezvous
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.MBarrier Prologue Thread Thread.Loader

/-- The next Bias generation needs a return from a warp which synchronized
with every live participant. A live lane's total rendezvous count therefore
bounds the number of generations its physical ready object can have finished. -/
theorem biasFinalPhaseLeLaneRendezvous {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (stage : Fin 2) (member : warpIndex l g ∈ biasParticipants stage)
    (live : ¬ Exited X g) {s : State}
    (hs : stateBefore (X.objects (biasReadyObject l (g/l.block) stage))
      (X.objects (biasReadyObject l (g/l.block) stage)).length = some s) :
    s.phase ≤ (X.tr g).countP (Execution.isBarId (11+stage.val))+1 := by
  let n := (X.tr g).countP (Execution.isBarId (11+stage.val))
  change s.phase ≤ n+1
  by_contra! high
  obtain ⟨_,_,⟨issuer,i⟩,record,id,issued,atAge⟩ :=
    biasReadyExpectationOfCompletedPhase hp hX stage hs high
  have ordinal := biasExpectationPhaseLeOrdinal hp hX stage record id issued atAge
  obtain ⟨_,_,empty,_,poll,_,_,ok,_,seen,budget⟩ :=
    biasReuseGuardObserved hp hX stage issued (by omega)
  obtain ⟨ret,returned,owner,_,age,_⟩ := biasEmptyObservedReturnOfWarp hp hX stage 0 poll ok seen
  obtain ⟨k,idx,bar,retBudget⟩ := Scores.biasReturnRendezvousBudget hp hX stage returned
  obtain ⟨_,he⟩ := returned
  have passed : k+1 < (X.tr ret.1).length := idx ▸ len_of_get he
  obtain ⟨j,mode,⟨event,hGet,kind⟩,rank⟩ := memberBarrierArrival hX
    (biasBarrierSources hp hX stage) (biasBarrierShape hp stage) bar passed owner.symm member
    (fun exited => (live exited).elim)
  have marked : Execution.isBarId (11+stage.val) event = true := by simp [Execution.isBarId,kind]
  have next := countP_take_succ hGet marked
  have lower := countP_take_mono (Execution.isBarId (11+stage.val)) (X.tr g)
    (show j+1 ≤ (X.tr g).length from len_of_get hGet)
  rw [List.take_length,next] at lower
  change observedBarrierOrdinal X (g,j) (11+stage.val)+1 ≤ n at lower
  rw [rank] at lower
  change arrivals _ _ = empty at age
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
