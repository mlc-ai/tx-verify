-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReturnObservation
import Kernels.TmlFa4Fwd.Proof.CtaMemoryOrder
import Kernels.TmlFa4Fwd.Proof.Thread.FirstBiasReadReuse
import Kernels.TmlFa4Fwd.Proof.Thread.WaitMode
import Lemmas.Order.OrderBaseCausality
import Lemmas.Protocol.PairTmaRing.Order
import Lemmas.Protocol.StagingHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX AsyncCopy MBarrier Thread.Loader
open PTX.Proof (event_thread_lt)

/-- The actual Bias completion observation uses an acquire at CTA scope. -/
theorem biasTensorObservedAtCTA {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i w : EvId}
    (hObs : MbarObserved X (.async i (.notify .load)) (.thread w)) :
    AsyncObserved X i (.notify .load) w true .cta := by
  obtain ⟨_,_,loc,acq,scope,hRef,hWait,_⟩ := hObs
  obtain rfl := Ref.thread.inj hRef
  obtain ⟨_,q,hEvent⟩ := hWait.1
  obtain ⟨n,j,r,poll,phase,hr,hId,_,_⟩ := hWait.2
  have hRecord := List.mem_of_getElem? hr
  have hVal := ((hX.tma.2.2.1 loc).2.1 r hRecord).1
  have hAction : ∃ tx, r.action = .completeTx tx := by
    cases record_source hX.tma.2.2.1 hRecord <;> first
    | exact ⟨_, ‹r.action = .completeTx _›⟩
    | grind
  obtain ⟨tx,htx⟩ := hAction
  rw [hId,htx] at hVal
  have hNotify : AsyncObserved X i (.notify .load) w acq scope := by
    obtain ⟨source,a,s,o,hLoad,hO,hObj,hDone,_⟩ :=
      PairTmaRing.tensorNotify_facts hVal
    obtain ⟨addr',source',hLoad'⟩ := (hX.tensor i o hO).1
    have hSpec : o.spec = s :=
      (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj
        (hLoad'.symm.trans hLoad)))).2
    exact ⟨_,loc,⟨rfl,o,addr',hO,⟨source',hLoad'⟩,hSpec ▸ hObj,hDone⟩,hWait⟩
  have hAcq := Thread.completionObservationAcquires hX hNotify
  have hScope := actualPollScope hX hEvent
  subst acq scope
  exact hNotify

private theorem observedTensorFinished {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i w : EvId} {x y byte : Nat}
    (hSame : SameCta l i.1 w.1)
    (hObs : MbarObserved X (.async i (.notify .load)) (.thread w)) :
    AsyncFinished l X i (.write (.load x y byte)) w := by
  have hObserved := biasTensorObservedAtCTA hX hObs
  exact .inr ⟨.cta,hObserved,MbarRing.Unit.Gate.scopesMeet hSame .cluster .cta⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {early later : EvId} {stage half : Fin 2}
    {s t : TensorCopy.Spec} (hEarly : BiasSubbox p l X early stage half s)
    (hLater : BiasSubbox p l X later stage half t) (hCta : early.1 / l.block = later.1 / l.block)
    (hOrd : biasTensorOrdinal l X stage half early < biasTensorOrdinal l X stage half later)
include hp hX hEarly hLater hCta hOrd

/-- The next use of a Bias half observes the previous generation's completed write.
The acquire-to-issue path extends to every subsequent use of the same half. -/
theorem biasModelWriteBeforeReuse {x y byte : Nat} {part : Part} {loc : Loc}
    (ha : AsyncCovers X early (.write (.load x y byte)) loc) (hb : AsyncCovers X later part loc) :
    modelCausality l X loc (.async early (.write (.load x y byte))) (.async later part) := by
  obtain ⟨g,index⟩ := later
  let n := biasTensorOrdinal l X stage half early + 1
  obtain ⟨next,hNext,sp,hBox,hNextOrd⟩ : ∃ j ≤ index, ∃ sp,
      BiasSubbox p l X (g,j) stage half sp ∧ biasTensorOrdinal l X stage half (g,j) = n := by
    by_cases hHere : biasTensorOrdinal l X stage half (g,index) = n
    · exact ⟨index,le_rfl,t,hLater,hHere⟩
    have hPrior : n < biasTensorOrdinal l X stage half (g,index) := by dsimp [n]; omega
    obtain ⟨j,hj,sp,hBox,hPhase⟩ := biasEarlierHalfOfOrdinal hp hX hPrior
    exact ⟨j,hj.le,sp,hBox,hPhase⟩
  have hPositive : 0 < biasTensorOrdinal l X stage half (g,next) := by
    rw [hNextOrd]
    dsimp [n]
    omega
  obtain ⟨ret,guard,hRet,hRetCta,_,hGeneration,hObs,hResume⟩ :=
    biasTensorReuseOfConsumerWarp hp hX 0 hBox hPositive
  obtain ⟨ready,pos,poll,hPoll,hPollId,hSuccess,hObserved,hRes⟩ :=
    biasReturnObservedReadyExact hp hX stage hRet
  obtain ⟨tensor,source,hTensorCta,hSource,hOrdinal,hSeen⟩ :=
    biasReadyObservedHalfOwner hp hX stage half hPoll hSuccess hObserved
  have hOrdinalEq : biasTensorOrdinal l X stage half tensor =
      biasTensorOrdinal l X stage half early := by
    change biasArrivalOrdinal X (biasEmptyObject l (g / l.block) stage) ret + 1 =
      biasTensorOrdinal l X stage half (g,next) at hGeneration
    rw [hNextOrd] at hGeneration
    dsimp [n] at hGeneration
    omega
  have hEarlyEq := biasTensorOrdinalInjective hp hX hSource hEarly
    (hTensorCta.trans hCta.symm) hOrdinalEq
  subst tensor
  rw [hPollId] at hSeen
  have hReuseObs := Thread.Scores.reuseWaitObservesAtCTA hp hX hBox hRet hObs
  obtain ⟨_,hEarlyGet⟩ := hEarly.1
  obtain ⟨_,hLaterGet⟩ := hLater.1
  have ⟨_,hReturnGet⟩ := hRet
  have hReadyThread : ret.1 < l.threads := event_thread_lt hX hReturnGet
  have hLoaderThread : g < l.threads := event_thread_lt hX hLaterGet
  have hEarlyThread : early.1 < l.threads := event_thread_lt hX hEarlyGet
  have hScope := MbarRing.Unit.Gate.scopesMeet
    (show SameCta l ret.1 g from ⟨hReadyThread,hLoaderThread,hRetCta⟩) .cta .cta
  have hOrderToRet : baseCausality l X (ret.1,ready) ret := .single (.inl
    (po_of_not_access hRes.1.1 hRes.1.2.1 hRes.1.2.2 (by rw [hReturnGet]; rfl)))
  have hLaterLen := (List.getElem?_eq_some_iff.mp hLaterGet).1
  have hOrderFromRet : baseCausality l X ret (g,index) :=
    Staging.baseCausality_of_handoff ⟨0,1,hRet⟩ hReuseObs hScope ⟨rfl,le_rfl⟩
      ⟨rfl,hResume.1.2.1.trans_le hNext,hLaterLen⟩
  have hA := observedTensorFinished (w := (ret.1,ready)) (x := x) (y := y) (byte := byte) hX
    ⟨hEarlyThread,hReadyThread,hCta.trans hRetCta.symm⟩ hSeen
  exact ⟨.inl ⟨hEarlyThread,hLoaderThread,hCta⟩,
    .direct ⟨ha,hb,.inl ⟨_,hA,hOrderToRet.trans hOrderFromRet⟩⟩⟩

/-- The next use of a Bias half observes the previous generation's completed write.
The acquire-to-issue path extends to every subsequent use of the same half. -/
theorem biasWriteBeforeReuse {x y byte : Nat} {part : Part} {loc : Loc}
    (ha : AsyncCovers X early (.write (.load x y byte)) loc) (hb : AsyncCovers X later part loc) :
    ByteCausality l X loc (.async early (.write (.load x y byte))) (.async later part) := by
  exact .direct (biasModelWriteBeforeReuse hp hX hEarly hLater hCta hOrd ha hb)

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
