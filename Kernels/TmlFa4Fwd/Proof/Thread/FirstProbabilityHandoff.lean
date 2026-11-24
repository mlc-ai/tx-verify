-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitProbabilityOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.TailPvProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTailRendezvous
import Lemmas.Protocol.StagingHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Softmax

section
variable {p : Params} {l : Launch} {X : Execution} {warp : Fin 8}
    {g j batch head row blocks cap past : Nat}
    (hRound : FirstRoundProgress p l X warp g j batch head row blocks cap past)
include hRound

/-- The first three P stores complete before the same lane publishes the early packet. -/
theorem firstProbabilityStoresBeforeCredit (q : Fin 4) (hQuarter : q.val < 3) :
    let source : EvId := (g,j+1+probabilityTraceIndex q)
    (∃ addr vals shape, X.TSt source addr vals shape) ∧
    (∃ pc, X.get (g,j+1+4) = some ⟨pc,.tc .waitSt⟩) ∧
      source.2 < j+1+4 ∧ ProbabilityCredit l X (g,j+1+5) (g/l.block) (stageOf warp) 0 := by
  obtain ⟨_,bar,elect,leader,_,_,hPub,_⟩ := hRound
  let stage := stageOf warp
  have hNotice : X.get (g,j+1+5) =
      some ⟨4847,.arrive (signalLoc l g stage 1) 0 1 true .cta⟩ := hPub 5
  have hLoc : signalLoc l g stage 1 = probabilityObject l (g/l.block) stage 0 := by
    unfold signalLoc probabilityObject
    congr 1
    change l.sharedBase+8*stage.val+96 = l.sharedBase+(96+8*stage.val+16*0)
    omega
  rw [hLoc] at hNotice
  refine ⟨?_,⟨4845,hPub 4⟩,?_,⟨4847,hNotice⟩⟩
  · fin_cases q
    · exact ⟨_,_,_,_,hPub 1⟩
    · exact ⟨_,_,_,_,hPub 2⟩
    · exact ⟨_,_,_,_,hPub 3⟩
    · change 3 < 3 at hQuarter
      omega
  · change j+1+probabilityTraceIndex q < j+1+4
    unfold probabilityTraceIndex
    rw [ite_eq_right (by omega)]
    omega

/-- An early-packet observation orders the completed first-round stores before the PV issue. -/
theorem firstProbabilityStoresDoneBeforeObservedPv (q : Fin 4) (hQuarter : q.val < 3) {i : EvId}
    {w : Nat} (hCta : SameCta l g i.1) (hResume : Resumes kernel X (i.1,w) i) {scope : MbarScope}
    (hObserved : WaitObserves X (.thread (g,j+1+5)) (i.1,w)
      (probabilityObject l (g/l.block) (stageOf warp) 0) true scope) :
    StoreDoneBefore l X (g,j+1+probabilityTraceIndex q) i := by
  obtain ⟨hStore,hWait,hOrder,hCredit⟩ :=
    firstProbabilityStoresBeforeCredit (X := X) hRound q hQuarter
  have hRelease : MbarRelease X (g,j+1+5)
      (probabilityObject l (g/l.block) (stageOf warp) 0) .cta := ⟨0,1,hCredit⟩
  have hSc := MbarRing.Unit.Gate.scopesMeet hCta .cta scope
  have hBefore := Staging.baseCausality_of_handoff (e := (g,j+1+4)) hRelease hObserved hSc
    ⟨rfl,by omega⟩ hResume.1
  exact ⟨hStore,.inl ⟨(g,j+1+4),hWait,rfl,hOrder,.inl hBefore⟩⟩

end

/-- The last P store completes before PV via the elected credit and the
producer warp's actual full-warp rendezvous. -/
theorem firstTailProbabilityStoreDoneBeforePv {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {warp : Fin 8} {g j batch head row blocks cap past : Nat}
    (hRound : FirstRoundProgress p l X warp g j batch head row blocks cap past)
    {i credit : EvId} {w : Nat} (hWarp : SameWarp l g credit.1)
    (hCta : SameCta l credit.1 i.1) (hResume : Resumes kernel X (i.1,w) i)
    (hCredit : ProbabilityCredit l X credit (g/l.block) (stageOf warp) 1)
    {scope : MbarScope} (hObserved : WaitObserves X (.thread credit) (i.1,w)
      (probabilityObject l (g/l.block) (stageOf warp) 1) true scope) :
    StoreDoneBefore l X (g,j+1+probabilityTraceIndex (3 : Fin 4)) i := by
  obtain ⟨_,bar,_,_,_,_,hPub,_⟩ := hRound
  have hStore : ∃ addr vals shape, X.TSt (g,j+1+probabilityTraceIndex (3 : Fin 4))
      addr vals shape := ⟨_,_,_,_,hPub 6⟩
  have hWait : ∃ tag, X.get (g,j+1+7) = some ⟨tag,.tc .waitSt⟩ := ⟨4857,hPub 7⟩
  have hBar : X.get (g,j+1+8) = some ⟨4858,.warpBar (2^32-1) bar⟩ := hPub 8
  have hFirst := firstTailBarrierBeforeWarpCredit hp hX hWarp hBar hCredit
    (show j+1+7 < j+1+8 by omega)
  have hRelease : MbarRelease X credit
      (probabilityObject l (g/l.block) (stageOf warp) 1) .cta := ⟨0,1,hCredit⟩
  have hSecond := Staging.baseCausality_of_handoff (e := credit) hRelease hObserved
    (MbarRing.Unit.Gate.scopesMeet hCta .cta scope) ⟨rfl,le_rfl⟩ hResume.1
  refine ⟨hStore,.inl ⟨(g,j+1+7),hWait,rfl,?_,.inl (hFirst.trans hSecond)⟩⟩
  change j+1+6 < j+1+7
  omega

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
