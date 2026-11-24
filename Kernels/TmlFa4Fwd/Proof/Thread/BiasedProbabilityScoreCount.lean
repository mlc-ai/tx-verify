-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatisticsEarlyRank
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityPublication
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow Softmax Prologue

/-- All events between the biased coefficient and the completed iteration
have the same physical successful score poll count. -/
theorem biasedProbabilityScoreCountOfIteration {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g store endPos visit : Nat} {t : TState}
    (hStage : warpIndex l g/4 = stage.val) {a : Acc} {data : List Byte}
    (hStore : StatisticsStore X (g,store) (rescaleStore true) a data)
    (hNotice : (before X (g,store)).notices = visit)
    (hPath : TraceReach kernel Assumptions.all l g {} ((X.tr g).take endPos) t)
    (hPc : t.pc = 5032 ∨ t.pc = 6654)
    (hEarly : ((X.tr g).take endPos).countP earlyProbabilityMark =
      ((X.tr g).take store).countP earlyProbabilityMark+1)
    {j : Nat} (hLo : store ≤ j) (hHi : j ≤ endPos) :
    okPolls (scoreReadyObject l (g/l.block) stage) ((X.tr g).take j) = visit+1 := by
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  have hStoreRank := scoreEarlyLedgerAtBiasedCoefficient hX hStore
  have hRaw := (earlyProbabilityCount hp hX stage hWarp hStage (len_of_get hStore)).trans
    ((rescaleStoreNoticeOfEarlyCredits hp hX (stage := stage) hStage hStore).symm.trans hNotice)
  change ((X.tr g).take store).countP earlyProbabilityMark = visit at hRaw
  change ((X.tr g).take store).countP scoreAcquireMark =
    ((X.tr g).take store).countP earlyProbabilityMark+1 at hStoreRank
  have hRun : ((X.tr g).take endPos).countP scoreAcquireMark =
      ((X.tr g).take endPos).countP earlyProbabilityMark := by
    rcases hPc with hHead | hDone
    · exact scoreEarlyLedgerAtHead hPath (.inr (.inl hHead))
    · exact scoreEarlyLedgerAtBiasedFallthrough hPath hDone
  have hFrom := countP_take_mono scoreAcquireMark (X.tr g) hLo
  have hUntil := countP_take_mono scoreAcquireMark (X.tr g) hHi
  have hExact : ((X.tr g).take j).countP scoreAcquireMark = visit+1 := by omega
  have hMark : scoreAcquireMark = phaseAcquired true := by
    funext event
    rw [scoreReadyMarkKind]
    rfl
  rw [hMark,scoreCount hp hX stage hWarp rfl hStage] at hExact
  exact hExact

/-- The completed biased visit owns all four actual probability
quarters and their common successful score poll. -/
theorem biasedObservedProbabilityTileOfIteration {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g store endPos visit bar : Nat} {t : TState}
    (hStage : warpIndex l g/4 = stage.val) {a : Acc} {data : List Byte}
    (hStore : StatisticsStore X (g,store) (rescaleStore true) a data)
    (hNotice : (before X (g,store)).notices = visit)
    (hPath : TraceReach kernel Assumptions.all l g {} ((X.tr g).take endPos) t)
    (hPc : t.pc = 5032 ∨ t.pc = 6654)
    (hEarly : ((X.tr g).take endPos).countP earlyProbabilityMark =
      ((X.tr g).take store).countP earlyProbabilityMark+1)
    {weights : Nat → ℝ}
    (hEvents : ∀ i : Fin (Repeated.biased.probabilityEvents l g stage weights).length,
      X.get (g,store+2+i.val) = (Repeated.biased.probabilityEvents l g stage weights)[i.val]?)
    (hEnd : store+2+(Repeated.biased.probabilityEvents l g stage weights).length < endPos)
    (hBar : X.get (g,store+2+(Repeated.biased.probabilityEvents l g stage weights).length+1) =
      some ⟨probabilityWaitPc .biased true+1,.warpBar (2^32-1) bar⟩) :
    ObservedProbabilityTile l X g stage visit weights := by
  apply Repeated.observedProbabilityTile (inst := bar) hp hX .biased stage hStage hEvents
  · rwa [Repeated.probabilityTailBarrierOffset_eq _ l g stage weights]
  · intro q
    have hOffset : Repeated.biased.probabilityStoreOffset q ≤
        (Repeated.biased.probabilityEvents l g stage weights).length := by
      change Repeated.biased.probabilityStoreOffset q ≤ 7
      fin_cases q <;> decide
    exact biasedProbabilityScoreCountOfIteration hp hX stage hStage hStore hNotice
      hPath hPc hEarly (by omega) (by omega)

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
