-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvCarryVisit
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleVisit
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputRescaleReuseOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Execution.ShapeExecution
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.TcMma Thread Thread.Correction Thread.Scores Protocol.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- If the actual carried value is unscaled, no rescale store covering this cell
can belong to that PV visit's score generation. -/
theorem PvVisit.noCurrentRescaleOfPriorPv {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index use prior d : Nat} {block : Fin 4} {row col : Fin 128}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (visit : PvVisit l X g block use row col index) (hCarry : visit.keep = true) :
    let stage := (pvSite block).stage
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op accum mask →
    Mma.LatestValueReadyUse l X g prior (use-2) →
    ReadSource l X .acc (g,prior) (g,visit.issues 0) cell →
    ∀ {store}, OutputRescaleStore X store stage → StoreCell l X store cell →
    ∀ seen : RescaleStatisticsScore l X store stage,
      scoreCommitOrdinal l X (store.1/l.block) stage seen.commit ≠ use/2 := by
  dsimp only
  intro hPrior hUsed hSource store hWriter hWord seen hOrdinal
  let stage := (pvSite block).stage
  let reader := visit.issues 0
  have hCurrent := visit.fragment 0
  have hOldIssue : X.MmaIssue (g,prior) d op accum mask := ⟨_,hPrior.decoded⟩
  have hNewIssue : X.MmaIssue (g,reader) (outputColumn stage) (pvOperands l g block 0 use)
      (visit.keep || decide (0 < (0 : Fin 8).val)) (List.replicate 4 0) := ⟨_,hCurrent.decoded⟩
  obtain ⟨_,hFoot⟩ := tensorStoreFootprint hp hX hWord
  have hCta : g/l.block = store.1/l.block := hFoot.cta
  have hRaw := hWord
  obtain ⟨_,_,_,_,⟨_,hStore⟩,_,_⟩ := hRaw
  have hSame := event_thread_lt hX hStore
  have hOldCta : SameCta l g store.1 :=
    ⟨event_thread_lt hX hPrior.decoded,hSame,hCta⟩
  have hNewCta : SameCta l g store.1 :=
    ⟨event_thread_lt hX hCurrent.decoded,hSame,hCta⟩
  have hCommit := mmaAndScoreCommitSameThread hp hX hOldIssue seen.score hCta
  have hId : seen.commit = (g,seen.commit.2) := Prod.ext hCommit.symm rfl
  have hRank : scoreCommitOrdinal l X (g/l.block) stage (g,seen.commit.2) = use/2 := by
    rw [hCta,← hId]
    exact hOrdinal
  obtain ⟨_,_,_,_,_,hOldCount⟩ := pvObservedScoreOfUse hp hX hCuQ hPrior hUsed
  have hStage : (pvSite (firstPvBlock true stage)).stage = stage := by
    have audit : ∀ s : Fin 2, (pvSite (firstPvBlock true s)).stage = s := by decide
    exact audit stage
  rw [hStage] at hOldCount
  have hPrevious : (use-2)/2+1 = use/2 := by
    have hPositive := (visit.keepOfValueUse hp hX).mp hCarry
    omega
  rw [hPrevious] at hOldCount
  obtain ⟨_,_,_,_,_,hNewCount⟩ := pvObservedScoreOfUse hp hX hCuQ hCurrent (visit.ready 0)
  have hBefore : prior < seen.commit.2 := by
    by_contra! hOrder
    have hCount := scoreCommitCountBeforeMma hp hX hOldIssue seen.score hCta hOrder
    rw [← hCta,hId,hRank,hOldCount] at hCount
    omega
  have hAfter : seen.commit.2 ≤ reader := by
    by_contra! hOrder
    have hCount := (List.take_sublist_take_left (l := X.tr g) (Nat.le_of_lt hOrder)).countP_le
      (p := scoreCommitOn (scoreReadyObject l (g/l.block) stage))
    change scoreCommitOrdinal l X (g/l.block) stage (g,reader) ≤
      scoreCommitOrdinal l X (g/l.block) stage (g,seen.commit.2) at hCount
    change scoreCommitOrdinal l X (g/l.block) stage (g,reader) = use/2+1 at hNewCount
    omega
  have hOldToStore := seen.doneBeforeEarlierMma hp hX hOldIssue hOldCta hBefore
  obtain ⟨wait,hWait⟩ := hCurrent.probabilityAcquire hp hX 0 (.inl rfl)
  have hStoreToRead := outputRescaleBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
    stage hWriter hNewIssue hNewCta seen hAfter hWait
  have hGuard := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
  rcases hSource.2.2.2.1 store (.inr (.inl hWord)) with hEq | hPast | hFuture
  · exact mmaIssueNeStore hOldIssue hWord hEq.symm
  · exact tcStep_asymm hX hGuard hPast.tcStep hOldToStore.tcStep
  · have hNe : store ≠ (g,reader) := (mmaIssueNeStore hNewIssue hWord).symm
    exact tcStep_asymm hX hGuard (hFuture.tcStep hNe) hStoreToRead.tcStep

/-- Carrying the previous PV result directly forces the actual rescale visit
for that row and score generation to take its no-store branch. -/
theorem PvVisit.previousCarrySkipsRescale {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index use prior d correction pos : Nat} {block : Fin 4} {row col : Fin 128}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    {alpha : ℝ} {old : Fin 8 → Nat → ℝ} {vote : BitVec 32} {coefficient : Value}
    (visit : PvVisit l X g block use row col index) (hCarry : visit.keep = true)
    (hCta : correction/l.block = g/l.block)
    (hRow : laneBase l correction+laneOf l correction = row.val) :
    let stage := (pvSite block).stage
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op accum mask →
    Mma.LatestValueReadyUse l X g prior (use-2) →
    ReadSource l X .acc (g,prior) (g,visit.issues 0) cell →
    TmlFa4Fwd.Correction.RescaleVisit l X correction pos stage alpha old vote coefficient →
    (correctionBefore X (correction,pos)).barrier
      (TmlFa4Fwd.Correction.statsBarrierId l correction stage) = use/2 →
    vote = 0 := by
  dsimp only
  intro hPrior hUsed hSource hVisit hOrdinal
  by_contra hTakes
  obtain ⟨store,hLane,hObserved,hCell,hStatistics⟩ := hVisit.storeOfColumn hTakes col
  obtain ⟨seen,_,hCursor⟩ :=
    rescaleStatisticsObservedScoreWithOrdinal hp hX hCuQ hObserved
  rw [hLane] at hCursor
  have hScore : scoreCommitOrdinal l X (store.1/l.block) (pvSite block).stage seen.commit =
      use/2 := by
    rw [hLane]
    omega
  rw [hCta,hRow] at hCell
  exact visit.noCurrentRescaleOfPriorPv hp hX hCuQ hCarry hPrior hUsed hSource
    hObserved hCell seen hScore

end PTX.Kernels.TmlFa4Fwd.Protocol
