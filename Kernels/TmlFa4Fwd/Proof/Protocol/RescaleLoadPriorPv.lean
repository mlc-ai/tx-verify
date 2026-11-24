-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Protocol.PvCarryVisit
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputRescaleReuseOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Tcgen05.TcMmaSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Proof PTX.TcMma Thread Thread.Correction Thread.Scores Thread.Mma
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- A rescale load uses the last PV fragment of the preceding logical V visit. -/
theorem RescaleStatisticsScore.loadReadsPreviousPv {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {load : EvId} {stage : Fin 2} {row col : Fin 128}
    (seen : RescaleStatisticsScore l X load stage) {g prior use d : Nat} {op : OperandSpec}
    {acc : Bool} {mask : List Nat}
    (hOwner : g/l.block = load.1/l.block)
    (hLoad : RescaleLoadCell l X load ⟨g/l.block,row.val,outputColumn stage+col.val⟩ stage)
    (hPv : PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op acc mask)
    (hUse : LatestValueReadyUse l X g prior use)
    (hOrdinal : scoreCommitOrdinal l X (load.1/l.block) stage seen.commit = use/2+1) :
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    ReadSource l X .ld (g,prior) load cell ∧ DoneBefore l X (g,prior) load := by
  dsimp only
  let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
  have hStage : (pvSite (firstPvBlock true stage)).stage = stage := by
    fin_cases stage <;> decide
  have hIssue : X.MmaIssue (g,prior) d op acc mask := ⟨_,hPv.decoded⟩
  obtain ⟨hWrite,hCta⟩ := hLoad.matchesPv hp hX hPv hStage hOwner
  obtain ⟨_,_,_,_,_,hCount⟩ := pvObservedScoreOfUse hp hX hCuQ hPv hUse
  rw [hStage,hOwner] at hCount
  have hLane := (mmaAndScoreCommitSameThread hp hX hIssue seen.score hOwner).symm
  have hCommit : seen.commit = (g,seen.commit.2) := Prod.ext hLane rfl
  have hIssueBefore : prior < seen.commit.2 := by
    by_contra! hLate
    have hBound := scoreCommitCountBeforeMma hp hX hIssue seen.score hOwner hLate
    omega
  have hDone := seen.doneBeforeEarlierMma hp hX hIssue hCta hIssueBefore
  obtain ⟨source,hStable⟩ := Safety.rescaleLoadReadSource hp hX hCuQ hLoad
  have hGuard := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
  have hPriorNe : (g,prior) ≠ load := by
    intro hEq
    obtain ⟨_,_,_,_,he⟩ := hLoad.loadEvent.decoded
    rw [← hEq] at he
    have hDiff := (Event.mk.inj (Option.some.inj (hPv.decoded.symm.trans he))).2
    cases Kind.tc.inj hDiff
  refine ⟨?_,hDone⟩
  rcases hStable.2.2.2.1 (g,prior) (.inl hWrite) with hEqual | hOlder | hFuture
  · exact hEqual.symm ▸ hStable
  · exfalso
    rcases hStable.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · rcases Safety.rescaleLoadMmaOrder hp hX hCuQ hLoad seen hMma with hPast | hAfter
      · obtain ⟨d',op',acc',mask',r,c,hWriter,hWritten⟩ := hMma
        have hBand : (.rescale stage : TensorStoreTile).columns.1 ≤ cell.column ∧
            cell.column < (.rescale stage : TensorStoreTile).columns.2 := by
          have hc := col.isLt
          change outputColumn stage ≤ outputColumn stage+col.val ∧
            outputColumn stage+col.val < outputColumn stage+128
          omega
        obtain ⟨block,step,newD,newOp,newAcc,newMask,_,_,hBlockStage,hOther,_⟩ :=
          mmaAccumulatorOnTile hp hX hBand hWriter (writeCell_resultCell hWritten)
        have hSourceCta := mmaWrittenCellCta hp hX
          (show X.MmaCell source cell from ⟨d',op',acc',mask',r,c,hWriter,hWritten⟩)
        have hSourceOwner : source.1/l.block = g/l.block := by simpa [cell] using hSourceCta.symm
        have hSourceLane := mmaIssueSameThread hp hX hWriter hIssue hSourceOwner
        change source.1 = g at hSourceLane
        have hLater := tcStep_same_thread (tcStep_acyclic hX hGuard)
          hOlder.tcStep hSourceLane.symm (mmaIsNotOrdinaryAccess hWriter)
        obtain ⟨actual,hActual,_,_⟩ := valueFragmentUse hp hX hOther
        have hUsed : LatestValueReadyUse l X g source.2 actual := hSourceLane ▸ hActual
        have hNewId : source = (g,source.2) := Prod.ext hSourceLane rfl
        have hOther' : PvInstruction X (g,source.2) block step newD newOp newAcc newMask :=
          hNewId ▸ hOther
        obtain ⟨_,_,_,_,_,hNewCount⟩ := pvObservedScoreOfUse hp hX hCuQ hOther' hUsed
        rw [hBlockStage,hOwner] at hNewCount
        have hEarlierCommit : source.2 < seen.commit.2 := by
          by_contra! hLate
          have hOverlap := OutputRescaleLoad.sameCtaMma hX hLoad.loadEvent hWriter
            (hSourceOwner.trans hOwner)
          obtain ⟨wait,hWait⟩ := hOther.probabilityAcquire hp hX 0 (.inl rfl)
          have hAcquire : MmaProbabilityAcquire l X source stage 0 wait := hBlockStage ▸ hWait
          have hAfter := rescaleLoadBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
            stage hLoad.loadEvent hWriter hOverlap seen hLate hAcquire
          exact tcStep_asymm hX hGuard hAfter.tcStep hPast.tcStep
        have hLeft := (List.take_sublist_take_left (l := X.tr g) hLater.le).countP_le
          (p := scoreCommitOn (scoreReadyObject l (load.1/l.block) stage))
        have hRight := (List.take_sublist_take_left (l := X.tr g) hEarlierCommit.le).countP_le
          (p := scoreCommitOn (scoreReadyObject l (load.1/l.block) stage))
        change scoreCommitOrdinal l X (load.1/l.block) stage (g,prior) ≤
          scoreCommitOrdinal l X (load.1/l.block) stage (g,source.2) at hLeft
        change scoreCommitOrdinal l X (load.1/l.block) stage (g,source.2) ≤
          scoreCommitOrdinal l X (load.1/l.block) stage (g,seen.commit.2) at hRight
        rw [← hCommit] at hRight
        have hOdd : use % 2 = 1 := by obtain ⟨_,_,_,h,_⟩ := hUse; exact h
        have hOdd' : actual % 2 = 1 := by obtain ⟨_,_,_,h,_⟩ := hUsed; exact h
        have hEq : actual = use := by omega
        subst actual
        let steady := decide (block.val < 2)
        have audit : ∀ b : Fin 4,
            b = firstPvBlock (decide (b.val < 2)) (pvSite b).stage := by decide
        have hBlock : block = firstPvBlock steady stage :=
          (audit block).trans (congrArg (firstPvBlock steady) hBlockStage)
        have hSteps := pvFragmentsOrderedWithinValueUse hp hX stage true steady
          hPv (hBlock ▸ hOther') hLater hUse hUsed
        exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ step.isLt) hSteps)
      · exact tcStep_asymm hX hGuard hAfter.tcStep hStable.2.2.1.tcStep
    · obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
      have hRange : outputColumn stage ≤ cell.column ∧ cell.column < outputColumn stage+128 := by
        have hc := col.isLt
        change outputColumn stage ≤ outputColumn stage+col.val ∧
          outputColumn stage+col.val < outputColumn stage+128
        omega
      have hTile := Safety.rescaleWriterTile hFoot hRange
      subst tile
      have hOn : MmaAccumulatorOn X (g,prior) cell (.rescale stage) :=
        ⟨_,7,_,_,_,_,row.val,col.val,hStage,hPv,(hPv.outputCell hp hX row col).trans
          (by rw [hStage])⟩
      obtain ⟨_,_,_,_,_,hOldMma,hSame,hStoreEvent,hWait⟩ :=
        outputRescaleOverlap hp hX hStore hFoot hOn
      obtain ⟨earlier,_,hEarlierCursor⟩ :=
        rescaleStatisticsObservedScoreWithOrdinal hp hX hCuQ hStoreEvent
      have hSameLane := rescaleLoadStoreSameLane hp hX hLoad hFoot
      obtain ⟨_,_,_,_,he⟩ := hLoad.loadEvent.decoded
      have hLt := tcStep_same_thread (tcStep_acyclic hX hGuard)
        hStable.2.2.1.tcStep hSameLane (by rw [he]; rfl)
      have hEarlier := rescaleStoreOfEarlierVisit hp hX hLoad hStore hStoreEvent hFoot hLt
      have hOrdinalOlder : scoreCommitOrdinal l X (source.1/l.block) stage earlier.commit <
          use/2+1 := by
        rw [← hEarlierCursor,← seen.cursor,hOrdinal] at hEarlier
        omega
      have hPastCommit : earlier.commit.2 ≤ prior := by
        by_contra! hAfter
        have hCommitLane :=
          (mmaAndScoreCommitSameThread hp hX hOldMma earlier.score hSame.2.2).symm
        have hid : earlier.commit = (g,earlier.commit.2) := Prod.ext hCommitLane rfl
        have hMonotone := (List.take_sublist_take_left (l := X.tr g) hAfter.le).countP_le
          (p := scoreCommitOn (scoreReadyObject l (load.1/l.block) stage))
        change scoreCommitOrdinal l X (load.1/l.block) stage (g,prior) ≤
          scoreCommitOrdinal l X (load.1/l.block) stage (g,earlier.commit.2) at hMonotone
        rw [← hid,← hSameLane] at hMonotone
        rw [← hSameLane] at hCount
        omega
      have hPast := outputRescaleBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
        stage hStoreEvent hOldMma hSame earlier hPastCommit hWait
      exact writeBefore_asymm hX hGuard hOlder (.inr (.inl hPast))
    · exact noTensorCopyOperandIssue hX hCopy
    · exact noTensorShiftIssue hX hShift
  · exact (tcStep_asymm hX hGuard (hFuture.tcStep hPriorNe) hDone.tcStep).elim

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
