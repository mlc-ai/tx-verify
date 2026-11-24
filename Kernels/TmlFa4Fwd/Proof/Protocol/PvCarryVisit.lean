-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityVisitAlignment
public import Kernels.TmlFa4Fwd.Proof.Protocol.PvVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvCarryVisit
public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsScore
import Kernels.TmlFa4Fwd.Proof.Safety.TmemAccumulatorProvenance
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaSource
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma Thread Thread.Scores Protocol.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- The carry of the first PV fragment has an actual prior PV or rescale origin. -/
inductive PvCarryOrigin (l : Launch) (X : Execution) (g use : Nat) (stage : Fin 2)
    (cell : Cell) (writer : EvId) : Prop
  | pv {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
      (hIssuer : writer.1 = g)
      (hIssue : PvInstruction X writer (firstPvBlock true stage) 7 d op acc mask)
      (hUse : Mma.LatestValueReadyUse l X g writer.2 (use-2)) :
      PvCarryOrigin l X g use stage cell writer
  | rescale (hStore : OutputRescaleStore X writer stage)
      (hValue : ∃ value, StoreValue l X writer cell value)
      (observed : RescaleStatisticsScore l X writer stage)
      (hSameVisit : scoreCommitOrdinal l X (writer.1/l.block) stage observed.commit = use/2) :
      PvCarryOrigin l X g use stage cell writer

private theorem earlierValueUse {l : Launch} {X : Execution} {g index prior u v : Nat}
    (hEarlier : prior < index) (hu : Mma.LatestValueReadyUse l X g prior u)
    (hv : Mma.LatestValueReadyUse l X g index v) : u ≤ v := by
  obtain ⟨a,ha,hU,hOdd,hAt,_⟩ := hu
  obtain ⟨b,_,hV,_,_,hOnly⟩ := hv
  have hLe : a ≤ b := by
    by_contra! hOrder
    have hLater := hOnly a _ _ hOrder (hAt.2.1.trans hEarlier) ha
    omega
  have hSize := ((List.take_sublist_take_left (l := X.tr g) hLe).filterMap readyEvent).length_le
  change Mma.readyCount X g a ≤ Mma.readyCount X g b at hSize
  omega

/-- The carry flag is enabled only for an actual noninitial V visit. -/
theorem PvVisit.keepOfValueUse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g last use : Nat} {block : Fin 4} {row col : Fin 128}
    (visit : PvVisit l X g block use row col last) : visit.keep = true ↔ 0 < use/2 := by
  have hFragment := visit.fragment 0
  simp only [Fin.val_zero, Nat.lt_irrefl, decide_false, Bool.or_false] at hFragment
  exact hFragment.firstCarryOfValueUse hp hX (visit.ready 0)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

/-- A fragment's observed score notification is the one of its actual V use. -/
theorem pvObservedScoreOfUse {g index use d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hPv : PvInstruction X (g,index) block step d op acc mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) :
    let stage := (pvSite block).stage
    ∃ score spec rank, ScoreCommit l X score (g/l.block) stage spec rank ∧
      scoreCommitOrdinal l X (g/l.block) stage score = use/2 ∧
      scoreCommitOrdinal l X (g/l.block) stage (g,index) = use/2+1 := by
  dsimp only
  let stage := (pvSite block).stage
  have hMma : X.MmaIssue (g,index) d op acc mask := ⟨_,hPv.decoded⟩
  obtain ⟨_,_,hDesc,hCta,_⟩ := hPv.valueOperand hp hX
  have hAddress := hPv.probabilityAddress hp hX
  have hA := pvACell hDesc stage step 0 0 hAddress
  let cell : Cell := ⟨g/l.block,0,probabilityColumn stage+8*step.val⟩
  have hRead : X.MmaACell (g,index) cell := by
    refine ⟨_,_,_,_,0,0,hMma,?_⟩
    simpa [cell,hCta] using hA
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨seen⟩ := probabilityCellPublication hp hX hJoint hRead
  obtain ⟨hStage,hPhase,obs,hOrdinal⟩ := seen.exactPvVisit hp hX hCuQ hRead hPv hUse
  obtain ⟨_,_,hCount⟩ := seen.exactScore hp hX hCuQ hRead
  have hOwner : seen.store.1/l.block = g/l.block := seen.footprint.cta.symm
  have hScoreAtCta : ScoreCommit l X obs.commit (g/l.block) seen.stage obs.spec obs.rank :=
    hOwner ▸ obs.score
  have hScore : ScoreCommit l X obs.commit (g/l.block) stage obs.spec obs.rank :=
    Eq.mp (congrArg (fun s => ScoreCommit l X obs.commit (g/l.block) s obs.spec obs.rank)
      hStage) hScoreAtCta
  have hExact : scoreCommitOrdinal l X (g/l.block) stage obs.commit = use/2 :=
    (congrArg (fun s => scoreCommitOrdinal l X (g/l.block) s obs.commit) hStage).symm.trans hOrdinal
  rw [hStage,hPhase] at hCount
  exact ⟨obs.commit,obs.spec,obs.rank,hScore,hExact,hCount⟩

/-- A carried visit follows the actual last fragment of the preceding V visit of this stage. -/
theorem PvVisit.previousValueBank {g last use : Nat} {block : Fin 4} {row col : Fin 128}
    (visit : PvVisit l X g block use row col last) (hKeep : visit.keep = true) :
    let stage := (pvSite block).stage
    ∃ prior < visit.issues 0, ∃ d op acc mask,
      PvInstruction X (g,prior) (firstPvBlock true stage) 7 d op acc mask ∧
      Mma.LatestValueReadyUse l X g prior (use-2) := by
  dsimp only
  let stage := (pvSite block).stage
  let index := visit.issues 0
  have hFirst := visit.fragment 0
  have hUse := visit.ready 0
  obtain ⟨score,spec,rank,hScore,hOrdinal,hCount⟩ := pvObservedScoreOfUse hp hX hCuQ hFirst hUse
  have hPos := (visit.keepOfValueUse hp hX).mp hKeep
  have hIssue : X.MmaIssue (g,index) (outputColumn stage) (pvOperands l g block 0 use)
      (visit.keep || decide (0 < (0 : Fin 8).val)) (List.replicate 4 0) := ⟨_,hFirst.decoded⟩
  have hLane := mmaAndScoreCommitSameThread hp hX hIssue hScore rfl
  have hId : score = (g,score.2) := Prod.ext hLane.symm rfl
  have hBefore : score.2 < index := by
    by_contra! hAt
    have hMono := (List.take_sublist_take_left (l := X.tr g) hAt).countP_le
      (p := scoreCommitOn (scoreReadyObject l (g/l.block) stage))
    change scoreCommitOrdinal l X (g/l.block) stage (g,index) ≤
      scoreCommitOrdinal l X (g/l.block) stage (g,score.2) at hMono
    rw [← hId] at hMono
    change scoreCommitOrdinal l X (g/l.block) stage score = use/2 at hOrdinal
    change scoreCommitOrdinal l X (g/l.block) stage (g,index) = use/2+1 at hCount
    omega
  have hScore' : ScoreCommit l X (g,score.2) (g/l.block) stage spec rank := hId ▸ hScore
  have hPositive : 0 < scoreCommitOrdinal l X (g/l.block) stage (g,score.2) := by
    rw [← hId]
    exact hOrdinal.symm ▸ hPos
  obtain ⟨prior,hPrior,previousUse,d,op,acc,mask,hPv,hPrevious,hRank⟩ :=
    hScore'.previousValueUse hp hX hPositive
  rw [← hId] at hRank
  have hOdd := (show use%2 = 1 by obtain ⟨_,_,_,h,_,_⟩ := hUse; exact h)
  have hBeforeOdd := (show previousUse%2 = 1 by obtain ⟨_,_,_,h,_,_⟩ := hPrevious; exact h)
  have hExact : previousUse = use-2 := by
    change scoreCommitOrdinal l X (g/l.block) stage score = use/2 at hOrdinal
    omega
  exact ⟨prior,hPrior.trans hBefore,d,op,acc,mask,hPv,hExact ▸ hPrevious⟩

/-- Each enabled first PV carry reads a stable actual accumulator write.
A correction store has observed the score of the current visit and stage. -/
theorem PvVisit.carrySource {g last use : Nat} {block : Fin 4} {row col : Fin 128}
    (visit : PvVisit l X g block use row col last) (hKeep : visit.keep = true) :
    let stage := (pvSite block).stage
    let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
    ∃ writer, ReadSource l X .acc writer (g,visit.issues 0) cell ∧
      PvCarryOrigin l X g use stage cell writer := by
  dsimp only
  let stage := (pvSite block).stage
  let reader := (g,visit.issues 0)
  let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
  let op := pvOperands l g block 0 use
  have hFragment : PvInstruction X reader block 0 (outputColumn stage) op true
      (List.replicate 4 0) := by
    simpa [hKeep] using visit.fragment 0
  have hMma : X.MmaIssue reader (outputColumn stage) op true (List.replicate 4 0) :=
    ⟨_,hFragment.decoded⟩
  have hD : resultCell op (outputColumn stage) row.val col.val = some cell :=
    hFragment.outputCell hp hX row col
  have hRead : X.MmaReadCell reader cell :=
    ⟨_,_,_,row.val,col.val,hMma,hD⟩
  have hBand : (.rescale stage : TensorStoreTile).columns.1 ≤ cell.column ∧
      cell.column < (.rescale stage : TensorStoreTile).columns.2 := by
    have := col.isLt
    change outputColumn stage ≤ outputColumn stage+col.val ∧
      outputColumn stage+col.val < outputColumn stage+128
    omega
  obtain ⟨writer,hSource⟩ := Safety.mmaAccumulatorReadSource hp hX hCuQ hRead
  have hGuard := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
  obtain ⟨prior,hPrior,prevD,prevOp,prevAcc,prevMask,hPrevious,hPreviousUse⟩ :=
    visit.previousValueBank hp hX hCuQ hKeep
  let prevBlock := firstPvBlock true stage
  have hBank : (pvSite prevBlock).stage = stage := by
    have audit : ∀ s : Fin 2, (pvSite (firstPvBlock true s)).stage = s := by decide
    exact audit stage
  have hOldIssue : X.MmaIssue (g,prior) prevD prevOp prevAcc prevMask :=
    ⟨_,hPrevious.decoded⟩
  obtain ⟨_,_,hDesc,_,_⟩ := hPrevious.valueOperand hp hX
  have hPreviousCell := hPrevious.outputCell hp hX row col
  rw [hBank] at hPreviousCell
  have hFixed := (hPrevious.fixedOperandFields hX).2.2
  have hPrevWrite : X.MmaCell (g,prior) cell := by
    refine ⟨prevD,prevOp,prevAcc,prevMask,row.val,col.val,hOldIssue,?_⟩
    rw [hFixed]
    exact writeCell_no_mask_128 (by rw [hDesc]; rfl) (by rw [hDesc]; rfl)
      row.isLt row.isLt hPreviousCell
  have hPriorLt : prior < reader.2 := hPrior
  have hPriorNe : (g,prior) ≠ reader := fun he => Nat.ne_of_lt hPriorLt (congrArg Prod.snd he)
  have hPriorTrace := po_of_not_access (show (g,prior).1 = reader.1 from rfl) hPriorLt
    (len_of_get hFragment.decoded) (mmaIsNotOrdinaryAccess hMma)
  have hPriorOrder : Relation.TransGen (TcStep l X) (g,prior) reader :=
    .single (.inl (.single (.inl hPriorTrace)))
  refine ⟨writer,hSource,?_⟩
  rcases hSource.2.1 with hW | hStore | hCopy | hShift
  · obtain ⟨od,oo,oa,om,r,c,hOld,hWritten⟩ := hW
    obtain ⟨b,f,_,_,_,_,_,_,hStage,hPv,hResult⟩ :=
      mmaAccumulatorOnTile hp hX hBand hOld (writeCell_resultCell hWritten)
    obtain ⟨_,_,_,hLow,hHigh⟩ := hPv.valueOperand hp hX
    have hOwner : writer.1/l.block = g/l.block := by
      rcases resultCell_cta hResult with h | h
      · exact (h.trans hLow).symm
      · exact (h.trans hHigh).symm
    have hIssuer := mmaIssueSameThread hp hX hOld hMma hOwner
    have hEarlier := tcStep_same_thread (tcStep_acyclic hX hGuard)
      hSource.2.2.1.tcStep hIssuer (mmaIsNotOrdinaryAccess hMma)
    obtain ⟨priorUse,hUse,_,_⟩ := Mma.valueFragmentUse hp hX hPv
    have hLane : writer.1 = g := hIssuer
    have hActual : Mma.LatestValueReadyUse l X g writer.2 priorUse := by
      simpa only [hLane] using hUse
    rcases hSource.2.2.2.1 (g,prior) (.inl hPrevWrite) with hEq | hPast | hFuture
    · exact hEq ▸ PvCarryOrigin.pv rfl hPrevious hPreviousUse
    · have hBetween := tcStep_same_thread (tcStep_acyclic hX hGuard) hPast.tcStep hLane.symm
        (mmaIsNotOrdinaryAccess hOld)
      let steady := decide (b.val < 2)
      let currentSteady := decide (block.val < 2)
      have hClass : ∀ i : Fin 4,
          i = firstPvBlock (decide (i.val < 2)) (pvSite i).stage := by decide
      have hOldBlock : b = firstPvBlock steady stage :=
        (hClass b).trans (congrArg (firstPvBlock steady) hStage)
      have hHeadBlock : block = firstPvBlock currentSteady stage := hClass block
      have hId : writer = (g,writer.2) := Prod.ext hLane rfl
      have hOldFragment : PvInstruction X (g,writer.2) (firstPvBlock steady stage)
          f _ _ _ _ := hOldBlock ▸ (hId ▸ hPv)
      have hHead := hHeadBlock ▸ hFragment
      have hUseLt : priorUse < use := by
        by_contra! hAtLeast
        have hUseEq := Nat.le_antisymm (earlierValueUse hEarlier hActual (visit.ready 0)) hAtLeast
        have hStrict := pvFragmentsOrderedWithinValueUse hp hX stage steady currentSteady
          hOldFragment hHead hEarlier (hUseEq ▸ hActual) (visit.ready 0)
        omega
      have hLower := earlierValueUse hBetween hPreviousUse hActual
      have hPrevOdd : priorUse%2 = 1 := by obtain ⟨_,_,_,h,_,_⟩ := hActual; exact h
      have hOdd : use%2 = 1 := by obtain ⟨_,_,_,h,_,_⟩ := visit.ready 0; exact h
      have hUseEq : priorUse = use-2 := by omega
      have hStrict := pvFragmentsOrderedWithinValueUse hp hX stage true steady hPrevious
        hOldFragment hBetween hPreviousUse (hUseEq ▸ hActual)
      have hFit := f.isLt
      omega
    · exact (tcStep_asymm hX hGuard (hFuture.tcStep hPriorNe) hPriorOrder).elim
  · obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
    have hTile : tile = .rescale stage := by
      have hLow := hFoot.columnLo
      have hHigh := hFoot.columnHi
      have hCol := col.isLt
      cases tile with
      | probability bank =>
        have hLimit := probabilityColumn_range bank
        have hScore := scoreColumn_range bank
        change cell.column < probabilityColumn bank+64 at hHigh
        change outputColumn stage+col.val < probabilityColumn bank+64 at hHigh
        dsimp [outputColumn] at hHigh
        omega
      | rescale bank =>
        suffices bank = stage by rw [this]
        apply Fin.ext
        change outputColumn bank ≤ outputColumn stage+col.val at hLow
        change outputColumn stage+col.val < outputColumn bank+128 at hHigh
        simp only [outputColumn] at hLow hHigh
        omega
    subst tile
    have hOn : MmaAccumulatorOn X reader cell (.rescale stage) :=
      ⟨block,0,_,_,_,_,row.val,col.val,rfl,hFragment,hD⟩
    obtain ⟨_,_,_,_,_,hIssue,hSame,hRescale,_⟩ := outputRescaleOverlap hp hX hStore hFoot hOn
    obtain ⟨seen⟩ := rescaleStatisticsObservedScore hp hX hCuQ hRescale
    have hBefore : seen.commit.2 ≤ reader.2 := by
      by_contra! hAfter
      exact tcStep_asymm hX hGuard (seen.doneBeforeEarlierMma hp hX hIssue hSame hAfter).tcStep
        hSource.2.2.1.tcStep
    have hUpper := scoreCommitCountBeforeMma hp hX hIssue seen.score hSame.2.2 hBefore
    obtain ⟨_,_,_,_,_,hCount⟩ := pvObservedScoreOfUse hp hX hCuQ hFragment (visit.ready 0)
    change scoreCommitOrdinal l X (g/l.block) stage reader = use/2+1 at hCount
    rw [show g/l.block = writer.1/l.block from hSame.2.2] at hCount
    change scoreCommitOrdinal l X (writer.1/l.block) stage seen.commit+1 ≤
      scoreCommitOrdinal l X (writer.1/l.block) stage reader at hUpper
    have hExact : scoreCommitOrdinal l X (writer.1/l.block) stage seen.commit = use/2 := by
      by_contra hNot
      have hOlder : scoreCommitOrdinal l X (writer.1/l.block) stage seen.commit < use/2 := by omega
      have hOnPrev : MmaAccumulatorOn X (g,prior) cell (.rescale stage) :=
        ⟨prevBlock,7,prevD,prevOp,prevAcc,prevMask,row.val,col.val,hBank,hPrevious,hPreviousCell⟩
      obtain ⟨_,_,_,_,_,hPrevMma,hPrevCta,_,hAcquire⟩ :=
        outputRescaleOverlap hp hX hStore hFoot hOnPrev
      obtain ⟨_,_,_,_,_,hPreviousCount⟩ := pvObservedScoreOfUse hp hX hCuQ hPrevious hPreviousUse
      change scoreCommitOrdinal l X (g/l.block) (pvSite prevBlock).stage (g,prior) =
        (use-2)/2+1 at hPreviousCount
      rw [hBank,hPrevCta.2.2] at hPreviousCount
      have hEarlier : seen.commit.2 ≤ prior := by
        by_contra! hLater
        have hLane := (mmaAndScoreCommitSameThread hp hX hPrevMma seen.score hPrevCta.2.2).symm
        have hId : seen.commit = (g,seen.commit.2) := Prod.ext hLane rfl
        have hMono := (List.take_sublist_take_left (l := X.tr g) hLater.le).countP_le
          (p := scoreCommitOn (scoreReadyObject l (writer.1/l.block) stage))
        change scoreCommitOrdinal l X (writer.1/l.block) stage (g,prior) ≤
          scoreCommitOrdinal l X (writer.1/l.block) stage (g,seen.commit.2) at hMono
        rw [← hId] at hMono
        have hPositive := (visit.keepOfValueUse hp hX).mp hKeep
        omega
      have hDone := outputRescaleBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
        stage hRescale hPrevMma hPrevCta seen hEarlier hAcquire
      rcases hSource.2.2.2.1 (g,prior) (.inl hPrevWrite) with h | h | h
      · exact mmaIssueNeStore hOldIssue hStore h
      · exact writeBefore_asymm hX hGuard h (.inr (.inl hDone))
      · exact tcStep_asymm hX hGuard (h.tcStep hPriorNe) hPriorOrder
    refine .rescale hRescale ?_ seen hExact
    obtain ⟨address,values,shape,i,hStoreGet,hi,hCell⟩ := hStore
    exact ⟨values[i],address,values,shape,i,hStoreGet,
      List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩,hCell⟩
  · obtain ⟨_,_,_,_,hCopy,_⟩ := hCopy
    exact (noTensorCopyOperandIssue hX hCopy).elim
  · obtain ⟨_,hShift,_⟩ := hShift
    exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Protocol
