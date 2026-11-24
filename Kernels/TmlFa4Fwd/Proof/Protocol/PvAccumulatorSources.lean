-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
public import Kernels.TmlFa4Fwd.Proof.MmaPvIssue
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvReadyFrame
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemOutputRescaleConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsScore
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.TcMma Thread Thread.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private theorem pvPipelineOfTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {b b' : Fin 4} {frag frag' : Fin 8} {d d' : Nat} {op op' : OperandSpec}
    {acc acc' : Bool} {mask mask' : List Nat}
    (hi : PvInstruction X i b frag d op acc mask)
    (hj : PvInstruction X j b' frag' d' op' acc' mask')
    (hSame : (pvSite b).stage = (pvSite b').stage) (hTrace : TraceBefore X i j) :
    Pipelined l X .dWrite i .dWrite j := by
  have hWarp : SameWarp l i.1 j.1 :=
    ⟨⟨event_thread_lt hX hi.decoded,event_thread_lt hX hj.decoded,by rw [hTrace.1]⟩,
      by rw [hTrace.1]⟩
  have hPo := po_of_not_access hTrace.1 hTrace.2.1 hTrace.2.2 (by rw [hj.decoded]; rfl)
  obtain ⟨_,_,hDesc,hLo,hHi⟩ := hi.valueOperand hp hX
  obtain ⟨_,_,hDesc',hLo',hHi'⟩ := hj.valueOperand hp hX
  have hCta := hWarp.1.2.2
  have hAcc : SameAccumulator d op d' op' :=
    ⟨(hi.outputDestination hp hX).trans ((congrArg outputColumn hSame).trans
      (hj.outputDestination hp hX).symm),
      by rw [hDesc,hDesc'],by rw [hDesc,hDesc'],
      hLo.trans (hCta.trans hLo'.symm),hHi.trans (hCta.trans hHi'.symm)⟩
  exact ⟨hWarp,.inl (.single (.inl hPo)),d,op,acc,mask,d',op',acc',mask',
    ⟨_,hi.decoded⟩,⟨_,hj.decoded⟩,hAcc⟩

private theorem outputBandDisjointProbability (stage other : Fin 2) (col : Fin 128) :
    ¬ ((.probability other : TensorStoreTile).columns.1 ≤ outputColumn stage+col.val ∧
      outputColumn stage+col.val < (.probability other : TensorStoreTile).columns.2) := by
  have hCol := col.isLt
  fin_cases stage <;> fin_cases other <;> simp [TensorStoreTile.columns,probabilityColumn,
    scoreColumn,outputColumn] <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec} {accum : Bool}
    {mask : List Nat} (hConsumer : PvInstruction X (g,index) block step d op accum mask)
include hp hX hCuQ hConsumer

/-- Every accumulating PV fragment after the first takes its accumulator from
the preceding fragment of the same visit. -/
theorem previousPvAccumulatorSourceAtUse (hStep : 0 < step.val) (row col : Fin 128) :
    ∃ prior < index, ∃ d' op' accum' mask',
      PvInstruction X (g,prior) block ⟨step.val-1,by omega⟩ d' op' accum' mask' ∧
      ReadSource l X .acc (g,prior) (g,index)
        ⟨g/l.block,row.val,outputColumn (pvSite block).stage+col.val⟩ ∧
      ∀ use, Mma.LatestValueReadyUse l X g index use → Mma.LatestValueReadyUse l X g prior use := by
  let stage := (pvSite block).stage
  let cell : Cell := ⟨g/l.block,row.val,outputColumn stage+col.val⟩
  obtain ⟨prior,hPrior,d',op',accum',mask',hProducer,hNoMma,hNoScore,hNoReady⟩ :=
    hConsumer.previousFragmentNoInterveningIssue hp hX hStep
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hConsumer.decoded⟩
  have hPrev : X.MmaIssue (g,prior) d' op' accum' mask' := ⟨_,hProducer.decoded⟩
  have hAfter : TraceBefore X (g,prior) (g,index) := ⟨rfl,hPrior,len_of_get hConsumer.decoded⟩
  have hOrder : WriteBefore l X (g,prior) (g,index) :=
    .inl (.inr (pvPipelineOfTrace hp hX hProducer hConsumer rfl hAfter))
  have hAcc : accum = true := (hConsumer.accumulatorUse hp hX).mpr (.inl hStep)
  have hReads : resultCell op d row col = some cell := hConsumer.outputCell hp hX row col
  have hRead : X.MmaReadCell (g,index) cell :=
    ⟨d,op,mask,row,col,hAcc ▸ hMma,hReads⟩
  have hWriteResult : resultCell op' d' row col = some cell := hProducer.outputCell hp hX row col
  have hMask := (hProducer.fixedOperandFields hX).2.2
  obtain ⟨_,_,hDesc,_,_⟩ := hProducer.valueOperand hp hX
  have hWrite : X.MmaCell (g,prior) cell := by
    refine ⟨d',op',accum',mask',row,col,hPrev,?_⟩
    rw [hMask]
    exact writeCell_no_mask_128 (by rw [hDesc]; rfl) (by rw [hDesc]; rfl)
      row.isLt row.isLt hWriteResult
  have hBand : (.rescale stage : TensorStoreTile).columns.1 ≤ cell.column ∧
      cell.column < (.rescale stage : TensorStoreTile).columns.2 := by
    change outputColumn stage ≤ outputColumn stage+col.val ∧
      outputColumn stage+col.val < outputColumn stage+128
    have := col.isLt
    omega
  have hLife := (Safety.mmaAccessLifetime hp hX hCuQ (.inr (.inl hRead))).2
  refine ⟨prior,hPrior,d',op',accum',mask',hProducer,readSource_acc.mpr ?_,
    fun _ hUse => hUse.beforeFragment hProducer hPrior hNoReady⟩
  refine ⟨fun h => (Nat.ne_of_lt hPrior) (congrArg Prod.snd h),.inl hWrite,hOrder,?_,?_⟩
  · intro other hw
    rcases hw with hOther | hStore | hCopy | hShift
    · obtain ⟨od,oa,oc,om,r,c,hIssue,hWrites⟩ := hOther
      have hResult := writeCell_resultCell hWrites
      obtain ⟨otherBlock,otherStep,_,_,_,_,_,_,hStage,hPv,hCell⟩ :=
        mmaAccumulatorOnTile hp hX hBand hIssue hResult
      have hCta : other.1/l.block = g/l.block := by
        obtain ⟨_,_,_,hLow,hHigh⟩ := hPv.valueOperand hp hX
        rcases resultCell_cta hCell with hc | hc
        · exact (hc.trans hLow).symm
        · exact (hc.trans hHigh).symm
      have hLane := mmaIssueSameThread hp hX hIssue hMma hCta
      obtain ⟨owner,position⟩ := other
      change owner = g at hLane
      subst owner
      rcases lt_trichotomy position prior with hOlder | rfl | hMiddle
      · exact .inr (.inr (.inl (.inl (.inr (pvPipelineOfTrace hp hX hPv hProducer hStage
          ⟨rfl,hOlder,len_of_get hProducer.decoded⟩)))))
      · exact .inl rfl
      rcases lt_trichotomy position index with hBefore | rfl | hLater
      · exact (hNoMma hMiddle hBefore hIssue).elim
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inr (.inr (pvPipelineOfTrace hp hX hConsumer hPv hStage.symm
          ⟨rfl,hLater,len_of_get hPv.decoded⟩))))
    · obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
      cases tile with
      | probability otherStage =>
        exact (outputBandDisjointProbability stage otherStage col ⟨hFoot.columnLo,
          hFoot.columnHi⟩).elim
      | rescale otherStage =>
        have hOverlap := mmaAccumulatorOnStoreTile hp hX hFoot hMma hReads
        obtain ⟨_,_,_,_,_,hReader,hSame,hRescale,_⟩ :=
          outputRescaleOverlap hp hX hStore hFoot hOverlap
        obtain ⟨seen⟩ := Scores.rescaleStatisticsObservedScore hp hX hCuQ hRescale
        have hScoreLane := mmaAndScoreCommitSameThread hp hX hMma seen.score hSame.2.2
        by_cases hEarlier : seen.commit.2 ≤ prior
        · have hPriorOverlap := mmaAccumulatorOnStoreTile hp hX hFoot hPrev hWriteResult
          obtain ⟨_,_,_,_,_,hBeforeIssue,hCta,_,hGuard⟩ :=
            outputRescaleOverlap hp hX hStore hFoot hPriorOverlap
          exact .inr (.inr (.inl (.inr (.inl
            (Scores.outputRescaleBeforeGuardedMma hp hX
              (Scores.correctionJointGuardsOfCuQ hp hX hCuQ)
              otherStage hRescale hBeforeIssue hCta seen hEarlier hGuard)))))
        · have hLater : index < seen.commit.2 := by
            by_contra! hNot
            have hNe := scoreCommitIndexNeMma hp hX seen.score hMma hSame.2.2
            have hMid : seen.commit.2 < index := by omega
            have hId : seen.commit = (g,seen.commit.2) := Prod.ext hScoreLane.symm rfl
            exact hNoScore (by omega) hMid (hId ▸ seen.score)
          exact .inr (.inr (.inr (.inl (seen.doneBeforeEarlierMma hp hX hReader hSame hLater))))
    · obtain ⟨_,_,_,_,hIssue,_⟩ := hCopy
      exact (noTensorCopyOperandIssue hX hIssue).elim
    · obtain ⟨_,hIssue,_⟩ := hShift
      exact (noTensorShiftIssue hX hIssue).elim
  · intro cta record hRecord hCovers release hRelease
    exact .inl (hLife cta record hRecord hCovers release hRelease)

end PTX.Kernels.TmlFa4Fwd.Protocol
