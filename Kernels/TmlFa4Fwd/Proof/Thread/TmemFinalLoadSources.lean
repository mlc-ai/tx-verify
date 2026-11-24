-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFinalLoadOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.TailPvIssueOrder
import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Protocol.UnitGate
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.AsyncCopy PTX.Assumption
open Thread.Scores
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Correction (finalizeLoadPc outputAddress rowOf)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The observed terminal commit gives the last actual PV instruction for each stage. -/
private theorem finalPvThroughOutputWait (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {load : EvId} {address : Nat}
    {words : List Value} {shape : TcShape} (chunk : Fin 16)
    (he : X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld address words shape)⟩) :
    ∃ source d op acc mask,
      PvInstruction X source (firstPvBlock false stage) 7 d op acc mask ∧
      source.1/l.block = load.1/l.block ∧ DoneBefore l X source load := by
  have finish {g i tag selectTag inst leader : Nat} {spec : TcCommit.Spec} {wait : EvId}
      {object : Loc} {scope : MbarScope} {rank : Fin 16}
      (hc : X.get (g,i) = some ⟨tag,.tc (.commit spec)⟩)
      (hTag : tag = 2642 ∨ tag = 2646)
      (hElect : X.Elect (g,i-1) selectTag (2^32-1) inst leader)
      (hWinner : laneOf l g = leader) (hSame : SameCta l g wait.1)
      (hTarget : TcCommit.target spec rank = some object)
      (hNotified : rank ∈ X.tcNotified (g,i))
      (hObserved : WaitObserves X (.async (g,i) (.tcNotify rank)) wait object true scope)
      (hPo : po X wait load) :
      ∃ source d op acc mask,
        PvInstruction X source (firstPvBlock false stage) 7 d op acc mask ∧
        source.1/l.block = load.1/l.block ∧ DoneBefore l X source load := by
    obtain ⟨k,hEarlier,d,op,acc,mask,hPv⟩ :=
      finalPvBeforeMatchedOutputCommit hp hX stage hc hTag hElect hWinner
    have hTracks : TracksMma X (g,k) (g,i) :=
      ⟨rfl,hEarlier,.inl ⟨d,op,acc,mask,_,hPv.decoded⟩,spec,⟨_,hc⟩⟩
    have hAsync : AsyncObserved X (g,k) .mmaDone wait true scope :=
      ⟨.async (g,i) (.tcNotify rank),object,
        ⟨(g,i),spec,rank,rfl,hTracks,⟨_,hc⟩,hTarget,hNotified⟩,hObserved⟩
    exact ⟨(g,k),d,op,acc,mask,hPv,hSame.2.2.trans (congrArg (·/l.block) hPo.1),
      .inl ⟨wait,scope,hAsync,MbarRing.Unit.Gate.scopesMeet hSame .cluster scope,
        .single (.inl hPo)⟩⟩
  fin_cases stage
  · obtain ⟨wait,hWait,hPo⟩ := firstAcquireBeforeFinalizationLoad hp hX 0 he
    obtain ⟨⟨g,i⟩,spec,rank,scope,hc,hSame,hTarget,hNotified,hObserved⟩ :=
      firstOutputAcquireCommit hp hX hWait
    obtain ⟨_,inst,leader,hElect,hWinner⟩ := firstOutputCommitLeader hp hX hc
    exact finish hc (.inl rfl) hElect hWinner hSame hTarget hNotified hObserved hPo
  · obtain ⟨wait,hWait,hPo⟩ := secondAcquireBeforeFinalizationLoad hp hX he
    obtain ⟨⟨g,i⟩,spec,rank,scope,hc,hSame,hTarget,hNotified,hObserved⟩ :=
      secondOutputAcquireCommit hp hX hWait
    obtain ⟨_,inst,leader,hElect,hWinner⟩ := secondOutputCommitLeader hp hX hc.decoded
    exact finish hc.decoded (.inr rfl) hElect hWinner hSame hTarget hNotified hObserved hPo

/-- A decoded finalization load reads that stage's output row and columns. -/
theorem finalizationLoadCellOfDecoded (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (chunk : Fin 16) {load : EvId}
    {address : Nat} {words : List Value} {shape : TcShape} {j : Nat} {cell : Cell}
    (he : X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld address words shape)⟩)
    (hj : j < words.length) (hCell : cell = tcDataCell l load.1 shape address j) :
    j < 8 ∧ cell = ⟨load.1/l.block,rowOf l load.1,outputColumn stage+8*chunk.val+j⟩ := by
  obtain ⟨rfl,rfl,hLength⟩ := finalizeLoadActualAddress hp hX stage chunk he
  rw [hLength] at hj
  refine ⟨hj,?_⟩
  rw [hCell,show outputAddress l load.1 stage (8*chunk.val) =
    2^16*laneBase l load.1 + (outputColumn stage+8*chunk.val) from rfl,
    tcDataCell_warp32 l load.1 j (by
      have := outputColumn_range stage
      have := chunk.isLt
      omega)]
  have hRow : laneBase l load.1 + laneOf l load.1 = rowOf l load.1 := by
    unfold laneBase laneOf rowOf
    omega
  rw [hRow]

/-- Every cell of an actual finalization load is written by the terminal PV fragment. -/
theorem finalizationLoadLastPvCell (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (chunk : Fin 16) {load : EvId} {address : Nat} {words : List Value}
    {shape : TcShape} {j : Nat} {cell : Cell}
    (he : X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld address words shape)⟩)
    (hj : j < words.length) (hCell : cell = tcDataCell l load.1 shape address j) :
    ∃ source d op acc mask,
      PvInstruction X source (firstPvBlock false stage) 7 d op acc mask ∧
      X.MmaCell source cell ∧ DoneBefore l X source load := by
  obtain ⟨hJ,rfl⟩ := finalizationLoadCellOfDecoded hp hX stage chunk he hj hCell
  let row : Fin 128 := ⟨rowOf l load.1,Nat.mod_lt _ (by decide)⟩
  let col : Fin 128 := ⟨8*chunk.val+j,by have := chunk.isLt; omega⟩
  obtain ⟨source,d,op,acc,mask,hPv,hOwner,hDone⟩ :=
    finalPvThroughOutputWait hp hX stage chunk he
  have hStage : (pvSite (firstPvBlock false stage)).stage = stage := by
    fin_cases stage <;> rfl
  obtain ⟨_,_,hDesc,_,_⟩ := hPv.valueOperand hp hX
  have hResult := hPv.outputCell hp hX row col
  rw [hStage,hOwner] at hResult
  have hWrite := writeCell_no_mask_128
    (show op.descriptor.group = .one by rw [hDesc]; rfl)
    (show op.descriptor.m = 128 by rw [hDesc]; rfl) row.isLt row.isLt hResult
  have hMask := (hPv.fixedOperandFields hX).2.2
  have hWrite' : writeCell op d mask row.val col.val =
      some ⟨load.1/l.block,rowOf l load.1,outputColumn stage+8*chunk.val+j⟩ := by
    rw [hMask]
    simpa only [row,col,Nat.add_assoc] using hWrite
  exact ⟨source,d,op,acc,mask,hPv,⟨d,op,acc,mask,row.val,col.val,
    ⟨_,hPv.decoded⟩,hWrite'⟩,hDone⟩

set_option maxRecDepth 100000 in
private theorem terminalPvFloors (stage : Fin 2) :
    let boundary := pvPc (firstPvBlock false stage) 7
    (kernel.code.drop boundary).all (fun ins => staysPastEvent boundary ins.op) = true ∧
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (boundary ≤ seg.stop)
      | none => false) = true := by
  fin_cases stage <;> constructor <;> kernel_rfl

/-- Any score commit in the same CTA precedes the last fragment of its output stage. -/
theorem lastPvAfterScoreCommit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {source commit : EvId} {d : Nat} {op : OperandSpec} {acc : Bool}
    {mask : List Nat} {spec : TcCommit.Spec} {rank : Fin 16}
    (hPv : PvInstruction X source (firstPvBlock false stage) 7 d op acc mask)
    (hScore : ScoreCommit l X commit (source.1/l.block) stage spec rank) :
    commit.2 < source.2 := by
  obtain ⟨block,_,hc⟩ := scoreCommitSite hp hX hScore
  have hLane := (mmaAndScoreCommitSameThread hp hX ⟨_,hPv.decoded⟩ hScore rfl).symm
  obtain ⟨hFloor,hSegments⟩ := terminalPvFloors stage
  have hEarlier : ∀ (stage : Fin 2) (block : Fin 4),
      (commitSite (qkCommitSite block)).pc < pvPc (firstPvBlock false stage) 7 := by decide
  obtain ⟨g,k⟩ := commit
  obtain ⟨g',j⟩ := source
  change g = g' at hLane
  subst g'
  exact traceOrderOfPcFloor hX hFloor hSegments hc hPv.decoded
    (hEarlier stage block) le_rfl

/-- The final fragment of a stage is later than every competing PV destination write. -/
theorem lastPvDominatesOutputMma (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {source other : EvId} {d : Nat} {op : OperandSpec} {acc : Bool}
    {mask : List Nat} (hPv : PvInstruction X source (firstPvBlock false stage) 7 d op acc mask)
    {cell : Cell} (hSource : X.MmaCell source cell) (hOther : X.MmaCell other cell)
    (hColumn : outputColumn stage ≤ cell.column ∧ cell.column < outputColumn stage+128) :
    other = source ∨ Pipelined l X .dWrite other .dWrite source := by
  have hCta := (mmaWrittenCellCta hp hX hOther).symm.trans (mmaWrittenCellCta hp hX hSource)
  obtain ⟨_,_,_,_,_,_,hIssue,hWrite⟩ := hOther
  obtain ⟨block,frag,d',op',acc',mask',row,col,hStage,hOld,_⟩ :=
    mmaAccumulatorOnTile hp hX (tile := .rescale stage) hColumn hIssue
      (writeCell_resultCell hWrite)
  have hOutput : (pvSite (firstPvBlock false stage)).stage = stage := by
    fin_cases stage <;> rfl
  have hBlock : ∃ steady, block = firstPvBlock steady stage := by
    fin_cases block <;> fin_cases stage <;>
      first | exact ⟨true,rfl⟩ | exact ⟨false,rfl⟩ | cases hStage
  obtain ⟨steady,rfl⟩ := hBlock
  by_cases hLast : steady = false ∧ frag = 7
  · obtain ⟨rfl,rfl⟩ := hLast
    exact .inl (hOld.tailUnique hp hX stage hPv hCta)
  have hLane := mmaIssueSameThread hp hX ⟨_,hOld.decoded⟩ ⟨_,hPv.decoded⟩ hCta
  have hEarlier : other.2 < source.2 := by
    have hTrace : ∀ (stage : Fin 2) (steady : Bool) (frag : Fin 8),
        ¬(steady = false ∧ frag = 7) →
        pvPc (firstPvBlock steady stage) frag < pvPc (firstPvBlock false stage) 7 := by decide
    obtain ⟨hFloor,hSegments⟩ := terminalPvFloors stage
    obtain ⟨g,k⟩ := other
    obtain ⟨g',j⟩ := source
    change g = g' at hLane
    subst g'
    exact traceOrderOfPcFloor hX hFloor hSegments hOld.decoded hPv.decoded
      (hTrace stage steady frag hLast) le_rfl
  obtain ⟨_,_,hShape,hLow,hHigh⟩ := hOld.valueOperand hp hX
  obtain ⟨_,_,hShape',hLow',hHigh'⟩ := hPv.valueOperand hp hX
  have hAcc : SameAccumulator d' op' d op := by
    refine ⟨?_,by rw [hShape,hShape'],by rw [hShape,hShape'],
      hLow.trans (hCta.trans hLow'.symm),hHigh.trans (hCta.trans hHigh'.symm)⟩
    rw [hOld.outputDestination hp hX,hPv.outputDestination hp hX,hStage,hOutput]
  have hWarp : SameWarp l other.1 source.1 :=
    ⟨⟨event_thread_lt hX hOld.decoded,event_thread_lt hX hPv.decoded,hCta⟩,by rw [hLane]⟩
  have hPo := po_of_not_access hLane hEarlier (len_of_get hPv.decoded)
    (by rw [hPv.decoded]; rfl)
  exact .inr ⟨hWarp,.inl (.single (.inl hPo)),d',op',acc',mask',d,op,acc,mask,
    ⟨_,hOld.decoded⟩,⟨_,hPv.decoded⟩,hAcc⟩

/-- A cell read from Tensor Memory by the correction role's terminal output pass. -/
@[no_expose] def FinalizationLoadCell (l : Launch) (X : Execution) (load : EvId)
    (cell : Cell) (stage : Fin 2) : Prop :=
  ∃ (chunk : Fin 16) (address : Nat) (words : List Value) (shape : TcShape) (j : Nat),
    X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld address words shape)⟩ ∧
    j < words.length ∧ cell = tcDataCell l load.1 shape address j

/-- Classify the observed load register without exposing the decoded site above Thread. -/
theorem FinalizationLoadCell.ofDecoded {l : Launch} {X : Execution}
    {load : EvId} {cell : Cell} {stage : Fin 2} (chunk : Fin 16)
    {address : Nat} {words : List Value} {shape : TcShape} {j : Nat}
    (he : X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld address words shape)⟩)
    (hj : j < words.length) (hc : cell = tcDataCell l load.1 shape address j) :
    FinalizationLoadCell l X load cell stage :=
  ⟨chunk,address,words,shape,j,he,hj,hc⟩

/-- The finalization pass uses the output stage in its CTA. -/
theorem FinalizationLoadCell.geometry {load : EvId} {cell : Cell} {stage : Fin 2}
    (h : FinalizationLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) :
    cell.cta = load.1/l.block ∧ outputColumn stage ≤ cell.column ∧
      cell.column < outputColumn stage+128 := by
  obtain ⟨chunk,_,_,_,_,he,hj,hc⟩ := h
  obtain ⟨hJ,rfl⟩ := finalizationLoadCellOfDecoded hp hX stage chunk he hj hc
  have := chunk.isLt
  exact ⟨rfl,by dsimp; omega,by dsimp; omega⟩

/-- The finalization pass reads from the stage's actual terminal fragment. -/
theorem FinalizationLoadCell.lastPv {load : EvId} {cell : Cell} {stage : Fin 2}
    (h : FinalizationLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) :
    ∃ source d op acc mask,
      PvInstruction X source (firstPvBlock false stage) 7 d op acc mask ∧
      X.MmaCell source cell ∧ DoneBefore l X source load := by
  obtain ⟨chunk,_,_,_,_,he,hj,hc⟩ := h
  exact finalizationLoadLastPvCell hp hX stage chunk he hj hc
end

/-- A finalization load is distinct from every MMA issue. -/
theorem FinalizationLoadCell.neMma {l : Launch} {X : Execution} {load source : EvId}
    {cell : Cell} {stage : Fin 2} (h : FinalizationLoadCell l X load cell stage)
    (hm : X.MmaCell source cell) : source ≠ load := by
  rintro rfl
  obtain ⟨_,_,_,_,_,he,_,_⟩ := h
  obtain ⟨_,_,_,_,_,_,⟨_,hm⟩,_⟩ := hm
  rw [he] at hm
  exact TcKind.noConfusion (Kind.tc.inj (congrArg Event.kind (Option.some.inj hm)))

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
