-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
public import Core.Tc.TcMmaOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TmemOrdinaryLoadOrder
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.TcMma Thread.Scores
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Correction (rowOf outputAddress rescaleLoadPc)

/-- The output rescale load and the cell selected by its actual register index. -/
@[no_expose] def RescaleLoadCell (l : Launch) (X : Execution) (load : EvId)
    (cell : Cell) (stage : Fin 2) : Prop :=
  ∃ (chunk : Fin 8) (address : Nat) (words : List Value) (shape : TcShape) (j : Nat),
    X.get load = some ⟨rescaleLoadPc stage chunk,.tc (.ld address words shape)⟩ ∧
    j < words.length ∧ cell = tcDataCell l load.1 shape address j

/-- Classify a decoded rescale load register inside Thread. -/
theorem RescaleLoadCell.ofDecoded {l : Launch} {X : Execution}
    {load : EvId} {cell : Cell} {stage : Fin 2} (chunk : Fin 8)
    {address : Nat} {words : List Value} {shape : TcShape} {j : Nat}
    (he : X.get load = some ⟨rescaleLoadPc stage chunk,.tc (.ld address words shape)⟩)
    (hj : j < words.length) (hc : cell = tcDataCell l load.1 shape address j) :
    RescaleLoadCell l X load cell stage :=
  ⟨chunk,address,words,shape,j,he,hj,hc⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The register of the rescale load reads its physical output row. -/
theorem RescaleLoadCell.geometry {load : EvId} {cell : Cell} {stage : Fin 2}
    (h : RescaleLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) :
    ∃ col : Fin 128, cell = ⟨load.1/l.block,rowOf l load.1,outputColumn stage+col.val⟩ := by
  obtain ⟨chunk,_,words,_,j,he,hJ,hCell⟩ := h
  obtain ⟨rfl,rfl,hLength⟩ := rescaleLoadActualAddress hp hX stage chunk he
  rw [hLength] at hJ
  let col : Fin 128 := ⟨16*chunk.val+j,by have := chunk.isLt; omega⟩
  refine ⟨col,?_⟩
  rw [hCell,show outputAddress l load.1 stage (16*chunk.val) =
    2^16*laneBase l load.1 + (outputColumn stage+16*chunk.val) from rfl,
    tcDataCell_warp32 l load.1 j (by
      have := outputColumn_range stage
      have := chunk.isLt
      omega)]
  have hRow : laneBase l load.1 + laneOf l load.1 = rowOf l load.1 := by
    unfold laneBase laneOf rowOf
    omega
  simp only [hRow,col,Nat.add_assoc]

/-- A score notification beyond the initial generation witnesses the preceding PV
update in the same physical output stage. -/
theorem steadyPvBeforePositiveScore (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {commit : EvId} {cta : Nat} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : ScoreCommit l X commit cta stage spec rank)
    (hLater : 0 < scoreCommitOrdinal l X cta stage commit) :
    ∃ source d op acc mask, PvInstruction X source (firstPvBlock true stage) 7 d op acc mask ∧
      source.1/l.block = cta ∧ source.2 < commit.2 := by
  obtain ⟨block,hStage,hRepeat,he⟩ := positiveScoreCommitRepeats hp hX hScore hLater
  have hSite : (commitSite (qkCommitSite block)).pc = if stage = 0 then 2418 else 2519 := by
    fin_cases block <;> fin_cases stage <;> first | decide | contradiction
  rw [hSite] at he
  obtain ⟨g,i⟩ := commit
  obtain ⟨k,hBefore,d,op,acc,mask,hPv⟩ := steadyPvBeforeRecurringScoreCommit hp hX stage he
  exact ⟨(g,k),d,op,acc,mask,hPv,(scoreCommitActor hp hX hScore).1,hBefore⟩

/-- A rescale-cell observation implies the corresponding ordinary load occurrence. -/
theorem RescaleLoadCell.loadEvent {l : Launch} {X : Execution} {load : EvId}
    {cell : Cell} {stage : Fin 2} (h : RescaleLoadCell l X load cell stage) :
    OutputRescaleLoad X load stage := by
  obtain ⟨chunk,address,words,shape,_,he,_,_⟩ := h
  exact OutputRescaleLoad.ofDecoded chunk he

/-- The actual CTA and output row bind every cell to the stage's PV result layout. -/
theorem RescaleLoadCell.matchesPv {load : EvId} {cell : Cell} {stage : Fin 2}
    (h : RescaleLoadCell l X load cell stage) (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {source : EvId} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : PvInstruction X source block step d op acc mask) (hStage : (pvSite block).stage = stage)
    (hOwner : source.1/l.block = load.1/l.block) :
    X.MmaCell source cell ∧ SameCta l source.1 load.1 := by
  obtain ⟨col,rfl⟩ := h.geometry hp hX
  obtain ⟨chunk,address,words,shape,_,he,_,_⟩ := h
  let row : Fin 128 := ⟨rowOf l load.1,Nat.mod_lt _ (by decide)⟩
  obtain ⟨_,_,hDesc,_,_⟩ := hPv.valueOperand hp hX
  have hResult := hPv.outputCell hp hX row col
  rw [hStage,hOwner] at hResult
  have hWrite := writeCell_no_mask_128
    (show op.descriptor.group = .one by rw [hDesc]; rfl)
    (show op.descriptor.m = 128 by rw [hDesc]; rfl) row.isLt row.isLt hResult
  have hMask := (hPv.fixedOperandFields hX).2.2
  have hWrite' : writeCell op d mask row.val col.val =
      some ⟨load.1/l.block,rowOf l load.1,outputColumn stage+col.val⟩ := by
    rw [hMask]
    exact hWrite
  exact ⟨⟨d,op,acc,mask,row.val,col.val,⟨_,hPv.decoded⟩,hWrite'⟩,
    event_thread_lt hX hPv.decoded,event_thread_lt hX he,hOwner⟩

/-- A recorded credit at the same or a later local ordinal observes the load's wait. -/
theorem rescaleLoadWaitThroughCredit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {load credit consumer : EvId} {stage : Fin 2} (hLoad : OutputRescaleLoad X load stage)
    (hCredit : ProbabilityCredit l X credit (load.1/l.block) stage 0)
    (hLane : credit.1 = load.1)
    (hOrdinal : probabilityOrdinal l X (load.1/l.block) stage 0 load ≤
      probabilityOrdinal l X (load.1/l.block) stage 0 credit)
    (hHandoff : baseCausality l X credit consumer) :
    WaitBefore l X .waitLd load consumer := by
  obtain ⟨chunk,_,_,_,hLoad⟩ := hLoad.decoded
  have hBefore := eventBeforeProbabilityCredit hLoad rfl hCredit hLane hOrdinal
  have hData : DataflowLoad X load := DataflowLoad.of_decoded
    ((by decide : ∀ stage chunk, rescaleLoadPc stage chunk ∈ Assumptions.tcLdDataflowSites)
      stage chunk) hLoad
  obtain ⟨_,he⟩ := hCredit
  exact dataflowLoadWaitThroughEvent hX hData he hBefore (by intro h; cases h) hHandoff

/-- A same-CTA MMA and a rescale load are actual events of threads in scope. -/
theorem OutputRescaleLoad.sameCtaMma {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {load mma : EvId} {stage : Fin 2} (hLoad : OutputRescaleLoad X load stage)
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hMma : X.MmaIssue mma d op acc mask) (hOwner : mma.1/l.block = load.1/l.block) :
    SameCta l mma.1 load.1 := by
  obtain ⟨_,_,_,_,hRead⟩ := hLoad.decoded
  obtain ⟨_,hWrite⟩ := hMma
  exact ⟨event_thread_lt hX hWrite,event_thread_lt hX hRead,hOwner⟩

theorem rescaleLoadStoreSameLane (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load store : EvId} {cell : Cell} {stage : Fin 2} (hLoad : RescaleLoadCell l X load cell stage)
    (hFoot : TensorStoreFootprint l store cell (.rescale stage)) : store.1 = load.1 := by
  have hRole := hLoad.loadEvent.correctionRole hp hX
  obtain ⟨col,hCell⟩ := hLoad.geometry hp hX
  have hCta : store.1/l.block = load.1/l.block :=
    hFoot.cta.symm.trans (congrArg Cell.cta hCell)
  have hRow : rowOf l store.1 = rowOf l load.1 :=
    hFoot.lane.symm.trans (congrArg Cell.lane hCell)
  have hGroup : store.1%l.block/128 = 2 := hFoot.warpGroup
  unfold Prologue.warpIndex at hRole
  unfold rowOf at hRow
  rw [hp.block] at hGroup hRole hRow hCta
  have hA := Nat.mod_add_div store.1 512
  have hB := Nat.mod_add_div load.1 512
  omega
/-- Correction accesses covering the same rescale cell are ordered on its owner lane. -/
theorem rescaleLoadStoreOrdered (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load store : EvId} {cell : Cell} {stage : Fin 2} (hLoad : RescaleLoadCell l X load cell stage)
    (hStore : StoreCell l X store cell) (hFoot : TensorStoreFootprint l store cell (.rescale stage))
    :
    WriteBefore l X store load ∨ ReadBefore l X .ld load store := by
  have hLane := rescaleLoadStoreSameLane hp hX hLoad hFoot
  obtain ⟨_,a,vs,shape,_,hRd,_,_⟩ := hLoad
  obtain ⟨b,ws,shape',_,⟨_,hWr⟩,_,_⟩ := hStore
  exact tensorLoadStoreOrderedOnThread hX ⟨a,vs,shape,_,hRd⟩ ⟨b,ws,shape',_,hWr⟩ hLane

/-- An older rescale store of this cell belongs to a strictly earlier
correction statistics visit than the recorded load. -/
theorem rescaleStoreOfEarlierVisit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {load store : EvId} {cell : Cell} {stage : Fin 2} (hLoad : RescaleLoadCell l X load cell stage)
    (hStore : StoreCell l X store cell) (hWriter : OutputRescaleStore X store stage)
    (hFoot : TensorStoreFootprint l store cell (.rescale stage)) (hBefore : store.2 < load.2) :
    (correctionBefore X store).barrier (TmlFa4Fwd.Correction.statsBarrierId l store.1 stage) <
      (correctionBefore X load).barrier (TmlFa4Fwd.Correction.statsBarrierId l load.1 stage) := by
  have hLane := rescaleLoadStoreSameLane hp hX hLoad hFoot
  obtain ⟨g,loadIndex⟩ := load
  obtain ⟨g',storeIndex⟩ := store
  change g' = g at hLane
  subst g'
  obtain ⟨i,_,_,_,j,hLoadGet,hJ,hLoadCell⟩ := hLoad
  obtain ⟨k,_,_,_,hStoreGet⟩ := hWriter.decoded
  obtain ⟨_,_,_,n,⟨_,he⟩,hN,hStoreCell⟩ := hStore
  have hEvent := Option.some.inj (he.symm.trans hStoreGet)
  obtain ⟨_,hKind⟩ := Event.mk.inj hEvent
  obtain ⟨rfl,rfl,rfl⟩ := TcKind.st.inj (Kind.tc.inj hKind)
  obtain ⟨rfl,rfl,hLoadLength⟩ := rescaleLoadActualAddress hp hX stage i hLoadGet
  obtain ⟨rfl,rfl,hStoreLength⟩ := rescaleStoreActualAddress hp hX stage k hStoreGet
  have hCol₁ : outputColumn stage+16*i.val < 512 := by
    have := outputColumn_range stage
    have := i.isLt
    omega
  have hCol₂ : outputColumn stage+16*k.val < 512 := by
    have := outputColumn_range stage
    have := k.isLt
    omega
  have hColumns := congrArg Cell.column (hLoadCell.symm.trans hStoreCell)
  change (tcDataCell l g .s32x32b (outputAddress l g stage (16*i.val)) j).column =
    (tcDataCell l g .s32x32b (outputAddress l g stage (16*k.val)) n).column at hColumns
  unfold outputAddress at hColumns
  rw [tcDataCell_warp32 l g j hCol₁,tcDataCell_warp32 l g n hCol₂] at hColumns
  change outputColumn stage+16*i.val+j = outputColumn stage+16*k.val+n at hColumns
  rw [hLoadLength] at hJ
  rw [hStoreLength] at hN
  have hChunk : i = k := Fin.ext (by omega)
  subst k
  exact previousRescaleStoreBeforeLoadAdvancesStatistics hp hX stage i hStoreGet hLoadGet hBefore

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
