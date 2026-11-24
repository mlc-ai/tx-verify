-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPvNumerator
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFinalLoadOrder
import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Kernels.TmlFa4Fwd.Proof.Thread.Resources
import Kernels.TmlFa4Fwd.Proof.Thread.TmemMmaCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.TcMma Prologue Epilogue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma (trips qkByteIndex)

noncomputable section

private theorem correctionDataRow (l : Launch) (g : Nat) :
    laneBase l g + laneOf l g = rowOf l g := by
  unfold laneBase laneOf rowOf
  omega

/-- The final pass for a single-visit row loads the exact shifted numerator in its
eight decoded output columns. The corresponding terminal acquire fixes the read source. -/
theorem singleVisitFinalizationLoadValues {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X) {batch : Nat}
    (stage : Fin 2) (chunk : Fin 16) {load : EvId} {addr : Nat} {vals : List Value}
    {shape : TcShape} (he : X.get load = some ⟨finalizeLoadPc stage chunk,
      .tc (.ld addr vals shape)⟩)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ load.1/l.block)
    (hHi : load.1/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (load.1/l.block)).1 = 1)
    (hRow : stageRow (assignedCoordinates p batch (load.1/l.block)).1 stage + rowOf l load.1 <
      p.qLength batch) :
    let coords := assignedCoordinates p batch (load.1/l.block)
    let row := stageRow coords.1 stage + rowOf l load.1
    let reference := firstReference p batch coords.2 row 1
    vals = List.ofFn (fun k : Fin 8 => fl ((2 : ℝ) ^ (-reference) *
      maskedBlockSum (p.keyCount batch row) 1 0
        (weightedValue p batch coords.2 row (8*chunk.val+k.val)))) := by
  let g := terminalStatsProducer l load.1 stage
  let warp := terminalStatsWarp l load.1 stage
  let coords := assignedCoordinates p batch (load.1/l.block)
  let row := stageRow coords.1 stage + rowOf l load.1
  let reference := firstReference p batch coords.2 row 1
  have hLoadThread := event_thread_lt hX he
  have hGrid := NamedBar.cta_lt hLoadThread
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hCta : g/l.block = load.1/l.block := terminalStatsCta hp load.1 stage
  have hg : g < l.threads := by
    change g < l.grid*l.block
    have hLocal : g % l.block < l.block := Nat.mod_lt _ (by rw [hp.block]; decide)
    have hIndex := Nat.mod_add_div g l.block
    rw [hCta] at hIndex
    have hNext := Nat.mul_le_mul_left l.block (show load.1/l.block+1 ≤ l.grid by omega)
    rw [Nat.mul_add,Nat.mul_one] at hNext
    rw [Nat.mul_comm l.grid l.block]
    omega
  have hWarpVal : warpIndex l g = warp.val := terminalStatsProducerWarp hp load.1 stage
  have hWarp : warpIndex l g < 8 := hWarpVal.symm ▸ warp.isLt
  have hStage : stageOf ⟨warpIndex l g,hWarp⟩ = stage := by
    apply Fin.ext
    have hLimit : rowOf l load.1 < 128 := Nat.mod_lt _ (by decide)
    rw [show (⟨warpIndex l g,hWarp⟩ : Fin 8) = warp from Fin.ext hWarpVal]
    change (rowOf l load.1 / 32 + 4 * stage.val) / 4 = stage.val
    omega
  have hLocal : g % l.block % 128 = rowOf l load.1 := by
    have hLimit : rowOf l load.1 < 128 := Nat.mod_lt _ (by decide)
    have hS := stage.isLt
    unfold g terminalStatsProducer
    rw [hp.block]
    omega
  have hProducerRow : 128 * (2 * (assignedCoordinates p batch (g/l.block)).1 +
        (stageOf ⟨warpIndex l g,hWarp⟩).val) + g%l.block%128 = row := by
    rw [hCta,hStage,hLocal]
    unfold row stageRow coords
    omega
  have hPhysicalRow : (tmemRow l g).val = rowOf l load.1 := by
    change laneBase l g + laneOf l g = _
    unfold laneBase laneOf
    omega
  obtain ⟨wait,hWait,hWCta⟩ := secondOutputAcquireOfWorkExit hp hX hGrid hWork
    (ctaExited hX (fun _ hi => exitedOfComplete hX hDone hi))
  obtain ⟨rfl,rfl,hLen⟩ := finalizeLoadActualAddress hp hX stage chunk he
  let addr := outputAddress l load.1 stage (8*chunk.val)
  have hLoad : X.TLd load addr vals .s32x32b := ⟨_,he⟩
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 8
  · let col : Fin 128 := ⟨8*chunk.val+k,by have := chunk.isLt; omega⟩
    obtain ⟨source,d,op,acc,mask,loc,hPv,hProducerCta,hLoc,hValue⟩ :=
      singleVisitPvNumeratorOfObservedOutput hp hX hDone hFrame hg hWarp hb (hCta.symm ▸ hLo)
        (hCta.symm ▸ hHi) (hCta.symm ▸ hTrip) (hProducerRow.symm ▸ hRow) col hWait
        (hCta.trans hWCta.symm)
    rw [hProducerRow,hStage,hCta,hPhysicalRow] at hValue
    rw [hStage] at hPv
    have hIssue : X.MmaIssue source d op acc mask := ⟨_,hPv.decoded⟩
    have hSourceCta := hProducerCta.trans hCta
    let cell : Cell := ⟨load.1/l.block,rowOf l load.1,outputColumn stage+col.val⟩
    have hCellEq : tcDataCell l load.1 .s32x32b addr k = cell := by
      rw [show addr = 2^16 * laneBase l load.1 + (outputColumn stage+8*chunk.val) from rfl,
        tcDataCell_warp32 l load.1 k (by
          have hS := outputColumn_range stage
          have hK := chunk.isLt
          omega)]
      simp only [correctionDataRow,cell,col,Nat.add_assoc]
    have hCell : LoadCell l X load k cell :=
      ⟨addr,vals,.s32x32b,hLoad,hLen.symm ▸ hk,hCellEq.symm⟩
    have hStageOp : (PTX.Kernels.TmlFa4Fwd.Mma.pvSite (firstPvBlock false stage)).stage =
        stage := by fin_cases stage <;> rfl
    have hWritten := hPv.outputCell hp hX (tmemRow l g) col
    rw [hStageOp,hSourceCta,hPhysicalRow] at hWritten
    obtain ⟨_,_,hDesc,_,_⟩ := hPv.valueOperand hp hX
    have hMask := (hPv.fixedOperandFields hX).2.2
    have hWrite := writeCell_no_mask_128
      (show op.descriptor.group = .one by rw [hDesc]; rfl)
      (show op.descriptor.m = 128 by rw [hDesc]; rfl)
      (Nat.mod_lt _ (show 0 < 128 by decide))
      (Nat.mod_lt _ (show 0 < 128 by decide)) hWritten
    rw [hMask] at hIssue
    have hProducer : X.MmaCell source cell :=
      ⟨d,op,acc,List.replicate 4 0,rowOf l load.1,col,hIssue,hWrite⟩
    have hBefore := mmaDoneBeforeFinalizationLoad hp hX stage chunk he hIssue hSourceCta hLoc
    have hNe : source ≠ load := by
      intro h
      have hPvEvent := hPv.decoded
      rw [h,he] at hPvEvent
      exact TcKind.noConfusion (Kind.tc.inj (congrArg Event.kind (Option.some.inj hPvEvent)))
    have hRead : ReadSource l X .ld source load cell := by
      refine ⟨hNe,.inl hProducer,.inl (.inl hBefore),?_,?_⟩
      · intro other hw
        obtain ⟨hOtherCta,f,d',op',acc',mask',hOther⟩ := singleVisitOutputWriter hp hX
          hDone hFrame hb hLo hHi hTrip stage ⟨rowOf l load.1,Nat.mod_lt _ (by decide)⟩ col hw
        have hSame := hOtherCta.trans hSourceCta.symm
        by_cases hLast : f.val = 7
        · obtain rfl : f = 7 := Fin.ext hLast
          exact .inl (hOther.tailUnique hp hX stage hPv hSame)
        · have hLt : f.val < (7 : Fin 8).val := by have := f.isLt; dsimp; omega
          exact .inr (.inl (.inl (.inr (tailPvPipeline hp hX stage hOther hPv hSame hLt))))
      · intro c r hMem hCover release hRelease
        obtain ⟨hOwn,hDealloc⟩ := allocationReleaseInOwnerCta hX hMem hRelease
        obtain ⟨_,_,_,hCellOwner,_,_,_⟩ := hCover
        exact .inl (Safety.tensorOperationsCompletedBeforeRelease hp hX
          (hFrame.metadataProtected hp).1 (hCellOwner.trans hOwn.symm) hDealloc)
    obtain ⟨v,hGet,hMatch⟩ := hX.tcRead.1 _ _ _ _ _ _ _ _ hLoad hCell hRead (.inl hValue)
    rcases hMatch with ⟨_,rfl⟩ | ⟨hBad,_⟩
    · simpa only [List.getElem?_ofFn,hk,↓reduceDIte,col,coords,row,reference,fl] using hGet
    · cases hBad
  · have hL : vals.length ≤ k := by omega
    rw [List.getElem?_eq_none hL,List.getElem?_ofFn,dite_eq_right (by simpa using hk)]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
