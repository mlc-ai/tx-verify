-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PvVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalPvVisit
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemFinalLoadProvenance
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.TcMma Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Protocol (PvVisit)

noncomputable section

/-- The actual finalizer loads the terminal PV bank of its selected stage and row.
Its visit ordinal is exactly the last block of the selected request. -/
theorem finalizationLoadValuesOfTerminalPv {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (stage : Fin 2) (chunk : Fin 16) {load : EvId} {batch addr : Nat}
    {vals : List Value} {shape : TcShape}
    (he : X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld addr vals shape)⟩)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ load.1/l.block)
    (hHi : load.1/l.block < tilePrefix p (batch+1)*p.heads)
    (numerator : Nat → ℝ) :
    let coords := assignedCoordinates p batch (load.1/l.block)
    let use := 2*trips p batch coords.1-1
    let row : Fin 128 := ⟨rowOf l load.1,Nat.mod_lt _ (by decide)⟩
    (∀ k : Fin 8, ∀ (source : EvId),
      let col : Fin 128 := ⟨8*chunk.val+k.val,by have := chunk.isLt; have := k.isLt; omega⟩
      let cell : Cell := ⟨load.1/l.block,row.val,outputColumn stage+col.val⟩
      source.1/l.block = load.1/l.block →
      ReadSource l X .ld source load cell →
      X.async.mmaDone source = true →
      PvVisit l X source.1 (firstPvBlock false stage) use row col source.2 →
      TcMma.Result l Assumptions.all X source cell (.float .f32 (numerator col.val))) →
    vals = List.ofFn (fun k : Fin 8 => fl (numerator (8*chunk.val+k.val))) := by
  dsimp only
  intro hNumerator
  obtain ⟨rfl,rfl,hLen⟩ := finalizeLoadActualAddress hp hX stage chunk he
  let addr := outputAddress l load.1 stage (8*chunk.val)
  have hLoad : X.TLd load addr vals .s32x32b := ⟨_,he⟩
  let row : Fin 128 := ⟨rowOf l load.1,Nat.mod_lt _ (by decide)⟩
  have hCuQ := ((hFrame X hX).metadataProtected hp).1
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 8
  · let k : Fin 8 := ⟨j,hj⟩
    let col : Fin 128 := ⟨8*chunk.val+k.val,by have := chunk.isLt; omega⟩
    let cell : Cell := ⟨load.1/l.block,row.val,outputColumn stage+col.val⟩
    have hJ : j < vals.length := hLen.symm ▸ hj
    have hCellEq : tcDataCell l load.1 .s32x32b addr j = cell := by
      rw [show addr = 2^16 * laneBase l load.1 + (outputColumn stage+8*chunk.val) from rfl,
        tcDataCell_warp32 l load.1 j (by
          have := outputColumn_range stage
          have := chunk.isLt
          omega)]
      have hLane : laneBase l load.1 + laneOf l load.1 = rowOf l load.1 := by
        unfold laneBase laneOf rowOf
        omega
      simp only [hLane,cell,row,col,k,Nat.add_assoc]
    have hWord : FinalizationLoadCell l X load cell stage :=
      FinalizationLoadCell.ofDecoded chunk he hJ hCellEq.symm
    obtain ⟨source,d,op,accum,mask,hPv,hWrites,hRead,hComplete⟩ :=
      Safety.finalizationLoadSourceWithTerminalPv hp hX hCuQ hWord
    have hOwner : source.1/l.block = load.1/l.block := by
      have h := mmaWrittenCellCta hp hX hWrites
      exact h.symm
    rcases source with ⟨g,index⟩
    have hUse := Thread.Mma.terminalFragmentUseOfCompletedWork hp hX hDone hFrame
      hPv hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
    rw [hOwner] at hUse
    obtain ⟨v⟩ := PvVisit.ofLast hp hX hCuQ hPv hUse row col
    have hResult := hNumerator k (g,index) hOwner hRead hComplete v
    have hCell : LoadCell l X load j cell := ⟨addr,vals,.s32x32b,hLoad,hJ,hCellEq.symm⟩
    have hActual := hX.tcRead.1.f32 hLoad hCell hRead (.inl hResult)
    simpa only [List.getElem?_ofFn,hj,↓reduceDIte,k,col,fl] using hActual
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by simp; omega)]

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
