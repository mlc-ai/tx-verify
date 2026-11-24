-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderCopyBytes
public import Kernels.TmlFa4Fwd.Proof.MmaPvResult
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
import Kernels.TmlFa4Fwd.Proof.Thread.ObservedPrimingValue
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueByteOperands
import Kernels.TmlFa4Fwd.Proof.MmaValueBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread (InitialValueFragment)
open Thread.Loader (producer producerLaneMod)
open PTX.Kernels.TmlFa4Fwd.Loader (primingScratchPage readyProducer)
open Mma (pvOperands pvLoaderCoordinates pvLoaderLane pvLoaderByte pvKeyRow qkByteIndex
  pvValue pvFragment pvValueByteLoc trips sharedDescriptor kvStart)
open Epilogue (assignedCoordinates)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {batch : Nat}
    {wait mma : EvId} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hReady : Completed l X wait 1 0) {steady : Bool} (stage : Fin 2) (step : Fin 8)
    {col k byte : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ mma.1/l.block)
    (hHi : mma.1/l.block < tilePrefix p (batch + 1) * p.heads) (hc : col < 128) (hk : k < 16)
    (hByte : byte < 2) (hFragment : InitialValueFragment X mma steady stage step d op accum mask)
    (hB : op.b = sharedDescriptor (kvStart l 1 + pvFragment step) 16384)
    (hMma : X.MmaIssue mma d op accum mask)
include hp hX hFrame hReady stage step hb hLo hHi hc hk hByte hFragment hB hMma

/-- The completed slot-one acquire identifies the V publication and the actual copy
that provides the selected operand byte or its zero fill. -/
theorem Completed.initialValueOperandWithPublication (hAfter : TraceBefore X wait mma) :
    let coords := assignedCoordinates p batch (mma.1/l.block)
    let key := 128 * (trips p batch coords.1 - 1) + pvKeyRow step k
    let read := Ref.async mma (.mmaRead true (qkByteIndex col k byte))
    ∃ (loc : Loc) (publication : EvId) (group : Thread.Loader.PublishedCopyGroup l X publication)
        (j : Nat) (s : Spec),
      X.AsyncArrive publication (Thread.Loader.readyObject l wait.1 1) true ∧
      generation l X publication 1 = 0 ∧ (j,s) ∈ group.copies ∧
      X.Copy (publication.1,j) s ∧ s.dst.Covers loc ∧ publication.1/l.block = mma.1/l.block ∧
      op.byteLoc .b (qkByteIndex col k byte) = some loc ∧
      ((∀ other access bytes, X.MemWrites other access bytes → access.Covers loc →
        other = .async (publication.1,j) (.write .copy) ∨
        modelCausality l X loc other (.async (publication.1,j) (.write .copy)) ∨
        modelCausality l X loc read other) →
        Mma.OperandByteSource l X mma true (qkByteIndex col k byte) loc
          (if key < p.kLength batch then
            (Value.float .bf16 (pvValue p batch coords.2 key col)).byteAt byte
          else zeroByte)) := by
  dsimp only
  let coords := assignedCoordinates p batch (mma.1/l.block)
  let tile := trips p batch coords.1-1
  let row := pvKeyRow step k
  let key := 128 * tile + row
  have hRowBound : row < 128 := by
    have := step.isLt
    unfold row pvKeyRow
    omega
  let lane : Fin 64 := ⟨pvLoaderLane step col k, by unfold pvLoaderLane; omega⟩
  let pair : Fin 16 := ⟨row/8, by omega⟩
  let upper := decide (64 ≤ col)
  let off := pvLoaderByte col byte
  have hOff : off < 16 := by dsimp [off,pvLoaderByte]; omega
  let loc : Loc := ⟨.shared,mma.1/l.block,kvCopyAddress l.sharedBase (1 : Fin 3)
    lane pair upper + off⟩
  have hLoc : op.byteLoc .b (qkByteIndex col k byte) = some loc := by
    rw [hFragment.valueByteLoc hp hX hB]
    simpa [loc,lane,pair,upper,off,pvLoaderLane,pvLoaderByte,Mma.kvSlot,Nat.add_assoc] using
      pvValueByteLoc l mma.1 (Thread.firstPvBlock steady stage) step 1
      hp.shared.1 hc hk hByte
  obtain ⟨issue,group,j,spec,bytes,hPublish,hLane,hPhase,hSlot,_,hMember,hAddr,hCover,
    hWrite,hOrder⟩ := hReady.actualOperandCoveringCopyWithPublication hp hX (isB := true)
      (index := qkByteIndex col k byte) lane pair upper hOff hMma hAfter hLoc
      (by simp only [loc,hAfter.1])
  have hPacket := group.initialValuePacket hp hX hPublish hPhase
  obtain ⟨actualPair,actualUpper,hVector,hDst⟩ :=
    group.primingValueMember hp hX hPublish hPacket hMember
  have hTid := producerLaneMod hp (wait.1/l.block) lane
  rw [← hLane] at hTid
  have hBase := congrArg Loc.addr hAddr
  change spec.dst.loc.addr + off =
    kvCopyAddress l.sharedBase (1 : Fin 3) lane.val pair.val upper + off at hBase
  rw [hDst,hSlot] at hBase
  have hEqual : kvCopyAddress l.sharedBase (1 : Fin 3) (issue.1%l.block)
      actualPair.val actualUpper =
      kvCopyAddress l.sharedBase (1 : Fin 3) (issue.1%l.block) pair.val upper := by
    have hLaneMod := Nat.mod_eq_of_lt lane.isLt
    simp only [kvCopyAddress,hTid,hLaneMod] at hBase ⊢
    exact Nat.add_right_cancel hBase
  have hCoords : actualPair = pair ∧ actualUpper = upper := by
    by_contra hDifferent
    have hApartCoords : actualPair.val ≠ pair.val ∨ actualUpper ≠ upper := by
      by_cases hPair : actualPair.val = pair.val
      · exact .inr (fun hUpper => hDifferent ⟨Fin.ext hPair,hUpper⟩)
      · exact .inl hPair
    have hApart := kvCopyAddress_apart
      (stage := (1 : Fin 3).val) (lane := issue.1%l.block) hp.shared.1
      actualPair.isLt pair.isLt hApartCoords
    omega
  obtain ⟨rfl,rfl⟩ := hCoords
  have hCta : mma.1/l.block = issue.1/l.block := by
    rw [← hAfter.1]
    exact publicationCta hp hX hPublish
  have hActive : issue.1/l.block < tilePrefix p p.batch * p.heads := by
    rw [← hCta]
    exact hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (by omega)))
  have hWarp : 14 ≤ Prologue.warpIndex l issue.1 := by
    have hParts := Nat.div_add_mod issue.1 l.block
    rw [← hCta,← hAfter.1] at hParts
    unfold producer readyProducer at hLane
    rw [Nat.mul_comm (wait.1/l.block) l.block] at hLane
    change 14 ≤ issue.1%l.block/32
    have := lane.isLt
    omega
  obtain ⟨b,hb',hLo',hHi',hHead,hSize,hSource⟩ := hVector.source hp hX hFrame hWarp hActive
  obtain ⟨_,_,hBatch⟩ := tileBatch_existsUnique p hActive
  have hBch : b = batch :=
    (hBatch b ⟨hb',hLo',hHi'⟩).trans (hBatch batch ⟨hb,hCta ▸ hLo,hCta ▸ hHi⟩).symm
  subst b
  rw [← hCta] at hHead hSize hSource
  obtain ⟨hRow,hDim,hBit,_⟩ := pvLoaderCoordinates step tile (k := k) hc hByte
  have hRowActual : kvCopyRow tile (issue.1%l.block) pair.val = key := by
    change kvCopyRow tile lane.val (row/8) = 128 * tile + row at hRow
    dsimp [kvCopyRow,pair,key] at hRow ⊢
    omega
  have hDimActual : kvCopyColumn (issue.1%l.block) upper + off/2 = col := by
    change kvCopyColumn lane.val upper + off/2 = col at hDim
    have hLaneMod := congrArg (fun x : Nat => x%8) hTid
    change (issue.1%l.block%64)%8 = lane.val%8 at hLaneMod
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 64)] at hLaneMod
    dsimp only [kvCopyColumn] at hDim ⊢
    rw [hLaneMod]
    exact hDim
  change spec.src.size = (if kvCopyRow tile (issue.1%l.block) pair.val < p.kLength batch
      then 16 else 0) at hSize
  have hSrc (hLive : key < p.kLength batch) :
      spec.src.loc = cacheVector p group.publication.packet.plane batch (coords.2/6)
        key (issue.1%l.block) upper := by
    change spec.src.loc = p.vLayout.loc
        (primingScratchPage p batch (kvCopyRow tile (issue.1%l.block) pair.val))
        (coords.2/6) (kvCopyRow tile (issue.1%l.block) pair.val%16)
        (kvCopyColumn (issue.1%l.block) upper) at hSource
    rw [hSource,hRowActual,hPacket]
    simp only [primingScratchPage,hLive,↓reduceIte,cacheVector,cacheLayout]
  rw [hRowActual] at hSize
  refine ⟨loc,issue,group,j,spec,hPublish,hPhase,hMember,hVector.copy,hCover,hCta.symm,hLoc,?_⟩
  intro hOther
  have hResult := publishedCopyOperandByteSource hp hX hFrame group hMember hb hHead upper
    hSrc hSize hOff hWrite (hAddr.symm ▸ hOrder) (hAddr.symm ▸ hOther)
  rw [hAddr,hPacket] at hResult
  change off%2 = byte at hBit
  change Mma.OperandByteSource l X mma true (qkByteIndex col k byte) loc
    (if key < p.kLength batch then
      (Value.float .bf16 (pvValue p batch coords.2 key col)).byteAt byte
      else zeroByte)
  by_cases hLive : key < p.kLength batch
  · simpa only [cacheByte,hLive,pvValue,↓reduceIte,hDimActual,hBit] using hResult
  · simpa only [hLive,↓reduceIte] using hResult

/-- The completed slot-one acquire identifies the V publication and the actual copy
that provides the selected operand byte or its zero fill. -/
theorem Completed.initialValueOperand (hAfter : TraceBefore X wait mma) :
    let coords := assignedCoordinates p batch (mma.1/l.block)
    let key := 128 * (trips p batch coords.1 - 1) + pvKeyRow step k
    let read := Ref.async mma (.mmaRead true (qkByteIndex col k byte))
    ∃ loc copy s, X.Copy copy s ∧ s.dst.Covers loc ∧ copy.1/l.block = mma.1/l.block ∧
      op.byteLoc .b (qkByteIndex col k byte) = some loc ∧
      ((∀ other access bytes, X.MemWrites other access bytes → access.Covers loc →
        other = .async copy (.write .copy) ∨
        modelCausality l X loc other (.async copy (.write .copy)) ∨
        modelCausality l X loc read other) →
        Mma.OperandByteSource l X mma true (qkByteIndex col k byte) loc
          (if key < p.kLength batch then
            (Value.float .bf16 (pvValue p batch coords.2 key col)).byteAt byte
          else zeroByte)) := by
  obtain ⟨loc,publication,_,j,s,_,_,_,hCopy,hCover,hOwner,hLoc,hValue⟩ :=
    hReady.initialValueOperandWithPublication hp hX hFrame stage step hb hLo hHi hc hk hByte
      hFragment hB hMma hAfter
  exact ⟨loc,(publication.1,j),s,hCopy,hCover,hOwner,hLoc,hValue⟩

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
