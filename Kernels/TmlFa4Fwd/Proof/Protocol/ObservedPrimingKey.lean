-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderCopyBytes
public import Kernels.TmlFa4Fwd.Proof.MmaQkResult
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinates
import Kernels.TmlFa4Fwd.Proof.Thread.ObservedPrimingKey

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (producer producerLaneMod PublishedCopyGroup readyObject)
open PTX.Kernels.TmlFa4Fwd.Loader (primingScratchPage readyProducer)
open Mma (qkOperands qkLoaderCoordinates qkLoaderLane qkLoaderByte qkByteIndex qkKey
  qkPlaneColumn_lt qkKCopyByteLoc trips)
open Epilogue (assignedCoordinates)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {batch : Nat}
    {wait mma : EvId} {d : Nat} {accum : Bool} {mask : List Nat} (hReady : Completed l X wait 0 0)
    (block : Fin 4) (step : Fin 8) {row k byte : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ mma.1 / l.block)
    (hHi : mma.1 / l.block < tilePrefix p (batch + 1) * p.heads) (hr : row < 128) (hk : k < 16)
    (hByte : byte < 2) (hMma : X.MmaIssue mma d (qkOperands l mma.1 block step 0) accum mask)
include hp hX hFrame hReady block step hb hLo hHi hr hk hByte hMma

/-- The completed initial K acquire identifies the publication supplying the selected byte. -/
theorem Completed.initialKeyOperandWithPublication (hAfter : TraceBefore X wait mma) :
    let coords := assignedCoordinates p batch (mma.1 / l.block)
    let key := 128 * (trips p batch coords.1 - 1) + row
    let read := Ref.async mma (.mmaRead true (qkByteIndex row k byte))
    ∃ (loc : Loc) (publication : EvId) (group : PublishedCopyGroup l X publication)
        (j : Nat) (s : Spec),
      X.AsyncArrive publication (readyObject l wait.1 0) true ∧
      generation l X publication 0 = 0 ∧ (j,s) ∈ group.copies ∧
      X.Copy (publication.1,j) s ∧ s.dst.Covers loc ∧ publication.1/l.block = mma.1/l.block ∧
      (qkOperands l mma.1 block step 0).byteLoc .b (qkByteIndex row k byte) = some loc ∧
      ((∀ other access bytes, X.MemWrites other access bytes → access.Covers loc →
        other = .async (publication.1,j) (.write .copy) ∨
        modelCausality l X loc other (.async (publication.1,j) (.write .copy)) ∨
        modelCausality l X loc read other) →
        Mma.OperandByteSource l X mma true (qkByteIndex row k byte) loc
          (if key < p.kLength batch then
            (Value.float .bf16 (qkKey p batch coords.2 key (16 * step.val + k))).byteAt byte
          else zeroByte)) := by
  dsimp only
  let coords := assignedCoordinates p batch (mma.1 / l.block)
  let tile := trips p batch coords.1 - 1
  let key := 128 * tile + row
  have hCol := qkPlaneColumn_lt step hk
  let lane : Fin 64 := ⟨qkLoaderLane step row k, by unfold qkLoaderLane; omega⟩
  let pair : Fin 16 := ⟨row / 8, by omega⟩
  let upper := decide (4 ≤ step.val)
  let off := qkLoaderByte step k byte
  have hOff : off < 16 := by dsimp [off, qkLoaderByte]; omega
  let loc : Loc := ⟨.shared, mma.1 / l.block,
    kvCopyAddress l.sharedBase (0 : Fin 3) lane pair upper + off⟩
  have hLoc : (qkOperands l mma.1 block step 0).byteLoc .b
      (qkByteIndex row k byte) = some loc :=
    qkKCopyByteLoc l mma.1 block step 0 hp.shared.1 hr hk hByte
  obtain ⟨issue, group, j, spec, bytes, hPublish, hLane, hPhase, hSlot, _,
      hMember, hAddr, hCover, hWrite, hOrder⟩ :=
    hReady.actualOperandCoveringCopyWithPublication hp hX (isB := true)
      (index := qkByteIndex row k byte) lane pair upper hOff hMma hAfter hLoc
      (by simp only [loc, hAfter.1])
  have hPacket := group.initialKeyPacket hp hX hPublish hPhase
  obtain ⟨actualPair, actualUpper, hVector, hDst⟩ :=
    group.primingKeyMember hp hX hPublish hPacket hMember
  have hTid := producerLaneMod hp (wait.1 / l.block) lane
  rw [← hLane] at hTid
  have hBase := congrArg Loc.addr hAddr
  change spec.dst.loc.addr + off =
    kvCopyAddress l.sharedBase (0 : Fin 3) lane.val pair.val upper + off at hBase
  rw [hDst, hSlot] at hBase
  have hEqual : kvCopyAddress l.sharedBase (0 : Fin 3) (issue.1 % l.block)
      actualPair.val actualUpper =
      kvCopyAddress l.sharedBase (0 : Fin 3) (issue.1 % l.block) pair.val upper := by
    have hLaneMod := Nat.mod_eq_of_lt lane.isLt
    simp only [kvCopyAddress, hTid, hLaneMod] at hBase ⊢
    exact Nat.add_right_cancel hBase
  have hCoords : actualPair = pair ∧ actualUpper = upper := by
    by_contra hDifferent
    have hApartCoords : actualPair.val ≠ pair.val ∨ actualUpper ≠ upper := by
      by_cases hPair : actualPair.val = pair.val
      · exact .inr (fun hUpper => hDifferent ⟨Fin.ext hPair, hUpper⟩)
      · exact .inl hPair
    have hApart := kvCopyAddress_apart
      (stage := (0 : Fin 3).val) (lane := issue.1 % l.block) hp.shared.1
      actualPair.isLt pair.isLt hApartCoords
    omega
  obtain ⟨rfl, rfl⟩ := hCoords
  have hCta : mma.1 / l.block = issue.1 / l.block := by
    rw [← hAfter.1]
    exact publicationCta hp hX hPublish
  have hActive : issue.1 / l.block < tilePrefix p p.batch * p.heads := by
    rw [← hCta]
    exact hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (by omega)))
  have hWarp : 14 ≤ Prologue.warpIndex l issue.1 := by
    have hParts := Nat.div_add_mod issue.1 l.block
    rw [← hCta, ← hAfter.1] at hParts
    unfold producer readyProducer at hLane
    rw [Nat.mul_comm (wait.1 / l.block) l.block] at hLane
    change 14 ≤ issue.1 % l.block / 32
    have := lane.isLt
    omega
  obtain ⟨b, hb', hLo', hHi', hHead, hSize, hSource⟩ :=
    hVector.source hp hX hFrame hWarp hActive
  obtain ⟨_, _, hBatch⟩ := tileBatch_existsUnique p hActive
  have hB : b = batch :=
    (hBatch b ⟨hb', hLo', hHi'⟩).trans (hBatch batch ⟨hb, hCta ▸ hLo, hCta ▸ hHi⟩).symm
  subst b
  rw [← hCta] at hHead hSize hSource
  obtain ⟨hRow, hDim, hBit, _⟩ := qkLoaderCoordinates step tile (row := row) hk hByte
  have hRowActual : kvCopyRow tile (issue.1 % l.block) pair.val = key := by
    change kvCopyRow tile lane.val (row / 8) = 128 * tile + row at hRow
    dsimp [kvCopyRow, pair, key] at hRow ⊢
    omega
  have hDimActual : kvCopyColumn (issue.1 % l.block) upper + off / 2 = 16 * step.val + k := by
    change kvCopyColumn lane.val upper + off / 2 = 16 * step.val + k at hDim
    have hLaneMod := congrArg (fun x : Nat => x % 8) hTid
    change (issue.1 % l.block % 64) % 8 = lane.val % 8 at hLaneMod
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 64)] at hLaneMod
    dsimp only [kvCopyColumn] at hDim ⊢
    rw [hLaneMod]
    exact hDim
  change spec.src.size = (if kvCopyRow tile (issue.1 % l.block) pair.val < p.kLength batch
      then 16 else 0) at hSize
  have hSrc (hLive : key < p.kLength batch) :
      spec.src.loc = cacheVector p group.publication.packet.plane batch (coords.2 / 6)
        key (issue.1 % l.block) upper := by
    change spec.src.loc = p.kLayout.loc
        (primingScratchPage p batch (kvCopyRow tile (issue.1 % l.block) pair.val))
        (coords.2 / 6) (kvCopyRow tile (issue.1 % l.block) pair.val % 16)
        (kvCopyColumn (issue.1 % l.block) upper) at hSource
    rw [hSource, hRowActual, hPacket]
    simp only [primingScratchPage, hLive, ↓reduceIte, cacheVector, cacheLayout]
  rw [hRowActual] at hSize
  refine ⟨loc,issue,group,j,spec,hPublish,hPhase,hMember,
    hVector.copy,hCover,hCta.symm,hLoc,?_⟩
  intro hOther
  have hResult := publishedCopyOperandByteSource hp hX hFrame group hMember hb hHead upper
    hSrc hSize hOff hWrite (hAddr.symm ▸ hOrder) (hAddr.symm ▸ hOther)
  rw [hAddr, hPacket] at hResult
  change off % 2 = byte at hBit
  change Mma.OperandByteSource l X mma true (qkByteIndex row k byte) loc
    (if key < p.kLength batch then
      (Value.float .bf16 (qkKey p batch coords.2 key (16 * step.val + k))).byteAt byte
    else zeroByte)
  by_cases hLive : key < p.kLength batch
  · simpa only [cacheByte, hLive, qkKey, ↓reduceIte, hDimActual, hBit] using hResult
  · simpa only [hLive, ↓reduceIte] using hResult

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
