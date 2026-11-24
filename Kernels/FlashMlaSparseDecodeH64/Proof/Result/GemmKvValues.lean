-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmInputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmValues
import Lemmas.Order.Order

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open MmaDataTrace PTX.Proof

noncomputable section

/-- A chosen shared writer supplies the observed operand byte. The writer may cover a
larger access than this byte. -/
theorem operand_byte_from_writer {L : Launch} {X : Execution} {mem0 : Mem0}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {i : EvId} {base : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} (hi : X.MmaIssue i base s acc mask)
    (ho : X.async.mmaOperands i = some ops)
    {isB : Bool} {index : Nat} {l : Loc} {value : Byte}
    (hl : s.byteLoc (if isB then .b else .a) index = some l)
    {w : AsyncCopy.Ref} {dst : Acc} {bs : List Byte}
    (hw : X.MemWrites w dst bs) (hv : wbyte dst bs l = some value)
    (hrf : X.rf (.async i (.mmaRead isB index)) 0 = some w) :
    (if isB then ops.b else ops.a)[index]? = some (some value) := by
  obtain ⟨observed, hr, hget⟩ := hX.mma_read_exists hi ho hl
  have hread : X.MemReads (.async i (.mmaRead isB index)) { loc := l, size := 1 } [observed] :=
    ⟨observed, hr, rfl, rfl⟩
  have h := (hX.rf _ _ _ hread).2 0 (Nat.zero_lt_succ 0)
  rw [hrf] at h
  obtain ⟨dst', bs', hw', _, hval⟩ := h
  obtain ⟨hfp, rfl⟩ := hw.unique hw'
  have hv' : wbyte dst' bs ({ loc := l, size := 1 : Acc }.loc.at 0) = some value := by
    simpa only [wbyte, ← hfp.1, Loc.at, Nat.add_zero] using hv
  have he : observed = some value := by
    simpa only [List.getElem?_cons_zero, Option.some.injEq] using hval.trans (congrArg some hv')
  rw [← he]
  exact hget

/-- An actual dequantizing store supplies the requested BF16 value at its swizzled address. -/
theorem dequantized_write_byte {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) {g j : Nat} {d : Wg2.D} {e : Event} {u : TState}
    {r : Fin 4} {s : Fin 8} (hd : d.site = .store r s) (hbuf : d.buf = d.block % 2)
    (he : X.get (g, j) = some e) (hf : (Wg2.machine P L g).Fired (some (.inr d)) e (some u))
    {row : Nat → Nat}
    (hw : ∀ k < Wg2.rawBytesPerThread, Wg2.Numeric.byteAt d.raw k = row (Wg2.elemByte L g s.val k))
    (hs : Wg2.Numeric.byteAt d.sc (Wg2.scaleIdx L g s.val) = row (512 + Wg2.scaleIdx L g s.val))
    (elem : Fin 8) (byte : Fin 2) :
    let feature := Wg2.logicalElem L g s.val elem.val
    let l : Loc := ⟨.shared, ctaOf L g, TcShared.Swizzle.offset .b128
      (kvLinearByte L d.block (Wg2.rawRow L g r.val) feature byte.val)⟩
    ∃ a bs, X.MemWrites (.thread (g, j)) a bs ∧
      wbyte a bs l = some (.float .bf16 (dequant row feature), byte.val) := by
  obtain ⟨a, hkind, hloc, _⟩ := Wg2.fired_store_event hpre hd hf
  let bytes := (Wg2.Numeric.dequantChunk d.raw
    (Wg2.Numeric.byteAt d.sc (Wg2.scaleIdx L g s.val))).toBytes
  refine ⟨a, bytes, ?_, ?_⟩
  · cases e
    exact .inl ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hkind))⟩
  · unfold wbyte
    rw [hloc, hbuf, dequantized_mmaByte hpre]
    have hsub : L.sharedBase + Wg2.tileBase (d.block % 2) + Wg2.tileOff L g r.val s.val +
        2 * elem.val + byte.val -
        (L.sharedBase + Wg2.tileBase (d.block % 2) + Wg2.tileOff L g r.val s.val) =
        2 * elem.val + byte.val := by omega
    rw [hsub]
    exact dequantized_payload_byte hw hs elem byte

/-- The unique dequantizer lane of a logical sparse token and feature. -/
def dequantLane (slot : Fin 64) (feature : Fin 512) : Fin 128 :=
  ⟨8 * (slot.val % 16) + feature.val / 8 % 8, by omega⟩

/-- Each logical input byte of the GEMMs is owned by a dequantizer lane and one of its chunks. -/
theorem dequantCoordinates {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (cta : Nat) (slot : Fin 64) (feature : Fin 512) :
    let g := cta * L.block + 256 + (dequantLane slot feature).val
    let r : Fin 4 := ⟨slot.val / 16, by omega⟩
    let s : Fin 8 := ⟨feature.val / 64, by omega⟩
    let j : Fin 8 := ⟨feature.val % 8, by omega⟩
    ctaOf L g = cta ∧ Wg2.rawRow L g r.val = slot.val ∧
      Wg2.logicalElem L g s.val j.val = feature.val := by
  let g := cta * L.block + 256 + (dequantLane slot feature).val
  let lane := 8 * (slot.val % 16) + feature.val / 8 % 8
  have hl : lane < 128 := by dsimp [lane]; omega
  have ht : tidOf L g = 256 + lane := by
    rw [tidOf_eq hpre]
    change (cta * L.block + 256 + lane) % 384 = 256 + lane
    rw [hpre.block]
    omega
  have hc : ctaOf L g = cta := by
    change (cta * L.block + 256 + lane) / L.block = cta
    rw [hpre.block]
    omega
  dsimp only
  refine ⟨hc, ?_, ?_⟩
  · change Wg2.rawRow L g (slot.val / 16) = slot.val
    simp only [Wg2.rawRow, Wg2.groupIdx, Wg2.idxInWg, ht, Wg2.numGroups, Wg2.groupSize]
    dsimp [lane]
    omega
  · change Wg2.logicalElem L g (feature.val / 64) (feature.val % 8) = feature.val
    simp only [Wg2.logicalElem, Wg2.idxInGroup, ht, Wg2.groupSize,
      Wg2.elemsPerStep, Wg2.rawBytesPerThread]
    dsimp [lane]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
