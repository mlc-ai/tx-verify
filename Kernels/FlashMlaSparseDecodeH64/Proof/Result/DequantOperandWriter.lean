-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.DequantStorePublication
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantStorePayload
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantByteGeometry

@[expose] public section

/-! # The BF16 writer supplying an MMA's dequantized tile generation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing Protocol MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An actual B operand has a preceding BF16 store of the same block, at its exact shared
byte and by the lane responsible for its logical row and feature. -/
theorem dequant_operand_source
    {cta issuer i : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer) (hc : ctaOf L issuer = cta)
    (he : X.get (issuer, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)))
    (hsite : Wg1MmaGemmTrace.completed .dequant d.site = true)
    (slot : Fin 64) (feature : Fin 512) (b : Fin 2) :
    let g := GemmRing.producer L cta (dequantLane slot feature)
    let byte : Loc := ⟨.shared, cta, TcShared.Swizzle.offset .b128
      (kvLinearByte L d.i slot.val feature.val b.val)⟩
    ∃ (j : Nat) (w : Wg2.D) (a : Acc) (bs : List Byte),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) ∧
      w.block = d.i ∧
      (∃ (r : Fin 4) (step : Fin 8), w.site = .store r step ∧
        r.val = slot.val / 16 ∧ step.val = feature.val / 64) ∧
      X.Writes (g, j) a bs ∧ a.Covers byte ∧
      wbyte a bs byte = some (.float .bf16
        (dequant (Wg2.gatheredByte P L g d.i slot.val) feature.val), b.val) ∧
      ProxyBefore L X (g, j) (issuer, i) byte := by
  dsimp only
  let lane := dequantLane slot feature
  let g := GemmRing.producer L cta lane
  let r : Fin 4 := ⟨slot.val / 16, by omega⟩
  let step : Fin 8 := ⟨feature.val / 64, by omega⟩
  let elem : Fin 8 := ⟨feature.val % 8, by omega⟩
  let phase : Fin 2 := ⟨d.i % 2, by omega⟩
  let m := GemmRing.full L cta phase
  let byte : Loc := ⟨.shared, cta, TcShared.Swizzle.offset .b128
    (kvLinearByte L d.i slot.val feature.val b.val)⟩
  have hgI := Frame.lt_of_get hX he
  have hp := Wg1MmaGemmTrace.composed_count_here hpre hgI .dequant
    ((hs issuer hgI).machine.produces (hX.thr issuer hgI)) hd (show d.i % 2 = phase.val by rfl)
  simp only [hsite, ↓reduceIte] at hp
  change okPolls (GemmRing.full L (ctaOf L issuer) phase) ((X.tr issuer).take i) =
    d.i / 2 + 1 at hp
  rw [hc] at hp
  change okPolls m ((X.tr issuer).take i) = d.i / 2 + 1 at hp
  obtain ⟨k, tag, parity, acquire, scope, _, hk, hKCount⟩ := Poll.exists_nth hp.ge
  obtain ⟨rfl, _⟩ := RingSourceSites.actual_wait_acquire hX hk rfl
  obtain ⟨_, w, _, j, f, u, a, _, _, _, _, hwblock, hwSite, hw, hfget, hf, hwr,
    hloc, hsize, _, _⟩ :=
    DequantStorePublication.store_of_wait hpre hX hs hmma hk hKCount lane r step
  have hb : w.block = d.i := by
    rw [hwblock]
    change 2 * (d.i / 2) + d.i % 2 = d.i
    omega
  obtain ⟨hCta, hRow, hFeature⟩ := dequantCoordinates hpre cta slot feature
  change ctaOf L g = cta at hCta
  change Wg2.rawRow L g r.val = slot.val at hRow
  change Wg2.logicalElem L g step.val elem.val = feature.val at hFeature
  obtain ⟨fp, bs, hwrite, hval⟩ := dequant_store_payload hpre hX hs hfget hw hwSite hf elem b
  rw [hb, hCta, hRow, hFeature] at hval
  change wbyte fp bs byte = _ at hval
  let bytes := (Wg2.Numeric.dequantChunk w.raw
    (Wg2.Numeric.byteAt w.sc (Wg2.scaleIdx L g step.val))).toBytes
  have hwActual : X.Writes (g, j) a bytes := by
    obtain ⟨tag, kind⟩ := f
    have hk : kind = .wr a bytes := hwr
    exact ⟨tag, by rw [show X.get (g, j) = _ from hfget, hk]⟩
  have hfp := (hwrite.unique (.inl hwActual)).1
  have hbyte : a.loc.at (2 * elem.val + b.val) = byte := by
    rw [hloc]
    simp only [Loc.at, byte, Loc.mk.injEq, true_and]
    rw [← hRow, ← hFeature, dequantized_mmaByte hpre]
    change L.sharedBase + Wg2.tileBase (d.i % 2) + Wg2.tileOff L g r.val step.val +
      (2 * elem.val + b.val) = _
    omega
  have hcov : fp.Covers byte := by
    rw [← hbyte]
    exact (hfp.covers _).2 (Acc.covers_at (by rw [hsize]; omega))
  have hProxy : ProxyBefore L X (g, j) (issuer, i) byte :=
    GemmRing.dequant_proxy_before_consumer (slot := phase) hpre hX
      (fun p h => (hs p h).machine) hmma hc he hd hsite rfl hfget hw
      ⟨r, step, hwSite⟩ hb ⟨a, bytes, hwr⟩ rfl rfl
  obtain hwrite | ⟨_, hAtomic⟩ := hwrite
  · exact ⟨j, w, fp, bs, hw, hb, ⟨r, step, hwSite, rfl, rfl⟩, hwrite, hcov, hval, hProxy⟩
  · obtain ⟨_, hrmw⟩ := hAtomic
    have hkind := congrArg Event.kind (Option.some.inj (hfget.symm.trans hrmw))
    rw [hwr] at hkind
    cases hkind

/-- A concrete operand read follows the covering dequantization store of that block. -/
theorem dequant_operand_writer
    {cta issuer i index : Nat} {d : Wg1Mma.D} {e : Event} {value : Option Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer) (hc : ctaOf L issuer = cta)
    (he : X.get (issuer, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)))
    (hsite : Wg1MmaGemmTrace.completed .dequant d.site = true)
    (slot : Fin 64) (feature : Fin 512) (b : Fin 2)
    (hread : X.MmaRead (issuer, i) true index
      ⟨.shared, cta, TcShared.Swizzle.offset .b128
        (kvLinearByte L d.i slot.val feature.val b.val)⟩ value) :
    let g := GemmRing.producer L cta (dequantLane slot feature)
    let byte : Loc := ⟨.shared, cta, TcShared.Swizzle.offset .b128
      (kvLinearByte L d.i slot.val feature.val b.val)⟩
    ∃ (j : Nat) (w : Wg2.D) (a : Acc) (bs : List Byte),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) ∧
      w.block = d.i ∧
      (∃ (r : Fin 4) (step : Fin 8), w.site = .store r step ∧
        r.val = slot.val / 16 ∧ step.val = feature.val / 64) ∧
      X.Writes (g, j) a bs ∧ a.Covers byte ∧
      wbyte a bs byte = some (.float .bf16
        (dequant (Wg2.gatheredByte P L g d.i slot.val) feature.val), b.val) ∧
      ByteCausality L X byte (.thread (g, j)) (.async (issuer, i) (.mmaRead true index)) := by
  dsimp only
  obtain ⟨j, w, fp, bs, hw, hb, hSite, hwrite, hcov, hval, hProxy⟩ :=
    dequant_operand_source hpre hX hs hmma hc he hd hsite slot feature b
  have hA : AsyncCovers X (issuer, i) (.mmaRead true index)
      ⟨.shared, cta, TcShared.Swizzle.offset .b128
        (kvLinearByte L d.i slot.val feature.val b.val)⟩ :=
    ⟨{loc := _, size := 1}, false, ⟨rfl, rfl, hread.1⟩,
      Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  exact ⟨j, w, fp, bs, hw, hb, hSite, hwrite, hcov, hval, .direct ⟨hA, .inl hProxy⟩⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
