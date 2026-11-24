-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.DequantByteGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryWriters

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingStageQkHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate

@[expose] public section

/-! # Actual writes that can supply a shared KV operand byte -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy Protocol MmaDataTrace MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The physical shared location of one byte of a logical KV operand. -/
def kvOperandLoc (L : Launch) (cta block : Nat) (slot : Fin 64) (feat : Fin 512)
    (b : Fin 2) : Loc :=
  ⟨.shared, cta, TcShared.Swizzle.offset .b128 (kvLinearByte L block slot.val feat.val b.val)⟩

theorem kv_operand_region (hpre : Pre P L mem0) (cta block : Nat) (slot : Fin 64)
    (feat : Fin 512) (b : Fin 2) :
    L.sharedBase + 65536 * (block % 2) ≤ (kvOperandLoc L cta block slot feat b).addr ∧
    (kvOperandLoc L cta block slot feat b).addr < L.sharedBase + 65536 * (block % 2) + 65536 := by
  let n := kvLinearByte L block slot.val feat.val b.val
  have hlo : (L.sharedBase + 65536 * (block % 2)) % 128 = 0 := by
    rw [hpre.sharedBase]
    have hAlign := hpre.sharedAlignment
    omega
  have hs := slot.isLt
  have hf := feat.isLt
  have hb := b.isLt
  change L.sharedBase + 65536 * (block % 2) ≤ TensorSwizzle.offset .b128 0 n ∧
    TensorSwizzle.offset .b128 0 n < L.sharedBase + 65536 * (block % 2) + 65536
  have hrow := TensorSwizzle.offset_row .b128 0 n
  simp only [n, kvLinearByte, Wg1Mma.kvBase] at hrow ⊢
  omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

private theorem dequant_writer_coordinates {cta block : Nat} {slot : Fin 64} {feat : Fin 512}
    {b : Fin 2} {i : EvId} {a : Acc} {bs : List Byte} {d : Wg2.D} {r : Fin 4} {s : Fin 8}
    (hw : X.Writes i a bs) (ha : a.Covers (kvOperandLoc L cta block slot feat b))
    (hCta : cta = ctaOf L i.1)
    (hd : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)))
    (hSite : d.site = .store r s) :
    i.1 = GemmRing.producer L cta (dequantLane slot feat) ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧
          d.site = .store r s ∧ r.val = slot.val / 16 ∧ s.val = feat.val / 64 ∧
          d.block % 2 = block % 2 := by
  obtain ⟨⟨g, j⟩, rfl⟩ : ∃ pair : EvId, i = pair := ⟨i, rfl⟩
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  have hWg := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  obtain ⟨lane, hgEq⟩ := RawRing.consumer_of_wg2 hpre hCta.symm hWg
  change g = RawRing.consumer L cta lane at hgEq
  subst g
  obtain ⟨u, hf⟩ := ((hs _ hg).machine.produces (hX.thr _ hg)).fired_at he hd
  cases u with
  | none =>
    obtain ⟨_, _, hFires⟩ := hf
    rcases fires_none_ends hFires with ⟨_, hh⟩ | hh <;> cases hh
  | some u =>
    have hf' : (Wg2.machine P L (GemmRing.producer L cta lane)).Fired (some (.inr d))
        ⟨hw.choose, .wr a bs⟩ (some u) := hf
    have hInv : Wg2.Inv P L (GemmRing.producer L cta lane) d := hf'.choose_spec.1.2
    obtain ⟨sub, hAddr⟩ := OutputStageReuse.dequantStoreByte_of_cover hpre hSite hf' he hw ha
    rw [hInv.bufBlock] at hAddr
    obtain ⟨hPhase, hLane, hRow, hStep, _⟩ := dequant_store_coordinates hpre hAddr.symm
    refine ⟨congrArg (RawRing.consumer L cta) hLane, d, r, s, ?_,
      hSite, hRow, hStep, hPhase⟩
    exact hd

/-- An ordinary writer of an operand byte is either its unique dequantization lane and
chunk in some generation, or an actual staging instruction of that CTA. -/
theorem kv_ordinary_writer (ht : Frame.Tracked (Machine.code P L) X) {cta block : Nat}
    {slot : Fin 64} {feat : Fin 512} {b : Fin 2} {i : EvId} {a : Acc} {bs : List Byte}
    (hw : X.Writes i a bs) (ha : a.Covers (kvOperandLoc L cta block slot feat b)) :
    (i.1 = GemmRing.producer L cta (dequantLane slot feat) ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg2 d)) ∧
          d.site = .store r s ∧ r.val = slot.val / 16 ∧ s.val = feat.val / 64 ∧
          d.block % 2 = block % 2) ∨
    (block % 2 = 1 ∧ ctaOf L i.1 = cta ∧
      ∃ (d : Wg0.D) (tile : Fin 4) (chunk : Fin 8),
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.wg0 d)) ∧
          d.site = .oStage tile chunk) := by
  let l := kvOperandLoc L cta block slot feat b
  have ⟨_, hi⟩ := kv_operand_region hpre cta block slot feat b
  have hHi : l.addr < L.sharedBase + 131072 := by
    dsimp only [l]
    omega
  obtain ⟨hCta, hDequant | ⟨hlo, hOut⟩⟩ :=
    RawSharedWrites.tile_writer_role hpre hX hs ht hw ha rfl hHi
  change cta = ctaOf L i.1 at hCta
  · obtain ⟨d, r, s, hd, hSite⟩ := hDequant
    exact .inl (dequant_writer_coordinates hpre hX hs hw ha hCta hd hSite)
  · exact .inr ⟨by omega, hCta.symm, hOut⟩

/-- A low shared writer is either the precise dequantization store or a staging
write preceded by the softmax lane's complete sequence of QK acquires. -/
theorem actual_kv_ordinary_writer {cta block : Nat} {slot : Fin 64} {feat : Fin 512} {b : Fin 2}
    {g i : Nat} {a : Acc} {bs : List Byte} (hw : X.Writes (g, i) a bs)
    (ha : a.Covers (kvOperandLoc L cta block slot feat b)) :
    (g = GemmRing.producer L cta (dequantLane slot feat) ∧
      ∃ (d : Wg2.D) (r : Fin 4) (s : Fin 8),
        Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)) ∧
          d.site = .store r s ∧ r.val = slot.val / 16 ∧ s.val = feat.val / 64 ∧
          d.block % 2 = block % 2) ∨
    (ctaOf L g = cta ∧ EpiloguePvHistory P L X g i) := by
  let l := kvOperandLoc L cta block slot feat b
  have ⟨_, hi⟩ := kv_operand_region hpre cta block slot feat b
  have hHi : l.addr < L.sharedBase + 131072 := by
    dsimp only [l]
    omega
  have he := hw.choose_spec
  have hg := Frame.lt_of_get hX he
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨hc, _, hHistory⟩ := dismissed_stage_pv_history hpre hX hs hw ha rfl hHi hDismiss
    exact .inr ⟨hc.symm, hHistory⟩
  obtain ⟨d, _, hState, _⟩ :=
    RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by simp)
  have hRegions := RawSharedWrites.ordinary_window_regions_of_state (i := (g, i))
    hpre hX hs hState hw ha
  rcases hRegions with hGlobal | ⟨_, _, hRegions, _⟩
  · change Space.shared = Space.global at hGlobal
    cases hGlobal
  rcases hRegions with ⟨_, hc, dq, r, step, hd, hSite⟩ |
      ⟨_, _, hc, out, tile, chunk, hd, hSite⟩ | hHigh
  · exact .inl (dequant_writer_coordinates hpre hX hs hw ha hc hd hSite)
  · exact .inr ⟨hc.symm, followed_stage_pv_history hpre hX hs he hd hSite⟩
  · omega

/-- The only tensor-load writer that can cover this operand byte is the earlier Q TMA
writer. It precedes the selected ordinary dequantization write in byte causality. -/
theorem kv_tensor_writer_earlier {cta block : Nat} {slot : Fin 64} {feat : Fin 512} {b : Fin 2}
    {g j : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8} {a fp : Acc} {bs data : List Byte} {src : EvId}
    {x y k : Nat} (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hsite : d.site = .store r s) (hw : X.Writes (g, j) a bs)
    (ha : a.Covers (kvOperandLoc L cta block slot feat b))
    (htma : X.MemWrites (.async src (.write (.load x y k))) fp data)
    (ha' : fp.Covers (kvOperandLoc L cta block slot feat b)) :
    ByteCausality L X (kvOperandLoc L cta block slot feat b)
      (.async src (.write (.load x y k))) (.thread (g, j)) := by
  let l := kvOperandLoc L cta block slot feat b
  obtain ⟨_, hhi⟩ := kv_operand_region hpre cta block slot feat b
  have hTensor := htma
  obtain ⟨_, _, _, _, hi, hl, _, hz, _⟩ := hTensor
  have heq : fp.loc = l := by
    have hCover : fp.Covers l := ha'
    obtain ⟨hspace, hcta, hlo, hEnd⟩ := hCover
    change fp.loc.addr ≤ l.addr at hlo
    change l.addr < fp.loc.addr + fp.size at hEnd
    have hAddr : fp.loc.addr = l.addr := by omega
    cases hfp : fp.loc
    cases hLoc : l
    simp only [Loc.mk.injEq]
    rw [hfp, hLoc] at hspace hcta hAddr
    exact ⟨hspace.symm, hcta.symm, hAddr⟩
  rw [heq] at hl
  have hFollow := MachineTracking.actual_tensor_issue_followed hpre hX hs hi.choose_spec rfl
  obtain ⟨_, _, hQ | hRaw⟩ :=
    TensorSharedBounds.write_loc_windows_at_followed hpre hX hs hFollow hi hl
  · exact GemmRing.query_writer_ordered hpre hX hs hd hsite hw ha htma ha' hQ.1
  · have hLow := hRaw.1.1
    change L.sharedBase + 131072 ≤ (kvOperandLoc L cta block slot feat b).addr at hLow
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
