-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingStoreExtent
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Audit.PeerScores
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Flow.NotClc
import Lemmas.Flow.WriteSpace

@[expose] public section

/-! # Concrete softmax writes stay outside the coordinate ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def softmaxStoreSites : List Nat := [566, 1155, 1178] ++
  (List.finRange 8).map (Wg0.Site.exchStore · |>.pc) ++
  (List.finRange 4).map (Wg0.Site.pStore · |>.pc) ++
  (List.finRange 4).flatMap (fun j => (List.finRange 8).map (Wg0.Site.oStage j · |>.pc))

set_option maxRecDepth 100000 in
private theorem softmax_store_sites : kernel.code.zipIdx.all (fun (ins, pc) =>
    !decide (softmaxWriteRegion pc) || !writeOp ins.op ||
      softmaxStoreSites.contains pc) = true := by
  decide +kernel

private theorem softmax_store_in_body {pc : Nat} (h : pc ∈ softmaxStoreSites) :
    253 ≤ pc ∧ pc < 1842 := by
  have hAudit : softmaxStoreSites.all (fun i => decide (253 ≤ i ∧ i < 1842)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hAudit pc h)

section
variable {t : TState} {pc : Nat} {a : Acc} {bytes : List Byte}

private theorem exchange_extent {ins : Instr} {o : Option TState} (hpre : Pre P L mem0) (j : Fin 8)
    (hWarp : warpOf L g < 4) (hCode : kernel.code[(Wg0.Site.exchStore j).pc]? = some ins)
    (hBase : t.regs (988 + j.val) = some (sb L
      (Wg0.exchangeBase + Wg0.exchangeQuad * (warpOf L g ^^^ 2) + 16 * laneOf L g +
        Wg0.exchangeChunk * j.val)))
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc, .wr a bytes⟩ o) :
    a.loc.space = .shared ∧
      L.sharedBase + 204800 ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + 221696 ∧
      a.size = 16 ∧ a.loc = Wg0.shLoc L g (Wg0.exchangeBase +
        Wg0.exchangeQuad * (warpOf L g ^^^ 2) + 16 * laneOf L g + Wg0.exchangeChunk * j.val) := by
  obtain rfl := Option.some.inj (hCode.symm.trans (Audit.peerPack_stores j).2)
  let base := L.sharedBase + (Wg0.exchangeBase + Wg0.exchangeQuad * (warpOf L g ^^^ 2) +
    16 * laneOf L g + Wg0.exchangeChunk * j.val)
  have hShared := sharedBase_lt hpre
  have hLane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hXor : warpOf L g ^^^ 2 < 4 := by interval_cases h : warpOf L g <;> decide
  have hj := j.isLt
  have hBound : base + 16 ≤ L.sharedBase + 221696 := by
    unfold base Wg0.exchangeBase Wg0.exchangeQuad Wg0.exchangeChunk
    omega
  have hAddr := effAddr_b32 (L := L) (g := g) hBase (by omega : base < 2 ^ 32)
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := 988 + j.val) (w := 32)
    rfl rfl rfl rfl (by simp)] at hf
  obtain ⟨hSpace, hStart, hEnd⟩ := direct_store_extent hAddr hf
  have hLower : L.sharedBase + 204800 ≤ base := by unfold base Wg0.exchangeBase; omega
  simp only [DType.width, Nat.reduceDiv, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.mul_one] at hEnd
  obtain ⟨hSub, hLoc, hSize⟩ := direct_store_element hAddr hf
  have hZero : t.sub = 0 := by
    change t.sub < 1 at hSub
    omega
  refine ⟨hSpace, hLower.trans hStart, hEnd.trans hBound, ?_, ?_⟩
  · simpa only [DType.width, Nat.reduceDiv] using hSize
  · rw [hLoc, hZero]
    rfl

private theorem probability_extent {ins : Instr} {o : Option TState} (hpre : Pre P L mem0)
    (j : Fin 4) (hWarp : warpOf L g < 4) (hCode : kernel.code[(Wg0.Site.pStore j).pc]? = some ins)
    (hBase : t.regs 474 = some
      (sb L (4096 * Wg0.half L g + 512 * (warpOf L g % 2) + 16 * laneOf L g)))
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc, .wr a bytes⟩ o) :
    a.loc.space = .shared ∧
      L.sharedBase + 204800 ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + 221184 ∧
      a.loc.cta = ctaOf L g := by
  obtain rfl := Option.some.inj (hCode.symm.trans (Wg0.pStore_code j))
  let base := L.sharedBase + (4096 * Wg0.half L g + 512 * (warpOf L g % 2) + 16 * laneOf L g)
  let off := Wg0.pTileBase + Wg0.pChunkStride * j.val
  have hShared := sharedBase_lt hpre
  have hLane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hHalf := Wg0.halfLt hWarp
  have hj := j.isLt
  have hBound : base + off + 16 ≤ L.sharedBase + 221184 := by
    unfold base off Wg0.pTileBase Wg0.pChunkStride
    omega
  have hAddr := effAddr_b32_off (L := L) (g := g) (off := off) hBase
    (by omega : base + off < 2 ^ 32)
  have hrule : (Wg0.pStoreInstr j).rule = some .threadAccess := by fin_cases j <;> rfl
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := 474) (w := 32)
    hrule rfl rfl rfl rfl] at hf
  obtain ⟨hSpace, hStart, hEnd⟩ := direct_store_extent hAddr hf
  have hLower : L.sharedBase + 204800 ≤ base + off := by unfold base off Wg0.pTileBase; omega
  simp only [Wg0.pStoreInstr, Wg0.pStoreSrcs, List.length_map, List.length_range,
    DType.width, Nat.reduceDiv, Nat.reduceMul] at hEnd
  have hLoc := (direct_store_element hAddr hf).2.1
  exact ⟨hSpace, hLower.trans hStart, hEnd.trans hBound, congrArg Loc.cta hLoc⟩

private theorem row_extent {o : Option TState} {src : Opnd} (hpre : Pre P L mem0)
    (hBase : t.regs 471 = some (sb L (4 * (tidOf L g % 128))))
    (hf : Fires pc (storeTmpl L g t .shared 32 471 221184 [src]) ⟨pc, .wr a bytes⟩ o) :
    a.loc.space = .shared ∧
      L.sharedBase + 221184 ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + 221696 ∧
      a.size = 4 ∧ a.loc = Wg0.shLoc L g (Wg0.rowMaxBase + 4 * (tidOf L g % 128)) := by
  have hShared := sharedBase_lt hpre
  let base := L.sharedBase + 4 * (tidOf L g % 128)
  have hAddr := effAddr_b32_off (L := L) (g := g) (off := 221184) hBase
    (by unfold base; omega : base + 221184 < 2 ^ 32)
  obtain ⟨hSpace, hStart, h⟩ := direct_store_extent hAddr hf
  change base + 221184 ≤ a.loc.addr at hStart
  change a.loc.addr + a.size ≤ base + 221184 + 4 at h
  unfold base at h hStart
  obtain ⟨hSub, hLoc, hSize⟩ := direct_store_element hAddr hf
  have hZero : t.sub = 0 := by
    change t.sub < 1 at hSub
    omega
  refine ⟨hSpace, by omega, by omega, hSize, ?_⟩
  rw [hLoc, hZero]
  simp only [Loc.at, Nat.mul_zero, Nat.add_zero, Wg0.shLoc, Wg0.rowMaxBase]
  congr 1
  omega

private theorem stage_extent {ins : Instr} {o : Option TState} (hpre : Pre P L mem0)
    (hg : g < L.threads) (j : Fin 4) (k : Fin 8) (hWarp : warpOf L g < 4)
    (hCode : kernel.code[(Wg0.Site.oStage j k).pc]? = some ins)
    (hBase : t.regs (2992 + k.val) = some (Wg0.stageWord L g k.val))
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) ⟨pc, .wr a bytes⟩ o) :
    a.loc.space = .shared ∧ a.loc.cta = ctaOf L g ∧ L.sharedBase + 65536 ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + 131072 := by
  obtain rfl := Option.some.inj (hCode.symm.trans (Wg0.stage_code j k))
  have hAddr := Wg0.stage_write_addr (j := j) hpre hg hWarp hBase
  have hTemplate : eventTmpl Assumptions.all L g t (.mem (Wg0.stageAccess j k)) =
      accessTmpl Assumptions.all L g t (Wg0.stageAccess j k) := by
    fin_cases j <;> fin_cases k <;> rfl
  rw [hTemplate] at hf
  obtain ⟨hSpace, hCta, hStart, h⟩ :=
    generic_store_extent rfl rfl (by simp [Wg0.stageAccess]) hAddr hf
  have hHalf := Wg0.halfLt hWarp
  have hHead := Wg0.head_lt L g
  have hPlane := (by decide : ∀ j : Fin 4, Wg0.planeAdd j.val ≤ 5) j
  have hXor := Wg0.xor_lt_eight k.isLt (Nat.mod_lt (tidOf L g % 64) (by decide))
  simp only [Wg0.shLoc, Wg0.stageAccess, DType.width, Nat.reduceDiv, Nat.reduceMul] at h hStart
  simp only [Wg0.stageWrite, Wg0.stageBase, Wg0.groupOff, Wg0.stageTileBytes] at h hStart
  exact ⟨hSpace, hCta, by omega, by omega⟩
end

/-- Concrete high shared writes carry the footprints of the exchange or probability store,
or lie in the row-maximum and half-sum array. -/
def SoftmaxHighWrite (L : Launch) (g tag : Nat) (a : Acc) : Prop :=
  (∃ j : Fin 8, tag = (Wg0.Site.exchStore j).pc ∧ a.size = 16 ∧
    a.loc = Wg0.shLoc L g (Wg0.exchangeBase + Wg0.exchangeQuad * (warpOf L g ^^^ 2) +
      16 * laneOf L g + Wg0.exchangeChunk * j.val)) ∨
  (∃ j : Fin 4, tag = (Wg0.Site.pStore j).pc ∧ a.loc.cta = ctaOf L g ∧
    a.loc.addr + a.size ≤ L.sharedBase + 221184) ∨
  (tag = Wg0.Site.rowMax.pc ∨ tag = Wg0.Site.lseStore0.pc) ∧
    a.size = 4 ∧ a.loc = Wg0.shLoc L g (Wg0.rowMaxBase + 4 * (tidOf L g % 128))

variable {start i : Nat} {d : Wg0.D} {a : Acc} {bytes : List Byte} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hWg : wgOf L g = 0)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)))
    (hMask : d.site = .maskReady)
include hpre hX hs hWg hState hMask

/-- A write after the first mask acquire is global, in output staging, or in the
exchange, probability or reduction region above the raw buffers. -/
theorem softmax_actual_write_extent (hi : start ≤ i) (hw : X.Writes (g, i) a bytes) :
    (a.loc.space = .global ∧ X.get (g, i) = some ⟨1178, .wr a bytes⟩) ∨
      (a.loc.space = .shared ∧ L.sharedBase + 65536 ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ L.sharedBase + 131072 ∧ a.loc.cta = ctaOf L g ∧
        ∃ tag > 1184, X.get (g, i) = some ⟨tag, .wr a bytes⟩) ∨
      (a.loc.space = .shared ∧ L.sharedBase + 204800 ≤ a.loc.addr ∧
        a.loc.addr + a.size ≤ L.sharedBase + 221696 ∧
        ∃ tag, X.get (g, i) = some ⟨tag, .wr a bytes⟩ ∧ SoftmaxHighWrite L g tag a) := by
  obtain ⟨tag, he⟩ := hw
  have hg := Frame.lt_of_get hX he
  have hWarp : warpOf L g < 4 := by unfold wgOf warpOf at *; omega
  obtain ⟨t, q, hStep, hRegion, hRegs⟩ := softmax_write_regs_at_event hX hs hMask hState he hi
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have h := fires_none_ends hf
    simp [Ends] at h
  | some u =>
    obtain ⟨ins, hc, _, hf⟩ := PTX.EventFrame.estep_event_source hStep
    have hk := List.all_eq_true.mp softmax_store_sites (ins, t.pc)
      (List.mem_zipIdx_iff_getElem?.mpr hc)
    have hSite : t.pc ∈ softmaxStoreSites := by
      simpa [hRegion, fires_write_op hf rfl] using hk
    have hBody := softmax_store_in_body hSite
    have hKeep := hRegs hBody.1 hBody.2
    have hp : tag = t.pc := PTX.EventFrame.estep_source_pc hStep
    rw [← hp] at hf
    change t.pc ∈ [566, 1155, 1178] ++
      (List.finRange 8).map (Wg0.Site.exchStore · |>.pc) ++
      (List.finRange 4).map (Wg0.Site.pStore · |>.pc) ++
      (List.finRange 4).flatMap (fun j => (List.finRange 8).map (Wg0.Site.oStage j · |>.pc))
      at hSite
    simp only [List.append_assoc] at hSite
    rcases List.mem_append.mp hSite with hRow | hOther
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hRow
      have hBase : t.regs 471 = some (sb L (4 * (tidOf L g % 128))) :=
        hKeep 471 (by decide)
      rcases hRow with h | h | h
      · rw [h, Flow.code_566] at hc
        obtain rfl := Option.some.inj hc
        rw [eventTmpl, memTmpl_store (sp := .shared) (base := 471) (w := 32)
          rfl rfl rfl rfl (by simp)] at hf
        obtain ⟨hSpace, hLo, hHi, hSize, hLoc⟩ := row_extent hpre hBase hf
        exact .inr (.inr ⟨hSpace, by omega, hHi, tag, he,
          .inr (.inr ⟨.inl (hp.trans h), hSize, hLoc⟩)⟩)
      · rw [h, Flow.code_1155] at hc
        obtain rfl := Option.some.inj hc
        rw [eventTmpl, memTmpl_store (sp := .shared) (base := 471) (w := 32)
          rfl rfl rfl rfl (by simp)] at hf
        obtain ⟨hSpace, hLo, hHi, hSize, hLoc⟩ := row_extent hpre hBase hf
        exact .inr (.inr ⟨hSpace, by omega, hHi, tag, he,
          .inr (.inr ⟨.inr (hp.trans h), hSize, hLoc⟩)⟩)
      · rw [h, Flow.code_1178] at hc
        obtain rfl := Option.some.inj hc
        rcases fires_write_space hf rfl with hSp | hDyn
        · exact .inl ⟨(Option.some.inj hSp).symm, by simpa only [hp, h] using he⟩
        · cases hDyn
    · rcases List.mem_append.mp hOther with hExchange | hOther
      · obtain ⟨r, _, hr⟩ := List.mem_map.mp hExchange
        have hReg : 988 + r.val ∈ softmaxWriteRegs := by
          simp only [softmaxWriteRegs, List.mem_append]
          exact .inl (.inr (List.mem_map.mpr ⟨r.val, List.mem_range.mpr r.isLt, rfl⟩))
        have hBase := hKeep (988 + r.val) hReg
        rw [← hr] at hc
        obtain ⟨hSpace, hLo, hHi, hSize, hLoc⟩ :=
          exchange_extent hpre r hWarp hc (by fin_cases r <;> exact hBase) hf
        exact .inr (.inr ⟨hSpace, hLo, hHi, tag, he, .inl ⟨r, hp.trans hr.symm, hSize, hLoc⟩⟩)
      · rcases List.mem_append.mp hOther with hProbability | hStage
        · obtain ⟨r, _, hr⟩ := List.mem_map.mp hProbability
          rw [← hr] at hc
          obtain ⟨hSpace, hLo, hHi, hCta⟩ :=
            probability_extent hpre r hWarp hc (hKeep 474 (by decide)) hf
          exact .inr (.inr ⟨hSpace, hLo, by omega, tag, he,
            .inr (.inl ⟨r, hp.trans hr.symm, hCta, hHi⟩)⟩)
        · obtain ⟨j, _, hMap⟩ := List.mem_flatMap.mp hStage
          obtain ⟨k, _, hk⟩ := List.mem_map.mp hMap
          have hReg : 2992 + k.val ∈ softmaxWriteRegs := by
            simp only [softmaxWriteRegs, List.mem_append]
            exact .inr (List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩)
          have hBase := hKeep (2992 + k.val) hReg
          rw [← hk] at hc
          obtain ⟨hSpace, hCta, hLo, hHi⟩ :=
            stage_extent hpre hg j k hWarp hc (by fin_cases k <;> exact hBase) hf
          have hTag : 1184 < tag := by
            rw [hp, ← hk]
            fin_cases j <;> fin_cases k <;> decide
          exact .inr (.inl ⟨hSpace, hLo, hHi, hCta, tag, hTag, he⟩)

theorem softmax_write_extent (hi : start ≤ i) (hw : X.Writes (g, i) a bytes) :
    a.loc.space = .global ∨ a.loc.addr + a.size ≤ L.sharedBase + 131072 ∨
      (L.sharedBase + 204800 ≤ a.loc.addr ∧ a.loc.addr + a.size ≤ L.sharedBase + 221696) := by
  rcases softmax_actual_write_extent hpre hX hs hWg hState hMask hi hw with
    ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, hLo, hHi, _⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨hLo, hHi⟩)

/-- Every concrete softmax write after the first mask acquire misses the coordinates. -/
theorem softmax_write_outside_coordinates (hi : start ≤ i) (hw : X.Writes (g, i) a bytes) :
    a.loc.space = .global ∨ a.loc.addr + a.size ≤ L.sharedBase + 221696 := by
  rcases softmax_write_extent hpre hX hs hWg hState hMask hi hw with h | h | ⟨_, h⟩
  · exact .inl h
  · exact .inr (h.trans (by omega))
  · exact .inr h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
