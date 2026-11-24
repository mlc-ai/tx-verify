-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2

@[expose] public section

/-! # Dequantizer memory events

The role's machine reports the addresses and bytes of its length, scale, raw and tile accesses.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
open PTX PTX.Flow PTX.Proof Numeric Thread
noncomputable section

private theorem firedAt {P : Params} {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}
    {op : Op} (hc : kernel.code[d.site.pc]? = some ⟨none, op⟩)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ t, AtD P L g d t ∧ Inv P L g d ∧
      Fires d.site.pc (eventTmpl asms L g t op) e (some u) := by
  obtain ⟨t, ht, hf⟩ := h
  change AtD P L g d t ∧ Inv P L g d at ht
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at hf
  rw [ht.1.1, hc] at hf
  exact ⟨t, ht.1, ht.2, hf⟩

/-- The abstract store site writes the packed bf16 chunk described by the recorded input. -/
theorem fired_store_event {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {d : D}
    {r : Fin 4} {s : Fin 8} {e : Event} {u : TState} (hpre : Pre P L mem0)
    (hd : d.site = .store r s) (hf : (machine P L g).Fired (some (.inr d)) e (some u)) :
    ∃ a, e.kind = .wr a (dequantChunk d.raw (byteAt d.sc (scaleIdx L g s.val))).toBytes ∧
      a.loc = ⟨.shared, ctaOf L g, L.sharedBase + tileBase d.buf + tileOff L g r.val s.val⟩ ∧
      a.size = 16 := by
  have hc := tileStore_code r s
  rw [← hd] at hc
  obtain ⟨t, ht, hi, hf⟩ := firedAt hc hf
  obtain ⟨a, he, ha, hs, -⟩ := fires_tileStore_payload hpre hd ht hi hf
  exact ⟨a, congrArg Event.kind he, ha, hs⟩

/-- A raw-read site reads eight bytes at its slot, row and chunk's position. -/
theorem fired_raw_event {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {d : D}
    {r : Fin 4} {s : Fin 8} {e : Event} {u : TState} (hpre : Pre P L mem0)
    (hd : d.site = .raw r s) (hf : (machine P L g).Fired (some (.inr d)) e (some u)) :
    ∃ a bs, e.kind = .rd a bs ∧
      a.loc = ⟨.shared, ctaOf L g, L.sharedBase + rawBase d.buf + rawWordOff L g r.val s.val⟩ ∧
      a.size = 8 := by
  have hc := rawLoad_code r s
  rw [← hd] at hc
  obtain ⟨t, ht, hi, hf⟩ := firedAt hc hf
  obtain ⟨a, bs, he, ha, hs, -⟩ := fires_raw hpre hd ht hi hf
  exact ⟨a, bs, congrArg Event.kind he, ha, hs⟩

/-- A scale-read site is one of the four elements of the row's 16-byte scale vector. -/
theorem fired_scale_event {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {d : D}
    {r j : Fin 4} {e : Event} {u : TState} (hpre : Pre P L mem0)
    (hd : d.site = .scale r j) (hf : (machine P L g).Fired (some (.inr d)) e (some u)) :
    ∃ a bs, e.kind = .rd a bs ∧
      a.loc =
        ⟨.shared, ctaOf L g, L.sharedBase + rawBase d.buf + scaleRowOff L g r.val + 4 * j.val⟩ ∧
      a.size = 4 := by
  have hc := scaleLoad_code r j
  rw [← hd] at hc
  obtain ⟨t, ht, hi, hf⟩ := firedAt hc hf
  obtain ⟨a, bs, he, ha, hs, -⟩ := fires_scale hpre hd ht hi hf
  exact ⟨a, bs, congrArg Event.kind he, ha, hs⟩

/-- The byte address computed by the runtime length instruction. -/
def runtimeLenAddr (L : Launch) (g : Nat) (orig : Bool) : Nat :=
  (Thread.paramWord L (if orig then 80 else 144) 8 + 4 * ctaidY L g) % 2 ^ 64

theorem runtimeLenAddr_main {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {ptr : Nat}
    (hpre : Pre P L mem0) (hp : P.topkLenBase = some ptr) (hb : eOf L g < P.b) :
    runtimeLenAddr L g true = ptr + 4 * eOf L g := by
  have hspan := (hpre.topkLenAddressable ptr hp).2.2
  have hptr := hpre.topkLenBaseLt ptr hp
  have hoff : ptr + 4 * eOf L g < 2 ^ 64 := by omega
  unfold runtimeLenAddr
  change (Thread.paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64 = _
  rw [Thread.paramWord_80_some hpre hp, Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hoff]

theorem runtimeLenAddr_extra {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {ptr : Nat}
    (hpre : Pre P L mem0) (hp : P.extraTopkLenBase = some ptr) (hb : eOf L g < P.b) :
    runtimeLenAddr L g false = ptr + 4 * eOf L g := by
  have hspan := (hpre.extraTopkLenAddressable ptr hp).2.2
  have hptr := hpre.extraTopkLenBaseLt ptr hp
  have hoff : ptr + 4 * eOf L g < 2 ^ 64 := by omega
  unfold runtimeLenAddr
  change (Thread.paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64 = _
  rw [Thread.paramWord_144_some hpre hp, Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hoff]

/-- A runtime length read returns four noncoherent bytes at its computed address. -/
theorem fired_length_event {P : Params} {L : Launch} {g : Nat} {d : D} {orig : Bool}
    {e : Event} {u : TState} (hd : d.site = runtimeLenSite orig)
    (hf : (machine P L g).Fired (some (.inr d)) e (some u)) :
    ∃ bs, e.kind = .nc { loc := ⟨.global, 0, runtimeLenAddr L g orig⟩, size := 4 } bs ∧
      bs.length = 4 := by
  have hc := runtimeLenLoad_code orig
  rw [← hd] at hc
  obtain ⟨t, ht, _, hf⟩ := firedAt hc hf
  have hb : t.regs (runtimeLenBase orig) = some (b64 (runtimeLenAddr L g orig)) := by
    have hmem : runtimeLenBase orig ∈ (Flow.live d.site.pc).filter tracked.contains := by
      rw [hd]
      cases orig <;> decide +kernel
    have hr := ht.reg hmem
    cases orig <;>
      simpa [runtimeLenAddr, runtimeLenBase, valueOf, table, PTX.Flow.lookupLit] using hr
  have ha : runtimeLenAddr L g orig < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hsub : t.sub = 0 := by rw [ht.2.1, hd]; cases orig <;> rfl
  have hn : asms.any (·.ncLoads t.pc) = true := by rw [ht.1, hd]; cases orig <;> decide +kernel
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := runtimeLenBase orig) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  change Fires d.site.pc
    (loadTmpl asms L g t .global true 32 [runtimeLenDest orig] (runtimeLenBase orig) 0) e (some u)
    at hf
  by_cases hal : runtimeLenAddr L g orig % 4 = 0
  · rw [loadTmpl_global_nc hsub hb ha (by decide) (by simpa using hal) hn] at hf
    obtain ⟨bs, hlen, he, -⟩ := hf
    exact ⟨bs, congrArg Event.kind he, hlen⟩
  · unfold loadTmpl at hf
    rw [effAddr_global hb ha] at hf
    simp [bind, Except.bind, elemAcc, hal, Fires, throw, throwThe, MonadExceptOf.throw] at hf

/-- The chunk bytes become the row's dequantized BF16 values once its input bytes are identified. -/
theorem chunkBytes_eq_row (L : Launch) (g s : Nat) (row : Nat → Nat) {word sc : Nat}
    (hword : ∀ i < rawBytesPerThread, byteAt word i = row (elemByte L g s i))
    (hscale : byteAt sc (scaleIdx L g s) = row (512 + scaleIdx L g s)) :
    (dequantChunk word (byteAt sc (scaleIdx L g s))).toBytes =
      (List.range rawBytesPerThread).flatMap fun i =>
        (Value.float .bf16 (dequant row (logicalElem L g s i))).toBytes := by
  rw [dequantChunk_toBytes]
  change (List.range rawBytesPerThread).flatMap _ = _
  apply List.flatMap_congr
  intro i hi
  rw [hword i (List.mem_range.mp hi), hscale, dequant_chunk row L g s i (List.mem_range.mp hi)]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
