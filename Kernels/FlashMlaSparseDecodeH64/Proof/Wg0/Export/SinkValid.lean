-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceSk
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.LseSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # The sink load of warpgroup 0 reads the head's float word

The `.nc` read at pc 156 returns the four bytes of the head's word of the sink array: the bits of
a finite `f32` (`Pre.paramSink`), read as `rebuild 3 bs = b32 bits`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The sink load's word** (pc 156): the bits of a finite `f32`, the bytes it read. -/
theorem wg0_sink_word_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} (hal : LaneUbFree X g k) {e : Event}
    (he : X.get (g, k) = some e)
    (hat : Wg0At L g e.pc) (hpc : e.pc = 156) {a : Acc} {bs : List (Option Byte)}
    (hk : e.kind = .nc a bs) :
    ∃ (bits : Nat) (q : ℚ), bits < 2 ^ 32 ∧ f32Value bits = some q ∧
      rebuild 3 bs = .ok (b32 bits) := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hg := Frame.lt_of_get hX he
  have hkl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, hE, hw⟩ := wg0_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  obtain ⟨t, ins, o, hat', hinv, hc', hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  have hs3 : d.site = .sink ∨ d.site = .lenA ∨ d.site = .lenB := by
    have hK := hE.2
    unfold Wg0.EvK at hK
    revert hK
    generalize d.site = s
    intro hK
    cases s <;> simp [Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv, RdAt, WrAt,
      GenWrAt, GWrAt, hk] at hK ⊢
  have hs : d.site = .sink := by
    rcases hs3 with h | h | h
    · exact h
    all_goals
      exfalso
      have h2 : e.pc = Wg0.Site.pc d.site := hpcσ
      rw [h] at h2
      simp [Wg0.Site.pc] at h2
      omega
  rcases wg0_pred_pre hFw hal hw hg hkl.le hσ with ⟨-, -, d', -, e', -, -, hS⟩ | h
  · obtain ⟨-, hptr, -⟩ := Wg0.sink_pred hS hs
    obtain ⟨x, hx⟩ := len_ptr hptr
    obtain ⟨bs', hr⟩ := Wg0.sink_read hp hx hs hat' hinv hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    have hm := hp.paramSink
    rw [hx] at hm
    obtain ⟨-, -, hmem⟩ := hm
    obtain ⟨s, bits, -, hlt, hb, hq⟩ := hmem (tidOf L g % 64) (Nat.mod_lt _ (by norm_num))
    obtain ⟨q, hq', -⟩ := Option.map_eq_some_iff.mp hq
    exact ⟨bits, q, hlt, hq', rebuild_word hX he hr fun j hj => by
      simpa [Nat.add_assoc] using hb j hj⟩
  · rw [hs] at h; cases h

/-- The raw sink word, the bits of a finite `f32`, reads as a number. -/
theorem sink_raw_rd {bits : Nat} {q : ℚ} (hb : bits < 2 ^ 32) (hq : f32Value bits = some q) :
    Rd (b32 bits) ((q : ℝ) : EReal) := by
  refine ⟨⟨rfl, (fun _ _ _ h => by cases h), fun w x h => ?_⟩,
    readEReal_bits32 bits q rfl (by omega) hq, Or.inl ⟨_, rfl⟩⟩
  simp only [b32, Value.bits.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bits < 2 ^ 64 by omega)]
  exact hb

/-- The scaled sink word of a sink load of the bits of a finite `f32`. -/
theorem w0SkOf_rd {bits : Nat} {q : ℚ} (hb : bits < 2 ^ 32) (hq : f32Value bits = some q)
    {bs : List (Option Byte)} (hr : rebuild 3 bs = .ok (b32 bits)) :
    ∃ sk, Rd (okVal (.bits 32 0) (fF (mulL true) [.reg 932, .f32imm 1069066811]
      [(rebuild 3 bs).toOption.getD (.pred false)])) sk := by
  have hf : fF (mulL true) [.reg 932, .f32imm 1069066811] [b32 bits] =
      mulE true (b32 bits) (.bits 32 (BitVec.ofNat 64 1069066811)) := by
    simp [fF, regsOf, regOf, fOpnd, lk, mulL]
  have hc : f32Value 1069066811 = some (12102203 / 8388608 : ℚ) := by decide +kernel
  have hx := rd_read (sink_raw_rd hb hq)
  have hy := readEReal_bits32 1069066811 _ rfl (by norm_num) hc
  have hm := mulE_reads (fz := true) hx hy (mulEReal_coe _ _)
  rw [hr]
  simp only [Except.toOption, Option.getD_some]
  rw [hf, hm, erealValue_coe]
  exact ⟨_, ⟨clean_float _, readEReal_float _, Or.inl ⟨_, rfl⟩⟩⟩

/-- **The core of the sink clause**: the sink events keep a trace valid (pc 103: `-inf`; pc 156:
the scaled word of the sink input), given the typing of the sink load's word (`hpay`). -/
theorem w0Core_sink {sc : ℝ} (hsc : 0 < sc) {l : List Event} {e : Event}
    (hpc : e.pc = 103 ∨ e.pc = 156)
    (hpay : e.pc = 156 → ∀ (a : Acc) (bs : List (Option Byte)), e.kind = .nc a bs →
      ∃ (bits : Nat) (q : ℚ), bits < 2 ^ 32 ∧ f32Value bits = some q ∧
        rebuild 3 bs = .ok (b32 bits))
    (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  have hw : W0QuietW e := by
    rcases hpc with h | h <;> exact ⟨by simp [w0ArrSPc, w0ArrLPc, h], by simp [h], by simp [h],
      by simp [h], by simp [h], by simp [h], fun k _ => by omega⟩
  have hq : W0QuietE e := by
    rcases hpc with h | h <;> exact ⟨by simp [h], by simp [w0OPcs, h]⟩
  rcases hpc with h103 | h156
  · refine h.snoc_sk hsc hw hq (Or.inl ?_) fun v hv => ?_
    · simp [Wg0.Data.w0SkWord_snoc, w0SkOf, h103, w0NegInf]
    · have : w0SkRaw (l ++ [e]) = w0SkRaw l := by
        simp [w0SkRaw, List.filterMap_append, w0SkRawOf, h103]
      rw [this] at hv
      obtain ⟨-, -, -, hr⟩ := h.epi
      exact hr v hv
  · by_cases hn : ∃ a bs, e.kind = .nc a bs
    · obtain ⟨a, bs, hk⟩ := hn
      obtain ⟨bits, q, hb, hq', hr⟩ := hpay h156 a bs hk
      refine h.snoc_sk hsc hw hq (Or.inr ?_) fun v hv => ?_
      · simp only [Wg0.Data.w0SkWord_snoc, w0SkOf, h156, hk]
        simpa using w0SkOf_rd hb hq' hr
      · simp only [w0SkRaw, List.filterMap_append, w0SkRawOf, h156, hk, ↓reduceIte,
          List.filterMap_cons, List.filterMap_nil, List.getLast?_append] at hv
        simp only [List.getLast?_singleton, Option.some_or, Option.some.injEq] at hv
        subst hv
        rw [hr]
        exact ⟨_, sink_raw_rd hb hq'⟩
    · have h1 : w0SkOf e = none := by
        unfold w0SkOf
        simp only [h156, ↓reduceIte, show (156 : Nat) ≠ 103 by omega]
        split
        · exact absurd ⟨_, _, ‹e.kind = _›⟩ hn
        · rfl
      have h2 : w0SkRawOf e = none := by
        unfold w0SkRawOf
        simp only [h156, ↓reduceIte]
        split
        · exact absurd ⟨_, _, ‹e.kind = _›⟩ hn
        · rfl
      refine h.snoc_sk hsc hw hq ?_ fun v hv => ?_
      · rw [Wg0.Data.w0SkWord_snoc, h1, Option.getD_none]
        exact h.epi.1
      · have : w0SkRaw (l ++ [e]) = w0SkRaw l := by
          simp [w0SkRaw, List.filterMap_append, h2]
        rw [this] at hv
        obtain ⟨-, -, -, hr⟩ := h.epi
        exact hr v hv

/-- **The sink events keep a trace valid** (pc 103: `-inf`; pc 156: the scaled word of the
sink input), from the lane's events before `k` being no undefined behaviour. -/
theorem w0Valid_snoc_sink_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} (hal : LaneUbFree X g k) {e : Event}
    (he : X.get (g, k) = some e)
    (hat : Wg0At L g e.pc) (hpc : e.pc = 103 ∨ e.pc = 156)
    (h : W0Valid P.scale ((X.tr g).take k)) : W0Valid P.scale ((X.tr g).take (k + 1)) := by
  rw [trace_take_succ he]
  exact w0Core_sink hp.scalePos hpc
    (fun h156 _ _ hk => wg0_sink_word_pre hp hX hFw hal he hat h156 hk) h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
