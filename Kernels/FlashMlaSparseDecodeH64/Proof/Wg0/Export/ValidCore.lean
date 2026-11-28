-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidPeer
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc

@[expose] public section

/-! # The cores of the clauses of warpgroup 0's valid trace

Each lemma `w0Core_<x>` is the step of `W0Valid` for an event at the pcs of one clause, from the
TYPING of the word the event delivers (the fields of `W0EvPayload`) and the block's pc bound
(`W0Bound`, from the data machine's state at the event); none needs `¬ HasUb` or an execution.
The clauses of the sink, the restart and the cut are in `SinkValid`, `ValidRestart`, `ValidCut`
(`w0Core_sink`, `w0Core_restart`, `w0Core_cut`). -/

/-! # The mask word keeps warpgroup 0's early words valid

The validity read at pc 289 sets the mask word of the block in progress (`w0Words_snoc_mw`), a
32-bit word, so a valid block stays valid with it (`W0Ok.with_mw`, `W0Early.snoc_mw`). -/

/-! # An accumulator load keeps the epilogue's words valid

An event at a pc of `w0OPcs` that loads 64 words that read as single-precision numbers sets the
accumulator words of the block in progress to those, and changes no other word. -/

/-! # A score load sets the high or the low half of the block's words

An event at pc 278 or 285 (the high half) or at 280 or 283 (the low half) that loads the words
`vals` replaces that half of the block's words; the trace stays valid when the new half is valid
(`W0Early.snoc_hi`, `W0Early.snoc_lo`; the block has no vote yet, `W0Now.snoc_lt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A word of a valid high half: clean and finite. -/
def W0HiWord (v : Value) : Prop := PTX.Flow.Clean v ∧ W0Fin v

/-- A word of a valid low half. -/
def W0LoWord (v : Value) : Prop := Kernels.FlashMlaSparseDecodeH64.Assumptions.scoreHalf v

variable {l : List Event} {f : Event} {vals : List Value}

theorem w0Words_snoc_half {seg : List Event} {pcs : List Nat}
    (hf : f.pc ∈ pcs) (hv : w0TcVals f = some vals) :
    w0Last w0TcVals pcs (seg ++ [f]) = some vals := by
  simp [w0Last, List.filterMap_append, hf, hv]

theorem w0Words_snoc_hi {seg : List Event} (hpc : f.pc = 278 ∨ f.pc = 285)
    (hv : w0TcVals f = some vals) : w0Words (seg ++ [f]) = { w0Words seg with hi := vals } := by
  have hlo : f.pc ∉ [280, 283] := by rcases hpc with h | h <;> simp [h]
  have hmw : f.pc ∉ [289] := by rcases hpc with h | h <;> simp [h]
  have hpm : f.pc ∉ [572] := by rcases hpc with h | h <;> simp [h]
  have hvt : f.pc ∉ [578] := by rcases hpc with h | h <;> simp [h]
  have hpw : ∀ k, k < 8 → w0Peer (seg ++ [f]) k = w0Peer seg k := fun k hk => by
    have : f.pc ≠ 477 + 5 * k := by rcases hpc with h | h <;> omega
    simp [w0Peer, List.filter_append, this]
  have hh := w0Words_snoc_half (seg := seg) (pcs := [278, 285])
    (by rcases hpc with h | h <;> simp [h]) hv
  unfold w0Words
  simp only [w0Last_snoc_quiet _ hlo, w0Last_snoc_quiet _ hmw, w0Last_snoc_quiet _ hpm,
    w0Last_snoc_quiet _ hvt, hh, Option.getD_some]
  congr 1
  funext k
  by_cases hk : k < 8
  · simp [hk, hpw k hk]
  · simp [hk]

theorem w0Words_snoc_lo {seg : List Event} (hpc : f.pc = 280 ∨ f.pc = 283)
    (hv : w0TcVals f = some vals) : w0Words (seg ++ [f]) = { w0Words seg with lo := vals } := by
  have hhi : f.pc ∉ [278, 285] := by rcases hpc with h | h <;> simp [h]
  have hmw : f.pc ∉ [289] := by rcases hpc with h | h <;> simp [h]
  have hpm : f.pc ∉ [572] := by rcases hpc with h | h <;> simp [h]
  have hvt : f.pc ∉ [578] := by rcases hpc with h | h <;> simp [h]
  have hpw : ∀ k, k < 8 → w0Peer (seg ++ [f]) k = w0Peer seg k := fun k hk => by
    have : f.pc ≠ 477 + 5 * k := by rcases hpc with h | h <;> omega
    simp [w0Peer, List.filter_append, this]
  have hh := w0Words_snoc_half (seg := seg) (pcs := [280, 283])
    (by rcases hpc with h | h <;> simp [h]) hv
  unfold w0Words
  simp only [w0Last_snoc_quiet _ hhi, w0Last_snoc_quiet _ hmw, w0Last_snoc_quiet _ hpm,
    w0Last_snoc_quiet _ hvt, hh, Option.getD_some]
  congr 1
  funext k
  by_cases hk : k < 8
  · simp [hk, hpw k hk]
  · simp [hk]

theorem W0Ok.with_hi {sc : ℝ} {w : W0Words} (h : W0Ok sc w) (hlen : vals.length = 32)
    (hv : ∀ c < 32, W0HiWord (vals.getD c (.pred false))) :
    W0Ok sc { w with hi := vals } :=
  ⟨h.scale, hlen, hv, h.loLen, h.lo, h.mask, h.peer, h.pm⟩

theorem W0Early.snoc_hi {sc : ℝ} (hsc : 0 < sc) (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc)
    (hpc : f.pc = 278 ∨ f.pc = 285) (hv : w0TcVals f = some vals) (hlen : vals.length = 32)
    (hvv : ∀ c < 32, W0HiWord (vals.getD c (.pred false))) (h : W0Early sc l) :
    W0Early sc (l ++ [f]) := by
  unfold W0Early
  rw [w0Fin_snoc_quiet hc]
  simp only [w0Words_snoc_hi hpc hv, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
    false_or]
  rcases h with h0 | ⟨w', hw', hlo, hhi, hmw, hpw, hpm⟩
  · obtain ⟨w', hw'⟩ := w0Ok_canon hsc
    obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := w0Words_nil
    rw [h0]
    exact ⟨{ w' with hi := vals }, hw'.with_hi hlen hvv, Or.inl hlo, Or.inr rfl, Or.inl hmw,
      fun k hk => Or.inl (hpw k hk), Or.inl hpm⟩
  · exact ⟨{ w' with hi := vals }, hw'.with_hi hlen hvv, hlo, Or.inr rfl, hmw, hpw, hpm⟩

theorem W0Ok.with_lo {sc : ℝ} {w : W0Words} (h : W0Ok sc w) (hlen : vals.length = 32)
    (hv : ∀ c < 32, W0LoWord (vals.getD c (.pred false))) :
    W0Ok sc { w with lo := vals } :=
  ⟨h.scale, h.hiLen, h.hi, hlen, hv, h.mask, h.peer, h.pm⟩

theorem W0Early.snoc_lo {sc : ℝ} (hsc : 0 < sc) (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc)
    (hpc : f.pc = 280 ∨ f.pc = 283) (hv : w0TcVals f = some vals) (hlen : vals.length = 32)
    (hvv : ∀ c < 32, W0LoWord (vals.getD c (.pred false))) (h : W0Early sc l) :
    W0Early sc (l ++ [f]) := by
  unfold W0Early
  rw [w0Fin_snoc_quiet hc]
  simp only [w0Words_snoc_lo hpc hv, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
    false_or]
  rcases h with h0 | ⟨w', hw', hlo, hhi, hmw, hpw, hpm⟩
  · obtain ⟨w', hw'⟩ := w0Ok_canon hsc
    obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := w0Words_nil
    rw [h0]
    exact ⟨{ w' with lo := vals }, hw'.with_lo hlen hvv, Or.inr rfl, Or.inl hhi, Or.inl hmw,
      fun k hk => Or.inl (hpw k hk), Or.inl hpm⟩
  · exact ⟨{ w' with lo := vals }, hw'.with_lo hlen hvv, Or.inr rfl, hhi, hmw, hpw, hpm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- A single-precision number reads as itself. -/
theorem rd_float_f32 (x : ℝ) : Rd (.float .f32 x) (x : EReal) :=
  ⟨clean_float x, readEReal_float x, Or.inl ⟨x, rfl⟩⟩

variable {l : List Event} {f : Event}

/-- **The accumulator words of the extended trace are valid.** -/
theorem W0EpiOk.snoc_eo {sc : ℝ} {vals : List Value} (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc)
    (hpe : f.pc ≠ 1157) (hs : f.pc ≠ 103 ∧ f.pc ≠ 156) (hop : f.pc ∈ w0OPcs)
    (hv : w0TcVals f = some vals) (hlen : vals.length = 64)
    (hO : ∃ O : Nat → ℝ, ∀ i < 64, Rd (vals.getD i (.pred false)) (O i))
    (h : W0EpiOk sc l) : W0EpiOk sc (l ++ [f]) := by
  have hpe' : f.pc ∉ [1157] := by simp [hpe]
  have hpe2 : w0EpiPe (w0Scan (l ++ [f])).2 = w0EpiPe (w0Scan l).2 := by
    rw [w0Scan_snoc_quiet hc]
    simp only [w0EpiPe, w0Last_snoc_quiet _ hpe']
  have heo : w0EpiO (w0Scan (l ++ [f])).2 = vals := by
    rw [w0Scan_snoc_quiet hc]
    simp [w0EpiO, w0Last, List.filterMap_append, hop, hv]
  obtain ⟨h1, hpe0, -, h4⟩ := h
  unfold W0EpiOk
  rw [hpe2, heo, w0Fin_snoc_quiet hc, w0SkWord_snoc_quiet hs, w0SkRaw_snoc_quiet hs]
  exact ⟨h1, hpe0, Or.inr ⟨hlen, hO⟩, h4⟩

/-- **The row-sum word of the extended trace is valid**: the peer's word the load at pc 1157
read reads as a non-negative `p`, zero while the carried maximum is `-inf`. -/
theorem W0EpiOk.snoc_pe {sc : ℝ} {x : Acc} {bs : List (Option Byte)} {v : Value} {p : ℝ}
    (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc) (hpc : f.pc = 1157) (hk : f.kind = .rd x bs)
    (hr : rebuild 3 bs = .ok v) (hp0 : 0 ≤ p) (hRd : Rd v p)
    (hz : w0MxCarry sc (w0Fin l).1 = ⊥ → p = 0) (hs : f.pc ≠ 103 ∧ f.pc ≠ 156)
    (h : W0EpiOk sc l) : W0EpiOk sc (l ++ [f]) := by
  have hpe2 : w0EpiPe (w0Scan (l ++ [f])).2 = v := by
    rw [w0Scan_snoc_quiet hc]
    simp [w0EpiPe, w0Last, List.filterMap_append, hpc, w0RdVal, hk, hr]
    rfl
  have heo : w0EpiO (w0Scan (l ++ [f])).2 = w0EpiO (w0Scan l).2 := by
    rw [w0Scan_snoc_quiet hc]
    have : f.pc ∉ w0OPcs := by simp [w0OPcs, hpc]
    simp only [w0EpiO, w0Last_snoc_quiet _ this]
  obtain ⟨h1, -, h3, h4⟩ := h
  unfold W0EpiOk
  rw [hpe2, heo, w0Fin_snoc_quiet hc, w0SkWord_snoc_quiet hs, w0SkRaw_snoc_quiet hs]
  exact ⟨h1, Or.inr ⟨p, hp0, hRd, hz⟩, h3, h4⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The words after a validity read: the mask word is the read's. -/
theorem w0Words_snoc_mw {seg : List Event} {f : Event} {v : Value} (hpc : f.pc = 289)
    (hv : w0RdVal f = some v) : w0Words (seg ++ [f]) = { w0Words seg with mw := v } := by
  have hlo : f.pc ∉ [280, 283] := by simp [hpc]
  have hhi : f.pc ∉ [278, 285] := by simp [hpc]
  have hpm : f.pc ∉ [572] := by simp [hpc]
  have hvt : f.pc ∉ [578] := by simp [hpc]
  have hpw : ∀ k, k < 8 → w0Peer (seg ++ [f]) k = w0Peer seg k := fun k hk => by
    have : f.pc ≠ 477 + 5 * k := by omega
    simp [w0Peer, List.filter_append, this]
  have hmw : w0Last w0RdVal [289] (seg ++ [f]) = some v := by
    simp [w0Last, List.filterMap_append, hpc, hv]
  unfold w0Words
  simp only [w0Last_snoc_quiet _ hlo, w0Last_snoc_quiet _ hhi, w0Last_snoc_quiet _ hpm,
    w0Last_snoc_quiet _ hvt, hmw, Option.getD_some]
  congr 1
  funext k
  by_cases hk : k < 8
  · simp [hk, hpw k hk]
  · simp [hk]

/-- A valid block keeps its validity when its mask word is replaced by a 32-bit word. -/
theorem W0Ok.with_mw {sc : ℝ} {w : W0Words} (h : W0Ok sc w) {x : BitVec 64}
    (hx : x.toNat < 2 ^ 32) :
    W0Ok sc { w with mw := .bits 32 x } :=
  ⟨h.scale, h.hiLen, h.hi, h.loLen, h.lo, ⟨x.toNat, hx, by simp⟩, h.peer, h.pm⟩

theorem W0Early.snoc_mw {sc : ℝ} {l : List Event} {f : Event} {x : BitVec 64} (hsc : 0 < sc)
    (hpc : f.pc = 289) (hv : w0RdVal f = some (.bits 32 x)) (hx : x.toNat < 2 ^ 32)
    (h : W0Early sc l) : W0Early sc (l ++ [f]) := by
  have hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc := by simp [w0ArrSPc, w0ArrLPc, hpc]
  unfold W0Early
  rw [w0Fin_snoc_quiet hc]
  simp only [w0Words_snoc_mw hpc hv, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
    false_or]
  rcases h with h0 | ⟨w', hw', hlo, hhi, hmw, hpw, hpm⟩
  · obtain ⟨w', hw'⟩ := w0Ok_canon hsc
    obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := w0Words_nil
    rw [h0]
    exact ⟨{ w' with mw := .bits 32 x }, hw'.with_mw hx, Or.inl hlo, Or.inl hhi, Or.inr rfl,
      fun k hk => Or.inl (hpw k hk), Or.inl hpm⟩
  · exact ⟨{ w' with mw := .bits 32 x }, hw'.with_mw hx, hlo, hhi, Or.inr rfl, hpw, hpm⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The events of the block in progress are at pcs up to `p` (from the data machine's state). -/
def W0Bound (l : List Event) (p : Nat) : Prop :=
  ∀ a ∈ (w0Fin l).2, 103 ≤ a.pc → a.pc ≤ p

variable {sc : ℝ} {l : List Event} {e : Event}

/-- **A score load keeps a trace valid**: the high half's 32 words (pcs 278, 285) are clean finite
numbers, the low half's (280, 283) are score halves. -/
theorem w0Core_score {vals : List Value} (hsc : 0 < sc)
    (hpc : e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285) (hv : w0TcVals e = some vals)
    (hb : W0Bound l e.pc)
    (hhi : (e.pc = 278 ∨ e.pc = 285) → vals.length = 32 ∧
      ∀ c < 32, W0HiWord (vals.getD c (.pred false)))
    (hlo : (e.pc = 280 ∨ e.pc = 283) → vals.length = 32 ∧
      ∀ c < 32, W0LoWord (vals.getD c (.pred false)))
    (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp only [w0ArrSPc, w0ArrLPc]; omega
  have hn := h.now.snoc_lt hc (by omega) hb
  have hq : W0QuietE e := ⟨by omega, by
    simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false]; omega⟩
  have hep := h.epi.snoc_nosk hc hq ⟨by omega, by omega⟩
  rcases hpc with h1 | h1 | h1 | h1
  · obtain ⟨hl, hh⟩ := hhi (Or.inl h1)
    exact h.snoc hn (h.early.snoc_hi hsc hc (Or.inl h1) hv hl hh) hep
  · obtain ⟨hl, hh⟩ := hlo (Or.inl h1)
    exact h.snoc hn (h.early.snoc_lo hsc hc (Or.inl h1) hv hl hh) hep
  · obtain ⟨hl, hh⟩ := hlo (Or.inr h1)
    exact h.snoc hn (h.early.snoc_lo hsc hc (Or.inr h1) hv hl hh) hep
  · obtain ⟨hl, hh⟩ := hhi (Or.inr h1)
    exact h.snoc hn (h.early.snoc_hi hsc hc (Or.inr h1) hv hl hh) hep

/-- **The validity read keeps a trace valid**: its word is a 32-bit word. -/
theorem w0Core_mask {x : Acc} {bs : List (Option Byte)} (hsc : 0 < sc) (hpc : e.pc = 289)
    (hk : e.kind = .rd x bs) (hb : W0Bound l e.pc)
    (hpay : ∃ n < 2 ^ 32, rebuild 3 bs = .ok (.bits 32 (BitVec.ofNat 64 n)))
    (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  obtain ⟨n, hn32, hr⟩ := hpay
  have hv : w0RdVal e = some (.bits 32 (BitVec.ofNat 64 n)) := by simp [w0RdVal, hk, hr]; rfl
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp [w0ArrSPc, w0ArrLPc, hpc]
  have hlt : (BitVec.ofNat 64 n).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn32
  exact h.snoc (h.now.snoc_lt hc (by omega) hb) (h.early.snoc_mw hsc hpc hv hlt)
    (h.epi.snoc_nosk hc ⟨by omega, by simp [w0OPcs, hpc]⟩ ⟨by omega, by omega⟩)

/-- **A peer read keeps a trace valid**: the block's pair `k0` is unchanged (the first element) or a
valid pair (the second): `hnew`. -/
theorem w0Core_peer {k0 : Nat} (hsc : 0 < sc) (hk0 : k0 < 8) (hpc : e.pc = 477 + 5 * k0)
    (hb : W0Bound l e.pc)
    (hnew : w0Peer ((w0Fin l).2 ++ [e]) k0 = w0Peer (w0Fin l).2 k0 ∨
      W0PeerOk (w0Peer ((w0Fin l).2 ++ [e]) k0))
    (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp only [w0ArrSPc, w0ArrLPc]; omega
  have hq : W0QuietE e := ⟨by omega, by
    simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false]; omega⟩
  exact h.snoc (h.now.snoc_lt hc (by omega) hb) (h.early.snoc_peer hsc hc hk0 hpc hnew)
    (h.epi.snoc_nosk hc hq ⟨by omega, by omega⟩)

/-- **The words of the block after a vote**: the vote changes only its own result. -/
theorem w0Words_snoc_vote {seg : List Event} {f : Event} (hpc : f.pc = 578) :
    (w0Words (seg ++ [f])).lo = (w0Words seg).lo ∧ (w0Words (seg ++ [f])).hi = (w0Words seg).hi ∧
      (w0Words (seg ++ [f])).mw = (w0Words seg).mw ∧
      (w0Words (seg ++ [f])).pm = (w0Words seg).pm ∧
      ∀ j, (w0Words (seg ++ [f])).pw j = (w0Words seg).pw j := by
  have hlo : f.pc ∉ [280, 283] := by simp [hpc]
  have hhi : f.pc ∉ [278, 285] := by simp [hpc]
  have hmw : f.pc ∉ [289] := by simp [hpc]
  have hpm : f.pc ∉ [572] := by simp [hpc]
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_⟩
  · simp only [w0Words, w0Last_snoc_quiet _ hlo]
  · simp only [w0Words, w0Last_snoc_quiet _ hhi]
  · simp only [w0Words, w0Last_snoc_quiet _ hmw]
  · simp only [w0Words, w0Last_snoc_quiet _ hpm]
  · simp only [w0Words]
    by_cases hj : j < 8
    · have : f.pc ≠ 477 + 5 * j := by omega
      simp [hj, w0Peer, List.filter_append, this]
    · simp [hj]

/-- The words of the block after the exchange load: the load's word is the exchange word. -/
theorem w0Words_snoc_pm {seg : List Event} {v : Value} (hpc : e.pc = 572)
    (hv : w0RdVal e = some v) :
    (w0Words (seg ++ [e])).lo = (w0Words seg).lo ∧ (w0Words (seg ++ [e])).hi = (w0Words seg).hi ∧
      (w0Words (seg ++ [e])).mw = (w0Words seg).mw ∧ (w0Words (seg ++ [e])).pm = v ∧
      ∀ j, (w0Words (seg ++ [e])).pw j = (w0Words seg).pw j := by
  have hlo : e.pc ∉ [280, 283] := by simp [hpc]
  have hhi : e.pc ∉ [278, 285] := by simp [hpc]
  have hmw : e.pc ∉ [289] := by simp [hpc]
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_⟩
  · simp only [w0Words, w0Last_snoc_quiet _ hlo]
  · simp only [w0Words, w0Last_snoc_quiet _ hhi]
  · simp only [w0Words, w0Last_snoc_quiet _ hmw]
  · simp [w0Words, w0Last, List.filterMap_append, hpc, hv]
  · simp only [w0Words]
    by_cases hj : j < 8
    · have : e.pc ≠ 477 + 5 * j := by omega
      simp [hj, w0Peer, List.filter_append, this]
    · simp [hj]

/-- A valid block keeps its validity when its exchange word is replaced by a valid word. -/
theorem w0Ok_with_pm {w : W0Words} (h : W0Ok sc w) {v : Value}
    (hv : PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf)) : W0Ok sc { w with pm := v } :=
  ⟨h.scale, h.hiLen, h.hi, h.loLen, h.lo, h.mask, h.peer, hv⟩

/-- **The exchange load keeps a trace valid**, from its word's typing: the new exchange word
differs from the default. -/
theorem w0Core_pm {x : Acc} {bs : List (Option Byte)} (hsc : 0 < sc) (hpc : e.pc = 572)
    (hk : e.kind = .rd x bs) (hb : W0Bound l e.pc)
    (hpay : ∃ v, rebuild 3 bs = .ok v ∧ PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf))
    (h : W0Valid sc l) :
    W0Valid sc (l ++ [e]) ∧ (w0Words (w0Fin (l ++ [e])).2).pm ≠ .pred false := by
  obtain ⟨v, hr, hclean, hfin⟩ := hpay
  have hrd : w0RdVal e = some v := by simp [w0RdVal, hk, hr]; rfl
  have hvok : PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf) := ⟨hclean, hfin⟩
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp [w0ArrSPc, w0ArrLPc, hpc]
  have hn := h.now.snoc_lt hc (by omega) hb
  obtain ⟨hl1, hh1, hm1, hp1, hw1⟩ := w0Words_snoc_pm (seg := (w0Fin l).2) hpc hrd
  have hea : W0Early sc (l ++ [e]) := by
    unfold W0Early
    rw [w0Fin_snoc_quiet hc]
    simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_or]
    rcases h.early with h0 | ⟨w', hw', hlo, hhi, hmw, hpw, -⟩
    · obtain ⟨w', hw'⟩ := w0Ok_canon hsc
      obtain ⟨n1, n2, n3, n4, -⟩ := w0Words_nil
      refine ⟨{ w' with pm := v }, w0Ok_with_pm hw' hvok, ?_, ?_, ?_, fun k0 hk0 => ?_, Or.inr hp1⟩
      · rw [hl1, h0]; exact Or.inl n1
      · rw [hh1, h0]; exact Or.inl n2
      · rw [hm1, h0]; exact Or.inl n3
      · rw [hw1 k0, h0]; exact Or.inl (n4 k0 hk0)
    · refine ⟨{ w' with pm := v }, w0Ok_with_pm hw' hvok, ?_, ?_, ?_, fun k0 hk0 => ?_,
        Or.inr hp1⟩
      · rw [hl1]; exact hlo
      · rw [hh1]; exact hhi
      · rw [hm1]; exact hmw
      · rw [hw1 k0]; exact hpw k0 hk0
  refine ⟨h.snoc hn hea (h.epi.snoc_nosk hc ⟨by simp [hpc], by simp [w0OPcs, hpc]⟩
    ⟨by omega, by omega⟩), ?_⟩
  rw [w0Fin_snoc_quiet hc, hp1]
  intro h0
  rw [h0] at hclean
  exact absurd hclean.1 (by simp [Value.bytes])

/-- **The vote keeps a trace valid**: every word of the block in progress that the vote needs has
been read (differs from its default). -/
theorem w0Core_vote (hpc : e.pc = 578)
    (hlo : (w0Words (w0Fin l).2).lo ≠ []) (hhi : (w0Words (w0Fin l).2).hi ≠ [])
    (hmw : (w0Words (w0Fin l).2).mw ≠ .pred false)
    (hpw : ∀ k0 < 8, (w0Words (w0Fin l).2).pw k0 ≠ (.pred false, .pred false))
    (hpm : (w0Words (w0Fin l).2).pm ≠ .pred false) (h : W0Valid sc l) :
    W0Valid sc (l ++ [e]) := by
  obtain ⟨w', hw', e_lo, e_hi, e_mw, e_pw, e_pm⟩ : ∃ w' : W0Words, W0Ok sc w' ∧
      ((w0Words (w0Fin l).2).lo = [] ∨ (w0Words (w0Fin l).2).lo = w'.lo) ∧
      ((w0Words (w0Fin l).2).hi = [] ∨ (w0Words (w0Fin l).2).hi = w'.hi) ∧
      ((w0Words (w0Fin l).2).mw = .pred false ∨ (w0Words (w0Fin l).2).mw = w'.mw) ∧
      (∀ k0 < 8, (w0Words (w0Fin l).2).pw k0 = (.pred false, .pred false) ∨
        (w0Words (w0Fin l).2).pw k0 = w'.pw k0) ∧
      ((w0Words (w0Fin l).2).pm = .pred false ∨ (w0Words (w0Fin l).2).pm = w'.pm) := by
    rcases h.early with h0 | h1
    · exfalso
      apply hlo
      rw [h0]
      exact w0Words_nil.1
    · exact h1
  have eL := e_lo.resolve_left hlo
  have eH := e_hi.resolve_left hhi
  have eM := e_mw.resolve_left hmw
  have eP : ∀ k0 < 8, (w0Words (w0Fin l).2).pw k0 = w'.pw k0 := fun k0 hk0 =>
    (e_pw k0 hk0).resolve_left (hpw k0 hk0)
  have ePm := e_pm.resolve_left hpm
  obtain ⟨hl1, hh1, hm1, hp1, hw1⟩ := w0Words_snoc_vote (seg := (w0Fin l).2) (f := e) hpc
  have hok : W0Ok sc (w0Words ((w0Fin l).2 ++ [e])) :=
    ⟨hw'.scale, by rw [hh1, eH]; exact hw'.hiLen, fun c hc => by rw [hh1, eH]; exact hw'.hi c hc,
      by rw [hl1, eL]; exact hw'.loLen, fun c hc => by rw [hl1, eL]; exact hw'.lo c hc,
      by rw [hm1, eM]; exact hw'.mask, fun j hj => by rw [hw1 j, eP j hj]; exact hw'.peer j hj,
      by rw [hp1, ePm]; exact hw'.pm⟩
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp [w0ArrSPc, w0ArrLPc, hpc]
  have hn : W0Now sc (l ++ [e]) := by
    refine ⟨?_, fun _ => ?_⟩
    · rw [w0Fin_snoc_quiet hc]
      exact h.now.1
    · rw [w0Fin_snoc_quiet hc]
      exact hok
  have hea : W0Early sc (l ++ [e]) := by
    unfold W0Early
    rw [w0Fin_snoc_quiet hc]
    simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_or]
    exact ⟨_, hok, Or.inr rfl, Or.inr rfl, Or.inr rfl, fun _ _ => Or.inr rfl, Or.inr rfl⟩
  exact h.snoc hn hea (h.epi.snoc_nosk hc ⟨by simp [hpc], by simp [hpc, w0OPcs]⟩
    ⟨by omega, by omega⟩)

/-- **An accumulator load keeps a trace valid**: it delivers 64 words that read as numbers. -/
theorem w0Core_opc {vals : List Value} (hsc : 0 < sc) (hpc : e.pc ∈ w0OPcs)
    (hv : w0TcVals e = some vals) (hpay : vals.length = 64 ∧
      ∃ O : Nat → ℝ, ∀ i < 64, Rd (vals.getD i (.pred false)) (O i))
    (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp only [w0ArrSPc, w0ArrLPc]; omega
  have hq : W0QuietW e := by
    refine ⟨hc, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩ <;> omega
  exact h.snoc (h.now.snoc_quiet hq) (h.early.snoc_quiet hsc hq)
    (h.epi.snoc_eo hc (by omega) ⟨by omega, by omega⟩ (by
      simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false]; exact hpc) hv hpay.1 hpay.2)

/-- **The row-sum load keeps a trace valid**: its word reads as a non-negative `p`, zero while the
carried maximum is `-inf`. -/
theorem w0Core_pe {x : Acc} {bs : List (Option Byte)} (hsc : 0 < sc) (hpc : e.pc = 1157)
    (hk : e.kind = .rd x bs)
    (hpay : ∃ (v : Value) (p : ℝ), rebuild 3 bs = .ok v ∧ 0 ≤ p ∧ Rd v p ∧
      (w0MxCarry sc (w0Fin l).1 = ⊥ → p = 0))
    (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  obtain ⟨v, p, hr, hp0, hRd, hz⟩ := hpay
  have hc : e.pc ≠ w0ArrSPc ∧ e.pc ≠ w0ArrLPc := by simp [w0ArrSPc, w0ArrLPc, hpc]
  have hq : W0QuietW e := by
    refine ⟨hc, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩ <;> omega
  exact h.snoc (h.now.snoc_quiet hq) (h.early.snoc_quiet hsc hq)
    (h.epi.snoc_pe hc hpc hk hr hp0 hRd hz ⟨by omega, by omega⟩)

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
