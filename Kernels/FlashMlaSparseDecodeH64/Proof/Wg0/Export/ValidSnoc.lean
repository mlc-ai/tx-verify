-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # An event that reads no word keeps a lane's trace valid

`W0Valid.snoc_quiet`: appending an event whose pc is none of the pcs that the words of a block
(`w0Words`), the block cut (`w0Fin`) or the epilogue's words read changes none of them, so the
trace stays valid. `W0Valid.snoc` is the general step: the three clauses of the extended trace
(`W0Now`, `W0Early`, `W0EpiOk`) and the validity of the trace give the validity of the extended
trace. A canonical block of valid words (`w0Ok_canon`) shows a block in progress that has read
nothing is early-valid. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- An event at none of the pcs a block's words and the block cut read. -/
structure W0QuietW (f : Event) : Prop where
  cut : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc
  lo : f.pc ≠ 280 ∧ f.pc ≠ 283
  hi : f.pc ≠ 278 ∧ f.pc ≠ 285
  mw : f.pc ≠ 289
  pm : f.pc ≠ 572
  vt : f.pc ≠ 578
  pw : ∀ k, k < 8 → f.pc ≠ 477 + 5 * k

/-- An event at none of the pcs the epilogue's peer sum and accumulator words read. -/
structure W0QuietE (f : Event) : Prop where
  pe : f.pc ≠ 1157
  eo : f.pc ∉ w0OPcs

/-- An event at none of the pcs the words, the block cut and the epilogue read. -/
structure W0Quiet (f : Event) : Prop extends W0QuietW f, W0QuietE f where
  sk : f.pc ≠ 103 ∧ f.pc ≠ 156

/-- **A block of valid words** (for a positive scale). -/
theorem w0Ok_canon {sc : ℝ} (hsc : 0 < sc) : ∃ w : W0Words, W0Ok sc w := by
  have hc : PTX.Flow.Clean (.float .f32 0) := ⟨by simp [Value.bytes, FloatFmt.bytes],
    fun _ _ _ => by simp, fun _ _ h => by cases h⟩
  have hf : W0Fin (.float .f32 0) := ⟨0, by simp [valFloat]; rfl⟩
  have hget' : ∀ n c : Nat, c < n → (List.replicate n (Value.float .f32 0)).getD c (.pred false) =
      .float .f32 0 := by
    intro n c hc'
    simp [List.getD_eq_getElem?_getD, hc']
  have hget : ∀ c < 32, (List.replicate 32 (Value.float .f32 0)).getD c (.pred false) =
      .float .f32 0 := hget' 32
  refine ⟨⟨List.replicate 32 (.float .f32 0), List.replicate 32 (.float .f32 0),
    .bits 32 (BitVec.ofNat 64 0), fun _ => (.pair (.float .f32 0) (.float .f32 0),
      .pair (.float .f32 0) (.float .f32 0)), .float .f32 0, false⟩, hsc, by simp, ?_, by simp, ?_,
    ⟨0, by norm_num, rfl⟩, ?_, ⟨hc, Or.inl hf⟩⟩
  · intro c hc'
    simp only [hget c hc']
    exact ⟨hc, hf⟩
  · intro c hc'
    simp only [hget c hc']
    trivial
  · intro k hk
    simp only [W0PeerOk, splitValue]
    exact ⟨hf, hf, hf, hf⟩

theorem w0Words_nil : (w0Words []).lo = [] ∧ (w0Words []).hi = [] ∧
    (w0Words []).mw = .pred false ∧ (∀ k < 8, (w0Words []).pw k = (.pred false, .pred false)) ∧
    (w0Words []).pm = .pred false := by
  refine ⟨by simp [w0Words, w0Last], by simp [w0Words, w0Last], by simp [w0Words, w0Last],
    fun k hk => ?_, by simp [w0Words, w0Last]⟩
  simp [w0Words, w0Peer, lastN]


variable {l : List Event} {f : Event}

theorem w0Fin_snoc_quiet (hf : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc) :
    w0Fin (l ++ [f]) = ((w0Fin l).1, (w0Fin l).2 ++ [f]) := by
  rw [w0Fin_snoc]
  simp [hf.1, hf.2]

theorem w0Scan_snoc_quiet (hf : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc) :
    w0Scan (l ++ [f]) = ((w0Scan l).1, (w0Scan l).2 ++ [f]) := by
  rw [w0Scan_snoc]
  simp [hf.1]

theorem w0Last_snoc_quiet {α : Type} (g : Event → Option α) {pcs : List Nat} {seg : List Event}
    (h : f.pc ∉ pcs) : w0Last g pcs (seg ++ [f]) = w0Last g pcs seg := by
  simp [w0Last, List.filterMap_append, h]

theorem w0Words_snoc_quiet {seg : List Event} (hf : W0QuietW f) :
    w0Words (seg ++ [f]) = w0Words seg := by
  have hpw : ∀ k, k < 8 → w0Peer (seg ++ [f]) k = w0Peer seg k := fun k hk => by
    have := hf.pw k hk
    simp [w0Peer, List.filter_append, this]
  have hlo : f.pc ∉ [280, 283] := by simp [hf.lo.1, hf.lo.2]
  have hhi : f.pc ∉ [278, 285] := by simp [hf.hi.1, hf.hi.2]
  have hmw : f.pc ∉ [289] := by simp [hf.mw]
  have hpm : f.pc ∉ [572] := by simp [hf.pm]
  have hvt : f.pc ∉ [578] := by simp [hf.vt]
  unfold w0Words
  simp only [w0Last_snoc_quiet _ hlo, w0Last_snoc_quiet _ hhi, w0Last_snoc_quiet _ hmw,
    w0Last_snoc_quiet _ hpm, w0Last_snoc_quiet _ hvt]
  congr 1
  funext k
  by_cases hk : k < 8
  · simp [hk, hpw k hk]
  · simp [hk]

theorem w0SkWord_snoc_quiet (hf : f.pc ≠ 103 ∧ f.pc ≠ 156) : w0SkWord (l ++ [f]) = w0SkWord l := by
  have : w0SkOf f = none := by simp [w0SkOf, hf.1, hf.2]
  simp [w0SkWord, List.filterMap_append, this]

theorem w0SkRaw_snoc_quiet (hf : f.pc ≠ 103 ∧ f.pc ≠ 156) : w0SkRaw (l ++ [f]) = w0SkRaw l := by
  have : w0SkRawOf f = none := by simp [w0SkRawOf, hf.2]
  simp [w0SkRaw, List.filterMap_append, this]

theorem W0Now.snoc_quiet {sc : ℝ} (hf : W0QuietW f) (h : W0Now sc l) : W0Now sc (l ++ [f]) := by
  refine ⟨?_, fun hv => ?_⟩
  · rw [w0Fin_snoc_quiet hf.cut]
    exact h.1
  · rw [w0Fin_snoc_quiet hf.cut] at hv ⊢
    obtain ⟨e, he, hpc⟩ := hv
    rw [w0Words_snoc_quiet hf]
    refine h.2 ⟨e, ?_, hpc⟩
    rcases List.mem_append.mp he with h1 | h1
    · exact h1
    · simp only [List.mem_singleton] at h1
      subst h1
      exact absurd hpc hf.vt

theorem W0Early.snoc_quiet {sc : ℝ} (hsc : 0 < sc) (hf : W0QuietW f) (h : W0Early sc l) :
    W0Early sc (l ++ [f]) := by
  unfold W0Early
  rw [w0Fin_snoc_quiet hf.cut]
  simp only [w0Words_snoc_quiet hf, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
    false_or]
  rcases h with h0 | ⟨w', hw', hr⟩
  · obtain ⟨w', hw'⟩ := w0Ok_canon hsc
    obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := w0Words_nil
    rw [h0]
    exact ⟨w', hw', Or.inl hlo, Or.inl hhi, Or.inl hmw, fun k hk => Or.inl (hpw k hk),
      Or.inl hpm⟩
  · exact ⟨w', hw', hr⟩

/-- The sink words of the extended trace are valid; the rest is unchanged. -/
theorem W0EpiOk.snoc_sk {sc : ℝ} (hw : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc)
    (hf : W0QuietE f) (h : W0EpiOk sc l)
    (hsk : w0SkWord (l ++ [f]) = w0NegInf ∨ ∃ sk, Rd (w0SkWord (l ++ [f])) sk)
    (hraw : ∀ v, w0SkRaw (l ++ [f]) = some v → ∃ x, Rd v x) : W0EpiOk sc (l ++ [f]) := by
  have hpe : f.pc ∉ [1157] := by simp [hf.pe]
  have hpe' : w0EpiPe (w0Scan (l ++ [f])).2 = w0EpiPe (w0Scan l).2 := by
    rw [w0Scan_snoc_quiet hw]
    simp only [w0EpiPe, w0Last_snoc_quiet _ hpe]
  have heo : w0EpiO (w0Scan (l ++ [f])).2 = w0EpiO (w0Scan l).2 := by
    rw [w0Scan_snoc_quiet hw]
    simp only [w0EpiO, w0Last_snoc_quiet _ hf.eo]
  unfold W0EpiOk
  rw [hpe', heo, w0Fin_snoc_quiet hw]
  obtain ⟨-, hpe0, heo0, -⟩ := h
  exact ⟨hsk, hpe0, heo0, hraw⟩

/-- An event that reads none of the epilogue's words keeps them valid. -/
theorem W0EpiOk.snoc_nosk {sc : ℝ} (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc) (hq : W0QuietE f)
    (hs : f.pc ≠ 103 ∧ f.pc ≠ 156) (h : W0EpiOk sc l) : W0EpiOk sc (l ++ [f]) := by
  refine h.snoc_sk hc hq ?_ ?_
  · rw [w0SkWord_snoc_quiet hs]
    exact h.1
  · rw [w0SkRaw_snoc_quiet hs]
    obtain ⟨-, -, -, hr⟩ := h
    exact hr

theorem W0EpiOk.snoc_quiet {sc : ℝ} (hf : W0Quiet f) (h : W0EpiOk sc l) :
    W0EpiOk sc (l ++ [f]) :=
  h.snoc_nosk hf.cut hf.toW0QuietE hf.sk

/-- An event below pc 578 in a block with no event past it does not start the vote's clause. -/
theorem W0Now.snoc_lt {sc : ℝ} (hc : f.pc ≠ w0ArrSPc ∧ f.pc ≠ w0ArrLPc) (hlt : f.pc < 578)
    (hno : ∀ a ∈ (w0Fin l).2, 103 ≤ a.pc → a.pc ≤ f.pc) (h : W0Now sc l) :
    W0Now sc (l ++ [f]) := by
  refine ⟨?_, ?_⟩
  · rw [w0Fin_snoc_quiet hc]
    exact h.1
  · rintro ⟨a, ha, hpa⟩
    rw [w0Fin_snoc_quiet hc] at ha
    rcases List.mem_append.mp ha with h1 | h1
    · have := hno a h1 (by omega)
      omega
    · simp only [List.mem_singleton] at h1
      subst h1
      omega

/-- **The general step**: the clauses of the extended trace and the validity of the trace. -/
theorem W0Valid.snoc {sc : ℝ} (h : W0Valid sc l) (hn : W0Now sc (l ++ [f]))
    (he : W0Early sc (l ++ [f])) (hp : W0EpiOk sc (l ++ [f])) : W0Valid sc (l ++ [f]) := by
  have key : ∀ j ≤ (l ++ [f]).length, (j ≤ l.length ∧ (l ++ [f]).take j = l.take j) ∨
      (l ++ [f]).take j = l ++ [f] := fun j hj => by
    by_cases hjl : j ≤ l.length
    · exact Or.inl ⟨hjl, List.take_append_of_le_length hjl⟩
    · refine Or.inr ?_
      simp only [List.length_append, List.length_singleton] at hj
      exact List.take_of_length_le (by simp; omega)
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rcases key j hj with ⟨hjl, he'⟩ | he'
    · rw [he']; exact h.1 j hjl
    · rw [he']; exact hn
  · rcases key j hj with ⟨hjl, he'⟩ | he'
    · rw [he']; exact h.2.1 j hjl
    · rw [he']; exact he
  · rcases key j hj with ⟨hjl, he'⟩ | he'
    · rw [he']; exact h.2.2 j hjl
    · rw [he']; exact hp

/-- The trace through event `e` is the trace before it with `e` appended. -/
theorem trace_take_succ {X : Execution} {g k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
  obtain ⟨hl, hk⟩ := List.getElem?_eq_some_iff.mp he
  rw [List.take_add_one, List.getElem?_eq_getElem hl]
  simp [hk]

/-- **An event that changes only the sink words**, to valid ones, keeps a trace valid. -/
theorem W0Valid.snoc_sk {sc : ℝ} (hsc : 0 < sc) (hw : W0QuietW f) (hf : W0QuietE f)
    (h : W0Valid sc l) (hsk : w0SkWord (l ++ [f]) = w0NegInf ∨ ∃ sk, Rd (w0SkWord (l ++ [f])) sk)
    (hraw : ∀ v, w0SkRaw (l ++ [f]) = some v → ∃ x, Rd v x) : W0Valid sc (l ++ [f]) :=
  h.snoc (h.now.snoc_quiet hw) (h.early.snoc_quiet hsc hw) (h.epi.snoc_sk hw.cut hf hsk hraw)

/-- **A quiet event keeps a trace valid.** -/
theorem W0Valid.snoc_quiet {sc : ℝ} (hsc : 0 < sc) (hf : W0Quiet f) (h : W0Valid sc l) :
    W0Valid sc (l ++ [f]) :=
  h.snoc (h.now.snoc_quiet hf.toW0QuietW) (h.early.snoc_quiet hsc hf.toW0QuietW)
    (h.epi.snoc_quiet hf)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
