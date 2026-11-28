-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Seen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The arrival that ends the set-up keeps warpgroup 0's trace valid

The arrival at pc 200 restarts the statistics (`w0Fin`). The block in progress before it has only
events at pcs up to 200 (`w0_boundSeen`), so it has read none of the block's words, the vote has
not happened, and the epilogue's words are unread. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A block with events only at pcs up to 200 has read no word. -/
theorem w0Words_small {seg : List Event} (h : ∀ a ∈ seg, a.pc ≤ 200) :
    (w0Words seg).lo = [] ∧ (w0Words seg).hi = [] ∧ (w0Words seg).mw = .pred false ∧
      (∀ k < 8, (w0Words seg).pw k = (.pred false, .pred false)) ∧
      (w0Words seg).pm = .pred false := by
  have hn : ∀ {α : Type} (f : Event → Option α) (pcs : List Nat), (∀ p ∈ pcs, 200 < p) →
      w0Last f pcs seg = none := by
    intro α f pcs hp
    unfold w0Last
    have : seg.filterMap (fun e => if e.pc ∈ pcs then f e else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro e he
      have h1 := h e he
      have : e.pc ∉ pcs := fun hm => by have := hp _ hm; omega
      simp [this]
    rw [this]; rfl
  refine ⟨?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · simp [w0Words, hn _ [280, 283] (by simp)]
  · simp [w0Words, hn _ [278, 285] (by simp)]
  · simp [w0Words, hn _ [289] (by simp)]
  · have : seg.filter (fun e => e.pc = 477 + 5 * k && (w0RdVal e).isSome) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      have := h e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro h'; omega
    simp [w0Words, hk, w0Peer, this, lastN]
  · simp [w0Words, hn _ [572] (by simp)]

/-- A block with events only at pcs up to 200 has no reading of the epilogue. -/
theorem w0Epi_small {seg : List Event} (h : ∀ a ∈ seg, a.pc ≤ 200) :
    w0EpiPe seg = .pred false ∧ w0EpiO seg = [] := by
  have hn : ∀ {α : Type} (f : Event → Option α) (pcs : List Nat), (∀ p ∈ pcs, 200 < p) →
      w0Last f pcs seg = none := by
    intro α f pcs hp
    unfold w0Last
    have : seg.filterMap (fun e => if e.pc ∈ pcs then f e else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro e he
      have h1 := h e he
      have : e.pc ∉ pcs := fun hm => by have := hp _ hm; omega
      simp [this]
    rw [this]; rfl
  exact ⟨by simp [w0EpiPe, hn _ [1157] (by simp)],
    by simp [w0EpiO, hn _ w0OPcs (by simp [w0OPcs])]⟩

/-- **The core of the restart clause**: the arrival at pc 200 after a block whose events are all at
pcs up to 200 keeps a trace valid. -/
theorem w0Core_restart {sc : ℝ} (hsc : 0 < sc) {l : List Event} {e : Event} (hpc : e.pc = 200)
    (hsm : ∀ a ∈ (w0Fin l).2, a.pc ≤ 200) (h : W0Valid sc l) : W0Valid sc (l ++ [e]) := by
  have hsm' : ∀ a ∈ (w0Fin l).2 ++ [e], a.pc ≤ 200 := fun a ha => by
    rcases List.mem_append.mp ha with h1 | h1
    · exact hsm a h1
    · simp only [List.mem_singleton] at h1; rw [h1]; omega
  have hfin : w0Fin (l ++ [e]) = ([], (w0Fin l).2 ++ [e]) := by
    rw [w0Fin_snoc]
    simp [hpc, w0ArrSPc, w0ArrLPc]
  have hscan : (w0Scan (l ++ [e])).2 = (w0Scan l).2 ++ [e] := by
    rw [w0Scan_snoc]
    simp [hpc, w0ArrSPc]
  have hsc' : ∀ a ∈ (w0Scan (l ++ [e])).2, a.pc ≤ 200 := fun a ha => by
    rw [hscan, ← w0Fin_snd] at ha
    exact hsm' a ha
  have hn : W0Now sc (l ++ [e]) := by
    refine ⟨?_, ?_⟩
    · rw [hfin]; intro seg hs; cases hs
    · rw [hfin]
      rintro ⟨a, ha, hp'⟩
      have := hsm' a ha
      omega
  obtain ⟨hlo, hhi, hmw, hpw, hpm⟩ := w0Words_small hsm'
  have hea : W0Early sc (l ++ [e]) := by
    unfold W0Early
    rw [hfin]
    obtain ⟨w', hw'⟩ := w0Ok_canon hsc
    simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_or]
    exact ⟨w', hw', Or.inl hlo, Or.inl hhi, Or.inl hmw, fun k hk => Or.inl (hpw k hk),
      Or.inl hpm⟩
  obtain ⟨hpe, heo⟩ := w0Epi_small hsc'
  have hsk : w0SkWord (l ++ [e]) = w0SkWord l := w0SkWord_snoc_quiet (by omega)
  have hraw : w0SkRaw (l ++ [e]) = w0SkRaw l := w0SkRaw_snoc_quiet (by omega)
  have hep : W0EpiOk sc (l ++ [e]) := by
    obtain ⟨h1, -, -, h4⟩ := h.epi
    refine ⟨by rw [hsk]; exact h1, Or.inl hpe, Or.inl heo, by rw [hraw]; exact h4⟩
  exact h.snoc hn hea hep

/-- **The arrival at pc 200 keeps the trace valid** (the event is no undefined behaviour). -/
theorem w0Valid_snoc_restart_hub (hp : Pre P L m)
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hw : warp L g < 4)
    (hpc : e.pc = 200) (h : W0Valid P.scale ((X.tr g).take k)) :
    W0Valid P.scale ((X.tr g).take (k + 1)) := by
  rw [trace_take_succ he]
  obtain ⟨hb, -, -⟩ := w0_boundSeen hp hX hFw hw he hub (by omega) h
  exact w0Core_restart hp.scalePos hpc (fun a ha => by
    by_cases h1 : 103 ≤ a.pc
    · have := hb a ha h1; omega
    · omega) h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
