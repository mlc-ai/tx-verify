-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Reduce
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Kernels.RmsNorm.Proof.NoBarArrive

@[expose] public section

/-! # The barrier arrivals of the threads

A thread's barrier arrivals before a state are its arrivals on barrier `0` and on barrier `1`
(`countP_isBar`), so an arrival's number among all of the thread's arrivals is `3 i`, `3 i + 1` or
`3 i + 2` in row `i`, by its site (`bar_number`). The generation of an arrival is its number among
the thread's arrivals on its barrier (`bar_key`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem countP_isBar_split {l : List Event}
    (h : ∀ ev ∈ l, Execution.isBar ev = true →
      Execution.isBarId 0 ev = true ∨ Execution.isBarId 1 ev = true) :
    l.countP Execution.isBar = l.countP (Execution.isBarId 0) + l.countP (Execution.isBarId 1) := by
  induction l with
  | nil => rfl
  | cons ev l ih =>
    simp only [List.countP_cons]
    rw [ih fun ev' hm => h ev' (List.mem_cons_of_mem _ hm)]
    obtain ⟨pc, k⟩ := ev
    cases k <;> simp only [Execution.isBar, Execution.isBarId, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero]
    rename_i id c
    have := h _ (List.mem_cons_self) rfl
    simp only [Execution.isBarId, beq_iff_eq] at this
    rcases this with rfl | rfl <;> simp only [beq_self_eq_true, ↓reduceIte, Nat.reduceBEq,
      Bool.false_eq_true] <;> omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **The arrivals before a state**: two on barrier `0` and one on barrier `1` per row. -/
theorem countP_isBar {g k : Nat} {d : D} {e : Event} (hA : At P L X g k d e) :
    ((X.tr g).take k).countP Execution.isBar = d.bc0 + d.bc1 := by
  rw [countP_isBar_split, hA.bc0, hA.bc1]
  intro ev hm hb
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h' => absurd hjk h')] at hj
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp only [Execution.isBar, Bool.false_eq_true] at hb
  rename_i id c mode
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out (g, j) _ _ _ hj).elim
  obtain ⟨-, -, _, -, hs⟩ := bar_facts hpre hX ht (show X.IsBarrier (g, j) id c pc from hj)
  rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Execution.isBarId]

/-- The arrival number of a barrier site's arrival: `3 i`, `3 i + 1`, `3 i + 2` in row `i`. -/
theorem bar_number {g k id pc : Nat} {c : Option Nat} (he : X.IsBarrier (g, k) id c pc) :
    ∃ d, At P L X g k d ⟨pc, .bar id c⟩ ∧ c = none ∧ pc = d.site.pc ∧
      ((d.site = .bar0 ∧ id = 0 ∧ ((X.tr g).take k).countP Execution.isBar = 3 * d.i) ∨
        (d.site = .bar1 ∧ id = 0 ∧ ((X.tr g).take k).countP Execution.isBar = 3 * d.i + 1) ∨
        (d.site = .bar2 ∧ id = 1 ∧ ((X.tr g).take k).countP Execution.isBar = 3 * d.i + 2)) := by
  obtain ⟨-, hc, d, hA, hs⟩ := bar_facts hpre hX ht he
  have hn := countP_isBar hpre hX ht hA
  have hpc : pc = d.site.pc := by
    obtain ⟨t, o, hf⟩ := hA.event
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [siteTmpl, h1, Fires] at hf <;>
      rw [h1] <;> exact (Event.mk.inj hf.1).1
  refine ⟨d, hA, hc, hpc, ?_⟩
  rcases hs with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp only [D.bc0, D.bc1, h1] at hn
  · exact .inl ⟨h1, rfl, by omega⟩
  · exact .inr (.inl ⟨h1, rfl, by omega⟩)
  · exact .inr (.inr ⟨h1, rfl, by omega⟩)

/-- **The generation of an arrival is its arrival number on its barrier.** -/
theorem bar_key {e : EvId} {key : Nat} (hk : CtaBarK L X e key) :
    key / 16 = ((X.tr e.1).take e.2).countP (Execution.isBarId (key % 16)) := by
  have hg := hk.1
  obtain ⟨index, s, warp, count, lanes, g, hr, hs, hm, hphase, t, ht'⟩ := hk.2.2
  have href : e ∈ (Record.arrival (key % 16) warp count lanes).refs :=
    List.mem_map.mpr ⟨(g, e), hm, rfl⟩
  obtain ⟨hprot, hw, hcount⟩ := prefixFor hpre hX ht hg (key % 16) index warp count lanes hr href
  subst count
  have hk' := NamedBar.source_key hX (n := 8) (by decide) (target_none hpre) (cta_lt hpre hg) hr
    href hprot (Finset.card_range 8) (warps_bound hpre) hw
  have hu := CtaBarK.key_unique hX.ctaBar hk hk'
  omega

end
end PTX.Kernels.RmsNorm.Proof
