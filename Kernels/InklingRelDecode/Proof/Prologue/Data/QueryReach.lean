-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryRun
public import Kernels.InklingRelDecode.Proof.Prologue.Data.Carry
import Lemmas.Flow.DataCompute

@[expose] public section

/-! # The facts of a query site from a run

The data facts of the successor are carried (held before the run, written by nothing in the
region) or computed by the run. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section
open Classical in
/-- **A `Reach` to the data facts of `d'`**: each is a fact the run starts with, written before
`p`, or one the run ends with. -/
theorem reach_tags {Q L g} {F G0 : List (Nat × Value)} (d' : D) {p q : Nat}
    (hq : q = d'.c.site.pc) (hp : 27 ≤ p) (hpq : p ≤ q) (hq5 : q ≤ 574)
    (hseg : SegU kernel Assumptions.all L g p F q G0)
    (hnew : ∀ τ ∈ tags d'.c.site, (τ.reg, τ.val Q L g d') ∈ F ∧ τ.pc < p ∨
      (τ.reg, τ.val Q L g d') ∈ G0) :
    Reach kernel Assumptions.all L g p F (dF Q L g d') := by
  let f : Tag → Nat × Value := fun τ => (τ.reg, τ.val Q L g d')
  let P : Tag → Bool := fun τ => decide (f τ ∈ F ∧ τ.pc < p)
  have hpc := fun τ (h : τ ∈ tags d'.c.site) =>
    Nat.blt_eq.mp (List.all_eq_true.mp (tags_pc d'.c.site) τ h)
  refine Reach.carry_new (C := ((tags d'.c.site).filter P).map f)
    (N := ((tags d'.c.site).filter (fun τ => !P τ)).map f) (G0 := G0) Lib.rulesFrame
    ?_ ?_ (fun pc h1 h2 => seg_range (by omega) h2) hpq hq5 ?_ hseg ?_ ?_
  · rw [List.map_map]
    exact region_tags hp fun τ hτ => by
      obtain ⟨h1, h2⟩ := of_decide_eq_true (List.mem_filter.mp hτ).2; exact h2
  · rw [List.map_map]
    exact region_tags (by omega) fun τ hτ => by
      have := hpc τ (List.mem_filter.mp hτ).1; omega
  · refine fun R hR => holds_of_mem fun r v hm => ?_
    obtain ⟨τ, hτ, e⟩ := List.mem_map.mp hm
    obtain ⟨h1, -⟩ := of_decide_eq_true (List.mem_filter.mp hτ).2
    exact holds_mem hR (e ▸ h1)
  · refine fun R hR => holds_of_mem fun r v hm => ?_
    obtain ⟨τ, hτ, e⟩ := List.mem_map.mp hm
    have hn := (List.mem_filter.mp hτ).2
    simp only [Bool.not_eq_true', P, decide_eq_false_iff_not] at hn
    exact holds_mem hR (e ▸ (hnew τ (List.mem_filter.mp hτ).1).resolve_left hn)
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp (by simpa [dF] using hx)
    by_cases h : P τ = true
    · exact .inl (List.mem_map.mpr ⟨τ, List.mem_filter.mpr ⟨hτ, h⟩, rfl⟩)
    · exact .inr (List.mem_map.mpr ⟨τ, List.mem_filter.mpr ⟨hτ, by simpa using h⟩, rfl⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
