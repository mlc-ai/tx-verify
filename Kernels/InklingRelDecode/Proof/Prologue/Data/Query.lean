-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.Column
public import Lemmas.Flow.DataLoadG

@[expose] public section

/-! # The query loads and stores in the value machine

A guarded query load puts the half in the successor's record; the stores keep the packed words. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section

theorem ldq_fresh : ∀ j, qDst j ∉ ctlLive (Site.ldq j).pc ∧
    ∀ τ ∈ tags (.ldq j), τ.reg ≠ qDst j := by decide +kernel

/-- The facts of a state after a load wrote `v` in a register nothing names. -/
theorem holds_snoc {R : Nat → Option Value} {F : List (Nat × Value)} {r : Nat} {v : Value}
    (h : Holds R F) (hn : r ∉ F.map Prod.fst) :
    Holds (Function.update R r (some v)) (F ++ [(r, v)]) :=
  holds_of_mem fun x y hm => by
    refine holds_mem (holds_update_cons (x := v) h hn) ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with hm | hm
    exacts [Or.inr hm, Or.inl hm]

/-- **The data step of a query load**, from the `Reach` after it for each successor. -/
theorem ldq_step_of {Q L g w} (d : D) (j : Fin 64) (hs : d.c.site = .ldq j)
    (hR : ∀ (d' : D) (v : Value), queryOn (g % L.block) (j.val / 16) d.c = true →
      d'.c = {d.c with site := afterQuery d.c (g % L.block) j} →
      d'.v = ⟨d.v.pay, Function.update d.v.q j v⟩ →
      Reach kernel Assumptions.all L g ((Site.ldq j).pc + 1)
        ((checkedCode Q L g w).facts d.c ++ dF Q L g d ++ [(qDst j, v)]) (dF Q L g d')) :
    DataStep (code Q L g w) (dF Q L g) d := by
  have hc : kernel.code[(code Q L g w).pc d]? = some (qLoad j) := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact (qLoadPair (L := L) (g := g) j).2
  intro t₀ e₀ u₀ d₀ ins₀ hat₀ hi₀ hc₀ hf₀ hn₀
  refine DataStep.loadG (r := qDst j) hc rfl rfl rfl rfl
    (fun _ => by show d.c.site.sub = 0; rw [hs]; rfl) (fun _ => rfl) ?_ ins₀ hat₀ hi₀ hc₀ hf₀ hn₀
  intro hi x bs v d' t hv hn hat
  obtain ⟨c, hnc, rfl⟩ := succ_split hn
  have hq : record d ⟨(code Q L g w).pc d, .rd x bs⟩ =
      ⟨d.v.pay, Function.update d.v.q j v⟩ := by
    have : loadVal bs = v := by simp [loadVal, hv, Except.toOption]
    simp [record, hs, this]
  have hcc : c = {d.c with site := afterQuery d.c (g % L.block) j} := by
    simp only [Control.next, hs, Option.some.injEq] at hnc
    exact hnc.symm
  obtain ⟨hp0, hs0, ha0, hf0, hr0⟩ := hat
  have hon : queryOn (g % L.block) (j.val / 16) d.c = true := by
    have := hi.1; simpa only [Control.Inv, hs] using this
  refine hR ⟨c, _⟩ v hon hcc hq _ ⟨?_, rfl, rfl, hf0, ?_⟩
  · show t.pc + 1 = _
    rw [hp0]; show d.c.site.pc + 1 = _; rw [hs]
  · obtain ⟨hc1, hd1⟩ := ldq_fresh j
    exact holds_snoc hr0 (fresh_facts (w := w) (by rw [hs]; exact hc1) (fun τ hτ => by
      rw [hs] at hτ; exact hd1 τ hτ))

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
