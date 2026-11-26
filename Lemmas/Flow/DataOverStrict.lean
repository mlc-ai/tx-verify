-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataOver
public import Lemmas.Flow.StrictWindow

@[expose] public section

/-! # The strict step of a value state from the control machine's

A proof tool beside `Over.stepAtU` (`Lemmas/Flow/DataOver.lean`). `Over.stepFor_quiet`: a value
machine over a control machine, at a state whose successors carry no data facts, takes the strict
step (`Code.StepFor`) of the control machine at the erased state (when its invariant holds): the
erased concrete state is the same, the successor's facts are the control facts. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A value state whose successors have no data facts** takes the control state's strict step. -/
theorem Over.stepFor_quiet {C' C : Code K A L g} {er : C'.D → C.D} {dF : C'.D → List (Nat × Value)}
    (hO : Over C' C er dF) {d : C'.D} (hS : C.inv (er d) → C.StepAt (er d))
    (hq : ∀ e d', C'.next d e = some (some d') → dF d' = []) (e : Event) : C'.StepFor d e := by
  intro t u ins hat hi hc hf
  have hF := hat.2.2.2.2
  rw [hO.facts, holds_append] at hF
  have htc : C.AtD (er d) t :=
    ⟨hat.1.trans (hO.pc d), hat.2.1.trans (hO.sub d), hat.2.2.1.trans (hO.acc d), hat.2.2.2.1,
      hF.1⟩
  have hic := (hO.inv d).mp hi
  rw [hO.pc] at hc hf
  rcases (hS hic).step ins htc hic hc hf with (hy | ⟨c', t', hy, hl, hg⟩) | ⟨hy, hd⟩
  · rcases hn : C'.next d e with _ | _ | d'
    · rw [hO.stop hn] at hy; cases hy
    · exact .inl (.inl rfl)
    · rw [hO.next hn] at hy; cases hy
  · rcases hn : C'.next d e with _ | _ | d'
    · rw [hO.stop hn] at hy; cases hy
    · exact .inl (.inl rfl)
    · have hx := hO.next hn
      rw [hx] at hy
      obtain rfl := Option.some.inj (Option.some.inj hy)
      refine .inl (.inr ⟨d', t', rfl, hl, ?_⟩)
      obtain ⟨hat', hinv'⟩ := hg
      refine ⟨⟨hat'.1.trans (hO.pc d').symm, hat'.2.1.trans (hO.sub d').symm,
        hat'.2.2.1.trans (hO.acc d').symm, hat'.2.2.2.1, ?_⟩, (hO.inv d').mpr hinv'⟩
      rw [hO.facts, hq e d' hn, holds_append]
      exact ⟨hat'.2.2.2.2, trivial⟩
  · rcases hn : C'.next d e with _ | _ | d'
    · exact .inr ⟨rfl, hd⟩
    · exact .inl (.inl rfl)
    · rw [hO.next hn] at hy; cases hy

end
end PTX.Flow.Code
