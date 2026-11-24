-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Machine

@[expose] public section

/-! # Induction along a run with the fired events

A proof tool. Like `Machine.after_induction`, but each step also knows that the event was
fired by a concrete state of the abstract state, so per-site facts about the event (which
object it names, which parity it polls with) can be used. -/

namespace PTX.Flow
open PTX

noncomputable section

namespace Machine

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {M : Machine K A L g}

theorem Trace.prefix_induction {σ0 : M.St} {es : List Event} (h : M.Trace σ0 es)
    (Q : M.St → List Event → Prop) (h0 : Q σ0 [])
    (hs : ∀ σ pre e σ' o, Q σ pre → M.Fired σ e o → M.next σ e = some σ' → Q σ' (pre ++ [e])) :
    ∀ j σ, M.after σ0 (es.take j) = some σ → Q σ (es.take j) := by
  intro j
  induction j with
  | zero => intro σ hσ; simp only [List.take_zero, after_nil, Option.some.injEq] at hσ; subst hσ;
              exact h0
  | succ j ih =>
    intro σ' hσ'
    by_cases hj : j < es.length
    · obtain ⟨e, he⟩ : ∃ e, es[j]? = some e := ⟨es[j], List.getElem?_eq_getElem hj⟩
      have htake : es.take (j + 1) = es.take j ++ [e] := by
        rw [List.take_add_one, he]; rfl
      rw [htake, after_snoc] at hσ'
      cases hτ : M.after σ0 (es.take j) with
      | none => rw [hτ] at hσ'; cases hσ'
      | some τ =>
        rw [hτ] at hσ'
        obtain ⟨o, hfired⟩ := h.fired_at he hτ
        exact htake ▸ hs τ (es.take j) e σ' o (ih τ hτ) hfired hσ'
    · have htake : es.take (j + 1) = es.take j := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [htake] at hσ' ⊢
      exact ih σ' hσ'

end Machine

end
end PTX.Flow
