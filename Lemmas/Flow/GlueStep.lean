-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Glue

@[expose] public section

/-! # The steps of a glued machine

A proof tool: a step of `Code.glue P R exit` to a state is a step of the first fragment followed by
the hand-off at its exits (`glue_inl_some`), or a step of the role it is in (`glue_inr_some`). A
measure or a ghost fact of a glued machine is proved fragment by fragment with these. -/

namespace PTX.Flow.Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {P : Code K A L g} {ι : Type}
  {R : ι → Code K A L g} {exit : P.D → Option ι}

/-- **A step of the first fragment**, then the hand-off at its exits. -/
theorem glue_inl_some {d : P.D} {e : Event} {σ' : (glue P R exit).D}
    (h : (glue P R exit).next (.inl d) e = some (some σ')) :
    ∃ d', P.next d e = some (some d') ∧ σ' = enter P R exit d' := by
  simp only [glue] at h
  cases hn : P.next d e with
  | none => rw [hn] at h; cases h
  | some o =>
    cases o with
    | none => rw [hn] at h; cases h
    | some d' =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨d', rfl, h.symm⟩

/-- **A step of a role.** -/
theorem glue_inr_some {i : ι} {d : (R i).D} {e : Event} {σ' : (glue P R exit).D}
    (h : (glue P R exit).next (.inr ⟨i, d⟩) e = some (some σ')) :
    ∃ d', (R i).next d e = some (some d') ∧ σ' = .inr ⟨i, d'⟩ := by
  simp only [glue] at h
  cases hn : (R i).next d e with
  | none => rw [hn] at h; cases h
  | some o =>
    cases o with
    | none => rw [hn] at h; cases h
    | some d' =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨d', rfl, h.symm⟩

end PTX.Flow.Code
