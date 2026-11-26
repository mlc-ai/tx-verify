-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Roles

@[expose] public section

/-! # The steps of a role thread

The step of a role thread (`Code.roleThread`: a first fragment, then a role or a stub, with a
ledger) from a role state is the role's step (`roleThread_next_role`, `roleThread_next_of_role`);
from a state of the first fragment it is the fragment's step followed by the entry
(`roleThread_next_start`). Two role threads with the same first fragment follow the same events
from a state of the first fragment (`roleThread_next_start_of`). -/

namespace PTX.Flow.Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {P : Code K A L g}
  {ι E : Type} {R R' : ι → Code K A L g} {pcOf : E → Nat} {enterOf : P.D → Option E}
  {sel : E → P.D → Option ι} {κ : Type} {cls : κ → Event → Bool} {e : Event}

/-- **A role state steps by its role.** -/
theorem roleThread_next_role {i : ι ⊕ E} {d : (withStubs R pcOf i).D} {n : κ → Nat}
    {s' : (roleThread P R pcOf enterOf sel cls).D}
    (h : (roleThread P R pcOf enterOf sel cls).next (.inr ⟨i, d⟩, n) e = some (some s')) :
    ∃ d', (withStubs R pcOf i).next d e = some (some d') ∧ s'.1 = .inr ⟨i, d'⟩ := by
  change (((withStubs R pcOf i).next d e).map (Option.map fun d' =>
    (Sum.inr ⟨i, d'⟩ : P.D ⊕ (Σ i, (withStubs R pcOf i).D)))).map _ = _ at h
  rcases hq : (withStubs R pcOf i).next d e with _ | _ | d'
  · rw [hq] at h; cases h
  · rw [hq] at h; cases h
  · rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨d', rfl, by rw [← h]⟩

/-- **A role state follows where its role follows.** -/
theorem roleThread_next_of_role {i : ι ⊕ E} {d d' : (withStubs R pcOf i).D} {n : κ → Nat}
    (h : (withStubs R pcOf i).next d e = some (some d')) :
    ∃ s', (roleThread P R pcOf enterOf sel cls).next (.inr ⟨i, d⟩, n) e = some (some s') := by
  change ∃ s', (((withStubs R pcOf i).next d e).map (Option.map fun d' =>
    (Sum.inr ⟨i, d'⟩ : P.D ⊕ (Σ i, (withStubs R pcOf i).D)))).map _ = _
  rw [h]
  exact ⟨_, rfl⟩

/-- **A state of the first fragment steps by the fragment**, then enters its exit's role. -/
theorem roleThread_next_start {b : P.D} {n : κ → Nat}
    {s' : (roleThread P R pcOf enterOf sel cls).D}
    (h : (roleThread P R pcOf enterOf sel cls).next (.inl b, n) e = some (some s')) :
    ∃ b', P.next b e = some (some b') ∧
      s'.1 = enter P (withStubs R pcOf) (gatedExit enterOf sel) b' := by
  change ((P.next b e).map (Option.map (enter P (withStubs R pcOf) (gatedExit enterOf sel)))).map
    _ = _ at h
  rcases hq : P.next b e with _ | _ | b'
  · rw [hq] at h; cases h
  · rw [hq] at h; cases h
  · rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨b', rfl, by rw [← h]⟩

/-- **Two role threads with the same first fragment** follow the same events from its states. -/
theorem roleThread_next_start_of {b : P.D} {n n' : κ → Nat}
    {s' : (roleThread P R pcOf enterOf sel cls).D}
    (h : (roleThread P R pcOf enterOf sel cls).next (.inl b, n) e = some (some s')) :
    ∃ s'', (roleThread P R' pcOf enterOf sel cls).next (.inl b, n') e = some (some s'') := by
  obtain ⟨b', hb, -⟩ := roleThread_next_start h
  change ∃ s'', ((P.next b e).map
    (Option.map (enter P (withStubs R' pcOf) (gatedExit enterOf sel)))).map _ = _
  rw [hb]
  exact ⟨_, rfl⟩

end PTX.Flow.Code
