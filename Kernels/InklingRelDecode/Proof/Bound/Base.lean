-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Generic

@[expose] public section

/-!
# Counted events

An event counts (`Event.counts`) unless it is a failed `try_wait`. Every rank step of this
directory compares the ranks of two states with the count of the event between them: at most one,
and exactly the poll's success for a poll.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound
open PTX

noncomputable section

/-- An event counts at most once. -/
theorem counts_le (e : Event) : (if e.counts then 1 else 0) ≤ 1 := by
  split <;> omega

/-- A poll counts exactly when it succeeds. -/
theorem counts_wait {e : Event} {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope}
    (hk : e.kind = .wait m p ok acq sc) : e.counts = ok := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases ok <;> rfl

/-- A step through a mapped successor comes from a step of the mapped machine. -/
theorem map_inv {α β : Type} {f : α → β} {o : Option (Option α)} {b : β}
    (h : o.map (Option.map f) = some (some b)) : ∃ a, o = some (some a) ∧ f a = b := by
  rcases o with _ | _ | a
  · cases h
  · cases h
  · exact ⟨a, rfl, by simpa using h⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Bound
