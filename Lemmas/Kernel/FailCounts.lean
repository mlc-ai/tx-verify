-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

/-! # A failed poll does not count

A proof tool for the bound obligation: an event of a `try_wait` that failed does not count toward
the size of an execution (`Event.counts`), so a role machine that stays in its state at a failed
poll needs no measure increase there. -/

namespace PTX

/-- **A failed poll does not count.** -/
theorem Event.counts_of_fail {e : Event} {l : Loc} {q : Nat} {ok a : Bool} {sc : MbarScope}
    (hk : e.kind = .wait l q ok a sc) (h : ¬ ok = true) : e.counts = false := by
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  simp only [Bool.not_eq_true] at h
  subst h
  rfl

end PTX
