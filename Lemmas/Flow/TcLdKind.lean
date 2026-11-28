-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Async

@[expose] public section

/-! # An event of a Tensor Memory load that is not undefined behaviour is the load

A proof tool beside `fires_tcLd`, which takes the thread that continues: here the continuation is
free, and the event is the load unless it records undefined behaviour. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- **The event of a Tensor Memory load**, at a site no assumption selects with `tcLdWait`. -/
theorem fires_tcLd_kind {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} {pc : Nat} {e : Event} {o : Option TState}
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e o)
    (hw : A.any (·.tcLdWait t.pc) = false) (hu : ∀ f, e.kind ≠ .ub f) :
    ∃ a vals, vals.length = ds.length ∧ e = ⟨pc, .tc (.ld a vals sh)⟩ := by
  rw [eventTmpl_tcLd_noWait hw, tcTmpl_tcLd_none hsh] at hf
  cases ha : readBits L g t 32 (.reg ta) with
  | error f =>
    simp [ofExec, ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf <;> (obtain ⟨rfl, -⟩ := hf; exact absurd rfl (hu _))
  | ok a =>
    simp [ofExec, ha, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> simp only [Fires] at hf
    all_goals first
      | (obtain ⟨rfl, -⟩ := hf; exact absurd rfl (hu _))
      | (obtain ⟨vals, hl, rfl, -⟩ := hf; exact ⟨_, vals, hl, rfl⟩)

end
end PTX.Flow
