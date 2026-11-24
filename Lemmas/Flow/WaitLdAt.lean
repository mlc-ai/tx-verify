-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs

@[expose] public section

/-! # The state after an implicit `tcgen05.wait::ld`

A proof tool. At a `tcgen05.ld` an assumption selects with `tcLdWait`, sub-step 1 performs the
implicit wait and continues at the next instruction's first sub-step with the registers
unchanged: every register fact of the wait's state holds there (`waitLd_at`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- The implicit wait of a load: the event is `tcgen05.wait::ld`, and the thread is at the next
instruction, at its first sub-step, with the facts of the wait's state. -/
theorem waitLd_at {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat}
    {e : Event} {ds : List Nat} {ta : Nat} {sh : TcShape} {F : List (Nat × Value)}
    (hw : A.any (·.tcLdWait pc) = true) (hpc : t.pc = pc) (hs : t.sub ≠ 0) (hacc : t.acc = [])
    (hfl : t.fault = none) (hF : Holds t.regs F)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e (some u)) :
    e = ⟨pc, .tc .waitLd⟩ ∧ At u (pc + 1) F := by
  subst hpc
  simp only [eventTmpl, tcLdTmpl, hw, ↓reduceIte, hs, Fires] at hf
  obtain ⟨rfl, hu⟩ := hf
  obtain rfl := Option.some.inj hu
  exact ⟨rfl, rfl, rfl, hacc, hfl, hF⟩

end
end PTX.Flow
