-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataStepE

@[expose] public section

/-! # A machine that follows only the events that satisfy a predicate

`C.cut Ok` is `C` with `next` cut to `some none` (the machine stops following) on an event that does
not satisfy `Ok`. A step obligation of the load combinators then holds without a case for such an
event, and `StepFor.of_cut` gives `C`'s strict step for an event that satisfies `Ok`. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

open Classical in
/-- `C` that follows an event only when it satisfies `Ok`. -/
@[reducible] def cut (C : Code K A L g) (Ok : Event → Prop) : Code K A L g :=
  { C with next := fun d e => if Ok e then C.next d e else some none }

theorem cut_next (C : Code K A L g) (d : C.D) {Ok : Event → Prop} {e : Event} (h : Ok e) :
    (C.cut Ok).next d e = C.next d e := by
  simp [cut, h]

theorem cut_next_not (C : Code K A L g) (d : C.D) {Ok : Event → Prop} {e : Event} (h : ¬ Ok e) :
    (C.cut Ok).next d e = some none := by
  simp [cut, h]

/-- The strict step of `C` for an event that satisfies `Ok`, from that of `C.cut Ok`. -/
theorem StepFor.of_cut {C : Code K A L g} {Ok : Event → Prop} {d : C.D} {e : Event}
    (h : (C.cut Ok).StepFor d e) (hOk : Ok e) : C.StepFor d e := by
  intro t u ins hat hi hc hf
  rw [← cut_next C d hOk]
  exact h ins hat hi hc hf

end
end PTX.Flow.Code
