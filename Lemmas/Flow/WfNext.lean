-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataStepE

@[expose] public section

/-! # A machine that follows only reads whose bytes rebuild

`C.wfNext` is `C` with `next` cut to `none` on a read (`rd`, `nc`) whose bytes do not rebuild. The
step obligations of the load combinators (`step_load_sel`, ...) then need no case for bytes that
fault the thread, and `StepFor.of_wfNext` gives `C`'s strict step for an event whose bytes rebuild
(`EvRdOk`, `EvNcOk`). -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- `C` that follows a read only when its bytes rebuild. -/
@[reducible] def wfNext (C : Code K A L g) : Code K A L g :=
  { C with next := fun d e => match e.kind with
      | .rd _ bs => match rebuild 3 bs with
        | .ok _ => C.next d e
        | .error _ => none
      | .nc _ bs => match rebuild 3 bs with
        | .ok _ => C.next d e
        | .error _ => none
      | _ => C.next d e }

theorem wfNext_next (C : Code K A L g) (d : C.D) {e : Event} (h1 : EvRdOk e) (h2 : EvNcOk e) :
    (C.wfNext).next d e = C.next d e := by
  obtain ⟨pc, k⟩ := e
  cases k with
  | rd x bs =>
    obtain ⟨v, hv⟩ := h1 x bs rfl
    simp [wfNext, hv]
  | nc x bs =>
    obtain ⟨v, hv⟩ := h2 x bs rfl
    simp [wfNext, hv]
  | _ => rfl

/-- The strict step of `C` for an event whose bytes rebuild, from that of `C.wfNext`. -/
theorem StepFor.of_wfNext {C : Code K A L g} {d : C.D} {e : Event}
    (h : (C.wfNext).StepFor d e) (h1 : EvRdOk e) (h2 : EvNcOk e) : C.StepFor d e := by
  intro t u ins hat hi hc hf
  rw [← wfNext_next C d h1 h2]
  exact h ins hat hi hc hf

end
end PTX.Flow.Code
