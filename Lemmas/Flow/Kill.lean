-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code
public import Lemmas.Flow.Next

@[expose] public section

/-! # A successor that kills the thread where the code has no rule

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/Kill.lean`). Plan rule M1
asks a machine to die (`none`), not to stop (`some none`), where the code has no rule: a load
whose bytes do not rebuild (`BYTES`) sets the thread's fault. `Code.StepAt.kill` turns the
obligation of a machine into the obligation of the same machine whose successor is `none` on a
class of events, given that every continuation of such an event is dead; `dead_of_load_error`
is that fact for a plain load whose bytes do not rebuild. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The machine `C` with successor `none` at the events `kill` selects. -/
@[reducible] def Code.killAt (C : Code K A L g) (kill : C.D → Event → Bool) : Code K A L g :=
  { C with next := fun d e => if kill d e then none else C.next d e }

/-- **The obligation of a machine that kills the thread on a class of events.** -/
theorem Code.StepAt.kill {C : Code K A L g} {kill : C.D → Event → Bool} {d : C.D}
    (h : C.StepAt d)
    (hk : ∀ {t e u} ins, C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
      Fires (C.pc d) (eventTmpl A L g t ins.op) e (some u) → kill d e = true →
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    (C.killAt kill).StepAt d where
  site := h.site
  step := by
    intro t e u ins hat hi hc hf
    by_cases hkl : kill d e = true
    · exact .inr ⟨by simp [Code.killAt, hkl], hk ins hat hi hc hf hkl⟩
    · have hn : (C.killAt kill).next d e = C.next d e := by simp [Code.killAt, hkl]
      rw [hn]
      exact h.step ins hat hi hc hf

/-- A plain load of one element. -/
def plainLoad : Op → Bool
  | .mem a => a.kind == .load && !a.nc && a.ext == .same && a.regs.length == 1
  | _ => false

/-- **A plain load whose bytes do not rebuild leaves a dead thread.** -/
theorem dead_of_load_error {t u : TState} {op : Op} {pc : Nat} {e : Event}
    (hop : plainLoad op = true)
    (hf : Fires pc (eventTmpl A L g t op) e (some u))
    (hr : ∀ a bs, e.kind = .rd a bs → ∃ f, rebuild 3 bs = .error f) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) u := by
  cases op with
  | mem a =>
    simp only [plainLoad, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hop
    obtain ⟨⟨⟨hk, hnc⟩, he⟩, -⟩ := hop
    obtain ⟨r, bs, rfl, rfl⟩ := fires_load hk hnc hf he
    obtain ⟨f, hf'⟩ := hr r bs rfl
    exact Machine.dead_of_fault (f := f) (by simp [afterLoad, hf'])
  | _ => simp [plainLoad] at hop

end
end PTX.Flow
