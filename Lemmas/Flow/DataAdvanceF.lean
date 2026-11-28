-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataAdvance

@[expose] public section

/-! # The data step of an advancing event from the state's whole facts

`DataStep.advance` starts the `Reach` after an advancing event from the data facts of the state.
A `Reach` that also needs the control facts (a predicate that guards a skipped load) starts from
all the facts of the state. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of an advancing event** (`hadv`: the event leaves the thread in `next t`), the
`Reach` after it from the facts of the state. -/
theorem DataStep.advanceF {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ins : Instr} (hc : K.code[C'.pc d]? = some ins)
    (hadv : ∀ {t e u}, Fires (C'.pc d) (eventTmpl A L g t ins.op) e (some u) → u = PTX.next t)
    (hs : C'.sub d = 0) (ha : C'.acc d = [])
    (hrun : ∀ e d', C'.next d e = some (some d') →
      Reach K A L g (C'.pc d + 1) (C'.facts d) (dF d')) :
    DataStep C' dF d := by
  intro t e u d' ins' hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := hadv hf
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  exact hrun e d' hn (PTX.next t) ⟨by simp [PTX.next, hpc], hsub.trans hs, hacc.trans ha, hft,
    hreg⟩

end
end PTX.Flow.Code
