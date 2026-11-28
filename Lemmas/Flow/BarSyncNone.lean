-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.IssueNext

@[expose] public section

/-! # `bar.sync id` without a count continues at the next instruction

A proof tool: the template of `bar.sync` with no thread count continues in `next` of the state
(`fires_barSync_next`). -/

namespace PTX.Flow
open PTX

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_barSync_next {t u : TState} {a : Opnd} {al : Bool} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.barSync a al)) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, barTmpl] at hf
  repeat' split at hf
  all_goals simp_all [Fires]

end PTX.Flow
