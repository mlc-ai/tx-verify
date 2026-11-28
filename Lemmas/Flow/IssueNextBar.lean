-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.IssueNext

@[expose] public section

/-! # The continuation of `bar.sync` without a count

`bar.sync id` continues at the next instruction, as `bar.sync id, n` does
(`fires_barSyncN_next`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem fires_barSync_next {t u : TState} {a : Opnd} {al : Bool} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.barSync a al)) e (some u)) : u = PTX.next t := by
  simp only [eventTmpl, barTmpl] at hf
  repeat' split at hf
  all_goals simp_all [Fires]

end

end PTX.Flow
