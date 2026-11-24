-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time

@[expose] public section

/-! # A lane's time from its last two states -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof

variable {p : Params} {L : Launch} {X : Execution} {g : Nat}

/-- A lane's time is bounded by the times of its last two states. -/
theorem threadTime_le {T : Nat}
    (h1 : ∀ σ, Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ) →
      Progress.time p L g σ ≤ T)
    (h2 : ∀ σ e, Frame.stateAt (thread p L) X g ((X.tr g).length - 1) = some (some σ) →
      X.get (g, (X.tr g).length - 1) = some e → Progress.time p L g σ + 1 ≤ T) :
    Sched.threadTime (Progress.timed p L) X g ≤ T := by
  unfold Sched.threadTime
  split
  · rename_i σ hσ; exact h1 σ hσ
  · exact Nat.zero_le _
  · rename_i hnone
    split
    · rename_i σ hσ
      have hlen : 0 < (X.tr g).length := by
        by_contra h0
        rw [show (X.tr g).length = 0 by omega, Frame.stateAt_zero] at hnone
        cases hnone
      exact h2 σ _ hσ (List.getElem?_eq_getElem (show (X.tr g).length - 1 < (X.tr g).length by
          omega))
    · exact Nat.zero_le _

end PTX.Kernels.TmlFa4Fwd.Proof
