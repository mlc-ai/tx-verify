-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasEnd
import Kernels.TmlFa4Fwd.Proof.Softmax.Base

@[expose] public section

/-! # The numeric steps of every softmax lane

The one numeric state `Softmax.stepAt_ctl` leaves out, the closing poll of a bias round, is
stepped by `Softmax.stepAt_pwendB`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0}

/-- **The numeric steps hold.** -/
theorem numAll (hp : Pre p L m) : NumAll p L := by
  rintro g - - ⟨s, v, k, acc⟩ hn
  by_cases hi : (k = 0 ∧ acc = [] ∧ s.first = true) ∨ s.midOk k acc
  swap
  · exact stepAt_junk hi
  cases s with
  | pwend r =>
    cases r with
    | bias =>
      rcases hi with ⟨rfl, rfl, -⟩ | h
      · exact stepAt_pwendB hp v
      · exact h.elim
    | _ => simp [D.numeric] at hn
  | _ => simp [D.numeric] at hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
