-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's events are no Tensor Memory loads or stores -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- A Tensor Memory load or store kind. -/
def IsLdSt : Kind → Prop
  | .tc (.ld ..) => True
  | .tc (.st ..) => True
  | _ => False

theorem epi_noldst {d : Epilogue.D} {pc : Nat} {k : Kind} (hk : IsLdSt k)
    (hev : Epilogue.Ev p L g d ⟨pc, k⟩) : False := by
  unfold Epilogue.Ev at hev
  split at hev <;> rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Epilogue.isStore, IsLdSt]

end
end PTX.Kernels.TmlFa4Fwd.Proof
