-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Flow PTX.Proof AsyncCopy Prologue

/-- The two completion objects of the Q tensor loads. -/
def queryObject (l : Launch) (cta : Nat) (stage : Fin 2) : Loc :=
  ⟨.shared, cta, l.sharedBase + 8 * stage.val⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

end PTX.Kernels.TmlFa4Fwd.Thread.Output
