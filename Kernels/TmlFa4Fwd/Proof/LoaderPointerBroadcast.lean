-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPointerReload
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The lane selected by source operand zero is the first lane in its eight-lane group. -/
def pointerBroadcastLane (lane : Nat) : Nat := 8 * (lane / 8)

end
end PTX.Kernels.TmlFa4Fwd.Loader
