-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaAllocationRead
public import Kernels.TmlFa4Fwd.Proof.MmaDescriptorStartup

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The allocation has one extra store event on lane zero. -/
def descriptorShufflePos (lane : Nat) : Nat := if lane = 0 then 10 else 9

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

end
end PTX.Kernels.TmlFa4Fwd.Mma
