-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Proof.WarpFollows
public import Lemmas.Step.WarpVote

@[expose] public section

namespace PTX

noncomputable section

section
variable {L : Launch} {K : Kernel} {A : List Assumption}

end

variable {L : Launch} {K : Kernel} {A : List Assumption} {m : Mem0} {X : Execution}
    (hX : Consistent L K A m X) {g : Nat}
include hX

end
end PTX
