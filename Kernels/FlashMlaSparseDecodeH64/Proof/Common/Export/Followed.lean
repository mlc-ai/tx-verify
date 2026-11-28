-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowProof

@[expose] public section

/-! # The following theorem of the launch

`follow_of`: every consistent execution is followed by the thread machine (`Follow`), with no
premise beyond `Pre`. The proof is `Common/FollowProof.lean`'s `follow_at`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The following theorem of the launch.** -/
theorem follow_of (hp : Pre P L m) :
    ∀ X, Consistent L kernel Assumptions.all m X → Follow P L X :=
  fun _ hX => follow_at hp hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
