-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # ERR-CLUSTER-BARRIER: no cluster barrier fault

The safety class of Core's `Unsafe` this file owns (`ClusterFault`). It is a static check of the
decoded program (`Lib/StaticCode.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-CLUSTER-BARRIER**: no cluster barrier fault. -/
theorem Safe.noClusterFault (_hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ ClusterFault L X :=
  Proof.noClusterFault hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
