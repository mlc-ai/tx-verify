-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.StaticCode

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noCluster {X : Execution} (hX : Consistent L kernel Assumptions.all m X) :
    ¬ ClusterFault L X :=
  Lib.noClusterFault hX

end PTX.Kernels.InklingRelDecode.Proof.Top
