-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.StaticCode

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

theorem Safe.noMatrix {X : Execution} (hX : Consistent L kernel Assumptions.all m X) :
    ¬ MatrixUnsafe L Assumptions.all X :=
  Lib.noMatrixUnsafe hX

end PTX.Kernels.InklingRelDecode.Proof.Top
