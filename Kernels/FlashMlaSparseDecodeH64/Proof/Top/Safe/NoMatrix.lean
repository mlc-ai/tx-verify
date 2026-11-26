-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # ERR-WARP-MATRIX: no undefined warp matrix instance

The safety class of Core's `Unsafe` this file owns (`MatrixUnsafe`). It is a static check of the
decoded program (`Lib/StaticCode.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-WARP-MATRIX**: no undefined warp matrix instance. -/
theorem Safe.noMatrix (_hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ MatrixUnsafe L Assumptions.all X :=
  noMatrixUnsafe hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
