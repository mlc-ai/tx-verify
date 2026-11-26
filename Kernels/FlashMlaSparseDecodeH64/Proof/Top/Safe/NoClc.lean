-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # ERR-CLC: no cancellation fault

The safety class of Core's `Unsafe` this file owns (`ClcUnsafe`). It is a static check of the
decoded program (`Lib/StaticCode.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-CLC**: no cancellation fault. -/
theorem Safe.noClc (_hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ ClcUnsafe L X :=
  noClcUnsafe hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
