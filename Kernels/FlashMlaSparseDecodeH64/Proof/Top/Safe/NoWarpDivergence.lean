-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll

@[expose] public section

/-! # ERR-NONUNIFORM-GUARD: no warp-divergent control flow at a uniform instruction

The safety class of Core's `Unsafe` this file owns (`WarpDivergent`). It is a static check of the
decoded program (`Lib/StaticPoll.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-NONUNIFORM-GUARD**: no warp-divergent control flow at a uniform instruction. -/
theorem Safe.noWarpDivergence (_hp : Pre P L mem0) {X : Execution}
    (_hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ WarpDivergent L kernel Assumptions.all X :=
  noWarpDivergent

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
