-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll

@[expose] public section

/-! # ERR-POLL-SHAPE: every poll is a canonical spin

The safety class of Core's `Unsafe` this file owns (`PollShapeUnsafe`). It is a static check of the
decoded program (`Lib/StaticPoll.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-POLL-SHAPE**: every poll is a canonical spin. -/
theorem Safe.noPollShape (_hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ PollShapeUnsafe kernel X :=
  noPollShapeUnsafe hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
