-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit

@[expose] public section

/-! # ERR-TC-COMMIT: every commit targets an existing group

The safety class of Core's `Unsafe` this file owns (`TcCommitUnsafe`). It is a static check of the
decoded program (`Lib/StaticCommit.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-TC-COMMIT**: every commit targets an existing group. -/
theorem Safe.noTcCommit (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ TcCommitUnsafe L X :=
  noTcCommitUnsafe hp hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
