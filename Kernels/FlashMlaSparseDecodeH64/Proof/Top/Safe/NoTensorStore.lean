-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit

@[expose] public section

/-! # ERR-REDUCTION-NO-RULE: no reduction without a rule

The safety class of Core's `Unsafe` this file owns (`TensorStoreUnsafe`). It is a static check of
the decoded program (`Lib/StaticCommit.lean`), so nothing of it is open. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-REDUCTION-NO-RULE**: no reduction without a rule. -/
theorem Safe.noTensorStore (_hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ TensorStoreUnsafe Assumptions.all X :=
  noTensorStoreUnsafe hX

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
