-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # No cancellation request, as a fact of the trace

The trace form of `noClcIssue` (`Lib/StaticCode.lean`, the static scan `Top/Safe/NoClc.lean`
uses): no event of a consistent execution is a cluster launch control request. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-- **No event is a cancellation request.** -/
theorem no_clcGet (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {sp : Clc.Spec}
    {tg : List Nat} : X.get i ≠ some ⟨pc, .clcIssue sp tg⟩ :=
  fun he => noClcIssue hX ⟨pc, he⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
