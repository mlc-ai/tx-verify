-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The MMA lane's issue count: vocabulary

The MMA warp's loop issues 24 MMAs per block: QK MMA `k` (`k < 16`) is the `24 r + k`-th of block
`r`, PV MMA `k` (`k < 8`) the `24 r + 16 + k`-th. `mmaIssues` is the number of MMA events at the
pcs of the MMA warp's code (1853 to 2160) in a prefix of a lane's trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- An MMA event at a pc of the MMA warp's code. -/
def isMmaIssue (e : Event) : Bool :=
  decide (1853 ≤ e.pc ∧ e.pc ≤ 2160) &&
    match e.kind with
    | .tc (.mma ..) => true
    | _ => false

/-- The number of MMA issues in a prefix of a lane's trace. -/
def mmaIssues (xs : List Event) : Nat := xs.countP isMmaIssue

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
