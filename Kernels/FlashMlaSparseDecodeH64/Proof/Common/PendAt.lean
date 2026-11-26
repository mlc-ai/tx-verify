-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollKey
public import Lemmas.Kernel.Frame
public import Kernels.FlashMlaSparseDecodeH64.Spec
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles

@[expose] public section

/-! # A lane at a thread state of a class

The classes of the thread machine's states a pending lane can be at, by name only (their bodies
are `Common/PendAtView.lean`'s, as `Follow`'s): the machine follows the lane's trace to a state
at a warp collective with a static part (`PendAtColl`), or to a state of the thread machine's
invariant at a given pc (`PendAtPc`). The steps of a pending lane at such a state are stated with
them, so that a lane is described without a next event (`Common/Export/NextAll.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- **The lane's machine is at a warp collective with a static part** after the lane's whole
trace. -/
@[no_expose] def PendAtColl (P : Params) (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∃ σ : (thread P L g).D, Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) ∧
    ∃ ins, kernel.code[(thread P L g).pc σ]? = some ins ∧ CollIns ins

/-- **The lane's machine is at the instruction at `pc`**, at a state that meets the thread
machine's invariant, after the lane's whole trace. -/
@[no_expose] def PendAtPc (P : Params) (L : Launch) (X : Execution) (g pc : Nat) : Prop :=
  ∃ σ : (thread P L g).D, Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) ∧
    (thread P L g).inv σ ∧ (thread P L g).pc σ = pc

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
