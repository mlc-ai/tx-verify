-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import all Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAt

@[expose] public section

/-! # The bodies of the lane's state classes

For a role's export (or `Common/`) that opens `PendAtColl` or `PendAtPc` (it reads the body
through `import all`, which only `Common/` may use). Files above `Common/` do not import this
file. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

theorem pendAtColl_iff {P : Params} {L : Launch} {X : Execution} {g : Nat} :
    PendAtColl P L X g ↔ ∃ σ : (thread P L g).D,
      Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) ∧
        ∃ ins, kernel.code[(thread P L g).pc σ]? = some ins ∧ CollIns ins :=
  Iff.rfl

theorem pendAtPc_iff {P : Params} {L : Launch} {X : Execution} {g pc : Nat} :
    PendAtPc P L X g pc ↔ ∃ σ : (thread P L g).D,
      Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ) ∧
        (thread P L g).inv σ ∧ (thread P L g).pc σ = pc :=
  Iff.rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
