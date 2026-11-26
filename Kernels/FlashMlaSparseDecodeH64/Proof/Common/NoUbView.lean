-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NoUbRole
import all Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbAt

@[expose] public section

/-! # The bodies of `AliveIn` and `StopsAt`

For `Common/` and the roles' exports, which read the vocabulary of the leaves
(`Common/Export/NoUbAt.lean`) through these two equations. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

theorem aliveIn_iff {P : Params} {L : Launch} {X : Execution} {g k : Nat} {r : RoleId} :
    AliveIn P L X g k r ↔
      ∃ σ, Frame.stateAt (thread P L) X g k = some (some σ) ∧ InRole P L g r σ := Iff.rfl

theorem stopsAt_iff {P : Params} {L : Launch} {X : Execution} {g k : Nat} :
    StopsAt P L X g k ↔ Frame.stateAt (thread P L) X g (k + 1) = none := Iff.rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
