-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp

@[expose] public section

/-! # The following premises of one execution: the fields

The four premises under which the softmax and correction warps are followed.
`SmWarp/Export/Follow.lean` gives them the opaque name `Follow`, which the theorems above the roles
take; a proof that uses a field imports `Common/FollowView.lean`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- Both control fragments track their warp's scheduler and ledger throughout the trace. -/
structure FollowS (p : Params) (L : Launch) (X : Execution) : Prop where
  correction : ∀ g w k, 8 ≤ w ∧ w ≤ 11 → g < L.threads → Prologue.warpIndex L g = w →
    CorrWarp.Good p L w X g k
  softmax : ∀ g w k, w < 8 → g < L.threads → Prologue.warpIndex L g = w →
    SmWarp.Good p L w X g k

end PTX.Kernels.TmlFa4Fwd.Proof
