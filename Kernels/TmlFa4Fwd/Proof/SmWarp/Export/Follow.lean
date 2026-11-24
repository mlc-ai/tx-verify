-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Types
public import Kernels.TmlFa4Fwd.Spec
public import Core.Data.Value
import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.Common.FollowDef

@[expose] public section

/-! # The following premises of one execution

`Follow` is the name of `FollowS` without its body: a theorem that takes `(hFw : Follow p L X)` does
not read the premises' definitions (the roles' reference invariants), so a change of them rebuilds
only the proofs that use a field (`Common/FollowView.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- **The premises under which the softmax and correction warps of `X` are followed.** -/
@[no_expose] def Follow (p : Params) (L : Launch) (X : Execution) : Prop := FollowS p L X

end PTX.Kernels.TmlFa4Fwd.Proof
