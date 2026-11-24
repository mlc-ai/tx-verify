-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp

@[expose] public section

/-! # The reference invariant of every lane, by name

The body of `JR` is not exposed: a theorem that takes `JR p L g σ` does not read the roles'
reference invariants, so a change of one rebuilds only the proofs that use it (`Top/JRView.lean`,
`Common/View.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The reference invariant of every lane: the softmax warps' or the migrated roles'. -/
@[no_expose] def JR (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  if Prologue.warpIndex L g < 8 then SmWarp.Ref p L (Prologue.warpIndex L g) g σ
  else RefAll p L g σ

end
end PTX.Kernels.TmlFa4Fwd.Proof
