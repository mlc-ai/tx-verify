-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Migrated
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Top.JR
import all Kernels.TmlFa4Fwd.Proof.Top.JR

@[expose] public section

/-! # The reference invariant of every lane, unfolded -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

theorem JR_eq (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) :
    JR p L g σ = if Prologue.warpIndex L g < 8 then SmWarp.Ref p L (Prologue.warpIndex L g) g σ
      else RefAll p L g σ := by
  unfold JR
  rfl

end PTX.Kernels.TmlFa4Fwd.Proof
