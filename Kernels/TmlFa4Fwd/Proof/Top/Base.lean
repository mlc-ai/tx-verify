-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Numerics
import Kernels.TmlFa4Fwd.Proof.Top.Register

@[expose] public section

/-! # Control following from the launch and execution -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Every consistent execution follows its control roles. -/
theorem launchFollow (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) :
    Follow p L X := Proof.follow hp hX

/-- **Every lane is followed with its role's reference invariant.** -/
theorem goodR' (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (k : Nat) : Frame.FollowedAt (thread p L) (JR p L) X g k :=
  goodR hp hX (launchFollow hp hX) hg k

end PTX.Kernels.TmlFa4Fwd.Proof
