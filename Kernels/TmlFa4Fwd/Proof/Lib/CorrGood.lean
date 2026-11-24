-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Common.FollowView

@[expose] public section

/-! # The correction warps are followed under the following premises -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem corr_good (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (_hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11)
    (hg : g < L.threads) (k : Nat) : CorrWarp.Good p L (Prologue.warpIndex L g) X g k :=
  CorrWarp.good hp hX hw hg rfl k

end PTX.Kernels.TmlFa4Fwd.Proof
