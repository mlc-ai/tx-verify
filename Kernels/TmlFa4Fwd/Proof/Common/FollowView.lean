-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Common.FollowDef
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import all Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow

@[expose] public section

/-! # The fields of the following premises -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {X : Execution}

theorem Follow.intro (h : FollowS p L X) : Follow p L X := h
theorem follow {m} (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) :
    Follow p L X := Follow.intro
  ⟨fun _ _ k hw hg hi => CorrWarp.good hp hX hw hg hi k,
   fun _ _ k hw hg hi => SmWarp.good hp hX hw hg hi k⟩

end PTX.Kernels.TmlFa4Fwd.Proof
