-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Warp.PollSync
import Kernels.InklingRelDecode.Proof.Lib.WarpGuard

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **ERR-NONUNIFORM-GUARD**: the six guarded `tcgen05` instructions have warp-uniform guards, and
the poll branches are exempted or ordered. -/
theorem Safe.noWarpDivergence (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X) :
    ¬ WarpDivergent L kernel Assumptions.all X :=
  not_warpDivergent_synced' Lib.lane_ok
    (Lib.not_divergentAt (by rw [hp.ntid,hp.block]) hp.block)
    Lib.localLands (Protocol.Warp.poll_synced hp hX hf rows)

end PTX.Kernels.InklingRelDecode.Proof.Top
