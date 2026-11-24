-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WnPre
public import Kernels.InklingRelDecode.Proof.Progress.WnShape
public import Kernels.InklingRelDecode.Proof.Progress.WnLag
public import Kernels.InklingRelDecode.Proof.Progress.WnLast

@[expose] public section

/-!
# The preloaded blocks of the `kv_ready` poll, `WarpCollFacts.shape` and `last` (`Wn*`)

* `WnPre.lean`: `Wn.mmaKvPre_of`, the blocker clause of the MMA warp's poll of `kv_ready i` for a
  block `i < num_pre`, whose producers are the prologue's thread 0 and the leading threads of
  warps 0 and 1.
* `WnShape.lean`: `Wn.warpColl_shape`, the field `shape` of `WarpCollFacts`, from the immediate
  operands of the program's warp collectives and the lockstep of the lanes.
* `WnLag.lean`: `Wn.lag_ordinal`, the lockstep under the premise of `WarpCollFacts.lag`.
* `WnLast.lean`: `Wn.warpColl_last`, the field `last` of `WarpCollFacts`: the blocking event
  before a warp collective is fired from a synchronizing state, so it is the event of the
  lockstep's previous synchronizing position, made by every lane at the same warp collective.
-/
