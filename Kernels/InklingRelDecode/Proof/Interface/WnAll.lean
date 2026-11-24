-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WnProReach
public import Kernels.InklingRelDecode.Proof.Thread.WnWarpImm

@[expose] public section

/-!
# The prologue's producers of a preloaded block, and the warp collectives' operands (`Wn*`)

* `WnProReach.lean`: thread 0 and the leading threads of warps 0 and 1 at or past `bar18` made
  the arrival and the copies of each block below `num_pre`.
* `Thread/WnWarpImm.lean` (for the layers above): every warp collective of the program has
  immediate lane operands and a full member mask (`Lk.wImm_of_code`).
-/
