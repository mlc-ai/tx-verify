-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreSpan
import Kernels.TmlFa4Fwd.Proof.Correction.Control.FenceSpan
import Kernels.TmlFa4Fwd.Gen.StepCorrection
import Lemmas.Flow.SegCtl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat} {v : V}

theorem store_1_12_1 : StoreSpan p L g v 1 12 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_13_1 : StoreSpan p L g v 1 13 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_14_1 : StoreSpan p L g v 1 14 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_15_1 : StoreSpan p L g v 1 15 1 := store_fence_span 1

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
