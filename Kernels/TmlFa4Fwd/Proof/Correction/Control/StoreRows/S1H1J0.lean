-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.StoreSpan
import Kernels.TmlFa4Fwd.Gen.StepCorrection
import Lemmas.Flow.SegCtl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat} {v : V}

theorem store_1_0_1 : StoreSpan p L g v 1 0 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_1_1 : StoreSpan p L g v 1 1 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_2_1 : StoreSpan p L g v 1 2 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_3_1 : StoreSpan p L g v 1 3 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
