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

theorem store_1_8_1 : StoreSpan p L g v 1 8 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_9_1 : StoreSpan p L g v 1 9 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_10_1 : StoreSpan p L g v 1 10 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_11_1 : StoreSpan p L g v 1 11 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
