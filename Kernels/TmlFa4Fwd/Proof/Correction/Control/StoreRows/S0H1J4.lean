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

theorem store_0_4_1 : StoreSpan p L g v 0 4 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_0_5_1 : StoreSpan p L g v 0 5 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_0_6_1 : StoreSpan p L g v 0 6 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_0_7_1 : StoreSpan p L g v 0 7 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
