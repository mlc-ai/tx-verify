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

theorem store_1_4_1 : StoreSpan p L g v 1 4 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_5_1 : StoreSpan p L g v 1 5 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_6_1 : StoreSpan p L g v 1 6 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_1_7_1 : StoreSpan p L g v 1 7 1 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
