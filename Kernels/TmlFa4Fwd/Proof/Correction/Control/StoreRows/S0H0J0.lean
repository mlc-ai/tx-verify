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

theorem store_0_0_0 : StoreSpan p L g v 0 0 0 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_0_1_0 : StoreSpan p L g v 0 1 0 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_0_2_0 : StoreSpan p L g v 0 2 0 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

theorem store_0_3_0 : StoreSpan p L g v 0 3 0 := by
  unfold StoreSpan
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
