-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsTab
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The bias words' table is consistent with the code

One pass over the code of each path (`tabScan`): outside the moves no instruction writes a fact's
register and the keys only shrink. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section

theorem wtab_scan_a : tabScan kernel (wIvs .a) (wKeys .a) wPost wSpecB = true := by
  decide +kernel

theorem wtab_scan_p : tabScan kernel (wIvs .p) (wKeys .p) wPost wSpecB = true := by
  decide +kernel

theorem wtab_scan_b : tabScan kernel (wIvs .b) (wKeys .b) wPost wSpecB = true := by
  decide +kernel

theorem wtab_scan : ∀ k, tabScan kernel (wIvs k) (wKeys k) wPost wSpecB = true
  | .a => wtab_scan_a
  | .p => wtab_scan_p
  | .b => wtab_scan_b

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
