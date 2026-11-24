-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Assumptions

@[expose] public section

/-!
# Audit: `tcgen05.ld` data flow, part 0b1

Each check evaluates the decoded program. The assumptions do not depend on these theorems: each
constructor applies only at its listed sites (and `tcLdDataflowAt` only where `ldConsumedAt`
holds); the checks confirm that the lists name the instructions `DECISIONS.md` describes.
-/

namespace PTX.Kernels.FlashAttn4Fwd.Assumptions
open PTX

/-- The listed loads pass the data-flow check of `tcLdDataflowAt`. -/
theorem tcLdSites_consumed_0b1 :
    [1317].all
      (Assumption.ldConsumedAt kernel) = true := by
  decide +kernel

end PTX.Kernels.FlashAttn4Fwd.Assumptions
