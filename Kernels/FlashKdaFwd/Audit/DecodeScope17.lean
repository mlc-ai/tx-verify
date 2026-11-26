-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 1340, 80 of them. -/
def raw17 : List Statement := (source.body.drop 1340).take 80

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved17 : List Statement := FlashKdaFwd_resolved_part% 1340 80

theorem resolved_17 :
    resolveScopePart (resolveScopes rootFuel) raw17 rootBindings "" 1340 =
      .ok resolved17 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
