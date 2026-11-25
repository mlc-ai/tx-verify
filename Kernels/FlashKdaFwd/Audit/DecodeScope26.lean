-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 2628, 382 of them. -/
def raw26 : List Statement := (source.body.drop 2628).take 382

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved26 : List Statement := FlashKdaFwd_resolved_part% 2628 382

theorem resolved_26 :
    resolveScopePart (resolveScopes rootFuel) raw26 rootBindings "" 2628 =
      .ok resolved26 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
