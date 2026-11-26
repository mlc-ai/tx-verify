-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 16, 309 of them. -/
def raw13 : List Statement := (source.body.drop 16).take 309

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved13 : List Statement := FlashKdaFwd_resolved_part% 16 309

theorem resolved_13 :
    resolveScopePart (resolveScopes rootFuel) raw13 rootBindings "" 16 =
      .ok resolved13 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
