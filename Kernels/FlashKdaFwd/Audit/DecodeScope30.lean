-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 3521, 275 of them. -/
def raw30 : List Statement := (source.body.drop 3521).take 275

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved30 : List Statement := FlashKdaFwd_resolved_part% 3521 275

theorem resolved_30 :
    resolveScopePart (resolveScopes rootFuel) raw30 rootBindings "" 3521 =
      .ok resolved30 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
