-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 828, 512 of them. -/
def raw16 : List Statement := (source.body.drop 828).take 512

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved16 : List Statement := FlashKdaFwd_resolved_part% 828 512

theorem resolved_16 :
    resolveScopePart (resolveScopes rootFuel) raw16 rootBindings "" 828 =
      .ok resolved16 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
