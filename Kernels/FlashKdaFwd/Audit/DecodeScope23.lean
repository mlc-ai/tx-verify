-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 1897, 230 of them. -/
def raw23 : List Statement := (source.body.drop 1897).take 230

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved23 : List Statement := FlashKdaFwd_resolved_part% 1897 230

theorem resolved_23 :
    resolveScopePart (resolveScopes rootFuel) raw23 rootBindings "" 1897 =
      .ok resolved23 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
