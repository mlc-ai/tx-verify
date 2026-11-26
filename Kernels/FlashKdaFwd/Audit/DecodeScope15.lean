-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 326, 502 of them. -/
def raw15 : List Statement := (source.body.drop 326).take 502

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved15 : List Statement := FlashKdaFwd_resolved_part% 326 502

theorem resolved_15 :
    resolveScopePart (resolveScopes rootFuel) raw15 rootBindings "" 326 =
      .ok resolved15 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
