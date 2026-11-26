-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 0, 4 of them. -/
def raw0 : List Statement := (source.body.drop 0).take 4

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved0 : List Statement := FlashKdaFwd_resolved_part% 0 4

theorem resolved_0 :
    resolveScopePart (resolveScopes rootFuel) raw0 rootBindings "" 0 =
      .ok resolved0 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
