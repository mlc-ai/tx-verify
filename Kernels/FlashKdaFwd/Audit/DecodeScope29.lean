-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 3012, 509 of them. -/
def raw29 : List Statement := (source.body.drop 3012).take 509

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved29 : List Statement := FlashKdaFwd_resolved_part% 3012 509

theorem resolved_29 :
    resolveScopePart (resolveScopes rootFuel) raw29 rootBindings "" 3012 =
      .ok resolved29 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
