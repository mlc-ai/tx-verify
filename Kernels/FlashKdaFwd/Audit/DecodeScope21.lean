-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 1445, 451 of them. -/
def raw21 : List Statement := (source.body.drop 1445).take 451

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved21 : List Statement := FlashKdaFwd_resolved_part% 1445 451

theorem resolved_21 :
    resolveScopePart (resolveScopes rootFuel) raw21 rootBindings "" 1445 =
      .ok resolved21 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
