-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 1421, 23 of them. -/
def raw19 : List Statement := (source.body.drop 1421).take 23

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved19 : List Statement := FlashKdaFwd_resolved_part% 1421 23

theorem resolved_19 :
    resolveScopePart (resolveScopes rootFuel) raw19 rootBindings "" 1421 =
      .ok resolved19 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
