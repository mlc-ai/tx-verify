-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 2128, 500 of them. -/
def raw25 : List Statement := (source.body.drop 2128).take 500

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved25 : List Statement := FlashKdaFwd_resolved_part% 2128 500

theorem resolved_25 :
    resolveScopePart (resolveScopes rootFuel) raw25 rootBindings "" 2128 =
      .ok resolved25 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
