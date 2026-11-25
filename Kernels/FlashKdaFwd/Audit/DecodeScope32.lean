-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

/-- The statements of the body from index 3797, 58 of them. -/
def raw32 : List Statement := (source.body.drop 3797).take 58

/-- What they resolve to, as the compiled decoder evaluates it. -/
def resolved32 : List Statement := FlashKdaFwd_resolved_part% 3797 58

theorem resolved_32 :
    resolveScopePart (resolveScopes rootFuel) raw32 rootBindings "" 3797 =
      .ok resolved32 := by
  kernel_rfl

end PTX.Kernels.FlashKdaFwd.DecodeAudit
