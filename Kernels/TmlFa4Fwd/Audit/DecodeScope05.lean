-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved5 : List Statement := tml_resolved_part% 2279 184

theorem resolved_5 :
    resolveScopePart (resolveScopes rootFuel) raw5 rootBindings "" 2279 =
      .ok resolved5 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
