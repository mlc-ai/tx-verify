-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved13 : List Statement := tml_resolved_part% 5939 464

theorem resolved_13 :
    resolveScopePart (resolveScopes rootFuel) raw13 rootBindings "" 5939 =
      .ok resolved13 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
