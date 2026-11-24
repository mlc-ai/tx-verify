-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved9 : List Statement := tml_resolved_part% 3969 512

theorem resolved_9 :
    resolveScopePart (resolveScopes rootFuel) raw9 rootBindings "" 3969 =
      .ok resolved9 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
