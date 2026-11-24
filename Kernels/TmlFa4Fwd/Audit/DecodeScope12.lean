-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved12 : List Statement := tml_resolved_part% 5487 452

theorem resolved_12 :
    resolveScopePart (resolveScopes rootFuel) raw12 rootBindings "" 5487 =
      .ok resolved12 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
