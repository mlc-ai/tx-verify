-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved16 : List Statement := tml_resolved_part% 7325 506

theorem resolved_16 :
    resolveScopePart (resolveScopes rootFuel) raw16 rootBindings "" 7325 =
      .ok resolved16 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
