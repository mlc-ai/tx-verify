-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved1 : List Statement := tml_resolved_part% 512 476

theorem resolved_1 :
    resolveScopePart (resolveScopes rootFuel) raw1 rootBindings "" 512 =
      .ok resolved1 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
