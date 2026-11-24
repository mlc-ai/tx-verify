-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved4 : List Statement := tml_resolved_part% 1953 326

theorem resolved_4 :
    resolveScopePart (resolveScopes rootFuel) raw4 rootBindings "" 1953 =
      .ok resolved4 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
