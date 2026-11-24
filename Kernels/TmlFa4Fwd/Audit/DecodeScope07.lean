-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved7 : List Statement := tml_resolved_part% 2963 494

theorem resolved_7 :
    resolveScopePart (resolveScopes rootFuel) raw7 rootBindings "" 2963 =
      .ok resolved7 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
