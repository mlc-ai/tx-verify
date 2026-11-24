-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved8 : List Statement := tml_resolved_part% 3457 512

theorem resolved_8 :
    resolveScopePart (resolveScopes rootFuel) raw8 rootBindings "" 3457 =
      .ok resolved8 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
