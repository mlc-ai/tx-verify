-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Audit.DecodeScopeSetup
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.DecodeAudit

open PTX PTX.Decode PTX.Syntax

set_option maxRecDepth 100000

def resolved18 : List Statement := tml_resolved_part% 8331 500

theorem resolved_18 :
    resolveScopePart (resolveScopes rootFuel) raw18 rootBindings "" 8331 =
      .ok resolved18 := by
  kernel_rfl

end PTX.Kernels.TmlFa4Fwd.DecodeAudit
