-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WmAll

@[expose] public section

/-!
# The MMA warp's `kv_ready` poll for the layers above (`Wm*`)

The protocol part (`Protocol/WmAll.lean`) as the progress layer sees it.
-/
