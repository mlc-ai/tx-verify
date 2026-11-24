-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.WmBlock
public import Kernels.InklingRelDecode.Proof.Protocol.WmLdCount

@[expose] public section

/-!
# The MMA warp's `kv_ready` poll, protocol part (`Wm*`)

`WmMmaCount.lean`: the MMA lane's warp barriers by state. `WmAhead.lean`: no lane of the MMA
warp commits a block its warp has not polled. `WmPhase.lean`: the final phase of `kv_ready` is
the polling lane's polls. `WmBlock.lean`: the premises of `MbarRing.Blocker.tx_short` and the
short producer. `WmLdCount.lean`: the loader's arrivals, copies and elections at a state up to the
end of its trace.
-/
