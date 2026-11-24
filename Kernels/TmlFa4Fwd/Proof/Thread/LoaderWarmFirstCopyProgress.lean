-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringCopyProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmFirstKeyLanePointer (p : Params) (l : Launch) (g batch lane : Nat) : Nat :=
  primingKRowPointer p batch ((assignedCoordinates p batch (g/l.block)).2/6)
    (warmFirstSlotRow p l g batch lane 0)

def warmFirstKeySource (p : Params) (l : Launch) (g batch lane : Nat) : Nat :=
  recurringSourceAddress (warmFirstKeyLanePointer p l g batch (pointerBroadcastLane lane))
    (warpLane l g lane%l.block)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
