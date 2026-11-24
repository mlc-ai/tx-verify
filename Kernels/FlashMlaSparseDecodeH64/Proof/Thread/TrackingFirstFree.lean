-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateWriter
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingObservedArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # No TMA slot release precedes its first coordinate read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy
open Protocol Protocol.IndexRing

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
