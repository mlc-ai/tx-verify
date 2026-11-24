-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinatePoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingWaitInitialization

@[expose] public section

/-! # Checked history of the actual TMA coordinate acquire -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
