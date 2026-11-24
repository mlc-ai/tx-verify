-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingProducerReuse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCommitOrigins

@[expose] public section

/-! # Classifying the actual reuse phase observed by the index producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
