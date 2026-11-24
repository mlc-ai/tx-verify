-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingFreePhase
import Lemmas.Protocol.MbarInit

@[expose] public section

/-! # A reuse phase without TMA forces repeated WG0 participation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
