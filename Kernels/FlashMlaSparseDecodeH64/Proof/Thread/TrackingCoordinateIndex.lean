-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexCoordinateTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingTensorEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1IndexRendezvous
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds

@[expose] public section

/-! # Identify a covering store on the index warp without global tracking -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
