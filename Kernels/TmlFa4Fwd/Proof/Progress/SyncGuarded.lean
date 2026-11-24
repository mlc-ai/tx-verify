-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderEmptyFaults
import Kernels.TmlFa4Fwd.Proof.LoaderArrivalSites
import Kernels.TmlFa4Fwd.Proof.MbarSafety
public import Kernels.TmlFa4Fwd.Proof.Safety.Mbar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.AsyncCopy PTX.MBarrier
open Thread.Loader (readyObject)
open Thread.Mma.Observation (emptyObject)

/-- The actual synchronization is guarded when the launch offsets are preserved. -/
theorem syncGuarded {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) :
    SyncGuarded l kernel X :=
  guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)

end PTX.Kernels.TmlFa4Fwd.Progress
