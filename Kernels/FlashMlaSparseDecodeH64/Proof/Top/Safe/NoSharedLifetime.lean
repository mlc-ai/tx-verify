-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Use
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Store
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Loads
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Commit

@[expose] public section

/-! # ERR-SHARED-LIFETIME: shared memory outlives its asynchronous uses

The safety class of Core's `Unsafe` this file owns (`SharedLifetimeUnsafe`), by
`Life.no_sharedLifetime` (`Protocol/Life/Use.lean`): every use of shared memory is of the issuing
lane's CTA (`Life.life_own`), a thread's instruction precedes its lane's exit, and an asynchronous
use finishes before an exit of its exited CTA when its operation does:

* a tensor store's source reads (`Life.life_store`: the assumption `storeDrain`);
* an MMA or copy (`Life.life_mma`: the last `svDone` commit, which warpgroup 0's poll at pc 1184
  observes);
* a tensor load's arrival (`Life.life_loads`: a gather's by the dequant lanes' polls of `rawReady`,
  a query load's by the MMA lane's poll of `qTma`);
* a commit's arrival (`Life.life_commit`: the query copy's and the QK commits' by the polls of the
  exited CTA's lanes, the PV commits' by warpgroup 0's poll at pc 1184 and, for an earlier block,
  by the assumption `commitOrder`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-SHARED-LIFETIME**: shared memory outlives its asynchronous uses. -/
theorem Safe.noSharedLifetime (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  Life.no_sharedLifetime hp hX hFw (hIn.mbar hp X hX hFw)
    (Life.life_loads hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
      (hIn.bar0 hp X hX hFw) (hIn.raw hp X hX hFw))
    (Life.life_mma hp hX hFw (hIn.bar hp X hX hFw) (hIn.mbar hp X hX hFw)
      (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw))
    (Life.life_commit hp hX hFw (hIn.bar hp X hX hFw) (hIn.mbar hp X hX hFw)
      (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw))
    (Life.life_store hp hX hFw hnu)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
