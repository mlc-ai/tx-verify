-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Reg
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Tc
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Tmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Cluster
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Bar

@[expose] public section

/-! # What the thread layer exports for the progress at the collective waits

A pending thread whose last event is a collective operation that has not returned waits for the
lanes that have not reached it (or, for a paired Tensor Memory operation, for the allocators).
The progress layer ranks a thread by the time of its machine state (`stateTime`); the facts
here place the lanes a blocked thread waits for no later than the operation, and the blocked
thread's state after the operation later than it. One structure per collective:

* `RegWaitFacts`: the register requests (`setmaxnreg`, at `regT`);
* `TcWaitFacts`: the warp-collective `tcgen05` events (a lane's `k`-th is at one site, item and
  trip across its warp);
* `TmemWaitFacts`: the paired Tensor Memory operations of warp 12 of the two CTAs of a cluster;
* `ClusterWaitFacts`: the prologue's cluster-barrier arrival and wait;
* `BarWaitFacts`: the named barriers (barrier 2's two generations and the statistics barriers).

Each is a fact of single threads' events and machine states, from the roles' run invariants and
the site tables of `Thread/Roles.lean`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The thread layer's facts for the progress at the collective waits. -/
structure ProgressWaitFacts (L : Launch) (X : Execution) : Prop where
  reg : RegWaitFacts L X
  tc : TcWaitFacts L X
  tmem : TmemWaitFacts L X
  cluster : ClusterWaitFacts L X
  bar : BarWaitFacts L X

end
end PTX.Kernels.FlashAttn4Fwd.Proof
