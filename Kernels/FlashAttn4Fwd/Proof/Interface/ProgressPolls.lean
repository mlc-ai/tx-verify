-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Loader
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.MmaRing
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.PReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.P2
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Handshake
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.SFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Credit
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.OFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Free
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Staged
public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2

@[expose] public section

/-! # What the thread layer exports for the progress at the mbarrier polls

A released thread whose next event is an mbarrier poll waits for the producers of the polled
object. One structure per wait class (in the shapes of `ProgressPolls/Base.lean`: the waiter
`PollsOn` its object, and a producer that has made no more producing events than the waiter's
poll needs `Lags` it):

* `LoaderPollFacts`: the loader's Q and KV empty waits and its tail drain;
* `MmaRingPollFacts`: the MMA warp's Q-full and KV-full waits;
* `PReadyPollFacts`, `P2PollFacts`: the MMA warp's P-ready waits on the two P-ready objects;
* `HandshakePollFacts`: the MMA warp's deallocation handshake (`+320`);
* `SFullPollFacts`, `CreditPollFacts`: the softmax S-full and statistics credit waits;
* `OFullPollFacts`, `FreePollFacts`: the correction's O-full and staging-free waits;
* `StagedPollFacts`: the store warp's staged waits.

Each is a fact of single threads' runs, from the roles' run invariants and the site tables of
`Thread/Roles.lean`. `PollInputs` collects the thread layer's existing exports the blocker exports
of the Tensor Memory objects and of the statistics credit read (the routes' facts and the older
facts, as the safety glue reads them). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX

noncomputable section

/-- The thread layer's facts for the progress at the mbarrier polls. -/
structure ProgressPolls (L : Launch) (X : Execution) : Prop where
  loader : LoaderPollFacts L X
  mmaRing : MmaRingPollFacts L X
  pReady : PReadyPollFacts L X
  p2 : P2PollFacts L X
  handshake : HandshakePollFacts L X
  sFull : SFullPollFacts L X
  credit : CreditPollFacts L X
  oFull : OFullPollFacts L X
  free : FreePollFacts L X
  staged : StagedPollFacts L X

/-- The thread layer's existing exports the poll blockers read: the facts of the reuse routes
through the P-ready, second P-ready, S-full and O-full objects (`Score.RouteCtx`) and the older
facts (`Stats.softArrives`). -/
structure PollInputs (P : Params) (L : Launch) (X : Execution) : Prop where
  route : RouteFacts L X
  pready : PReadyFacts L X
  p2 : P2Facts L X
  sfull : SFullFacts L X
  ofull : OFullFacts L X
  older : OlderFacts P L X

end
end PTX.Kernels.FlashAttn4Fwd.Proof
