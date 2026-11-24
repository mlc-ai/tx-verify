-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WxLag0
public import Kernels.InklingRelDecode.Proof.Progress.WxTcLag
public import Kernels.InklingRelDecode.Proof.Progress.WxAsync

@[expose] public section

/-!
# The count-to-time facts of `Remaining` (umbrella)

The facts of `Progress.Remaining` that compare a lane's time with the time of a blocked state by
the counts of the CTA's or the warp's events (the development notes, "Progress layer: counts and
times
(`Wx*`)"):

* `WxSmOrder.lean`, `WxProOrder.lean`: the barrier-0 count of a softmax state and of a prologue
  state, as a function of the state, orders the states in time;
* `WxLag0.lean`: `BarTime.lag0l` (`lag0l_of`);
* `WxTcCount.lean`: the warp-collective `tcgen05` events before a default-partition state
  (`tc_inv`); `WxTcOrder.lean`: that count orders the states of each region in time;
* `WxTcLag.lean`: `TcWaitFacts.lag` (`tcLag_of`);
* `WxAsync.lean`: `TcMma.ATmemApart` and `TcMma.LayoutInjective` from the two MMA shapes
  (`aTmemApart_of`, `layoutInjective_of`).
-/
