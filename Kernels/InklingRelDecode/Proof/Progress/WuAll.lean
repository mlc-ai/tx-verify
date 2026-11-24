-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuEnd
public import Kernels.InklingRelDecode.Proof.Progress.WuLate
public import Kernels.InklingRelDecode.Proof.Progress.WuCap
public import Kernels.InklingRelDecode.Proof.Progress.WuEpoch
public import Kernels.InklingRelDecode.Proof.Progress.WuReg
public import Kernels.InklingRelDecode.Proof.Progress.WuBar1
public import Kernels.InklingRelDecode.Proof.Progress.WuBar0e
public import Kernels.InklingRelDecode.Proof.Progress.WuBar0f
public import Kernels.InklingRelDecode.Proof.Progress.WuPost

@[expose] public section

/-!
# The epoch facts of the virtual time (umbrella)

The facts of `Remaining` that compare a lane's time with the time of a blocked thread by counts of
events (the development notes, "Progress layer: the epoch tables"):

* `WuEnd.lean`: where a thread without an exit is now (`end_cases`).
* `WuLate.lean`: the round marker of the dispatch loop agrees with the count of requests
  (`late_inv`).
* `WuCap.lean`, `WuEpoch.lean`: the time of a state is capped by the counts of requests and of
  barrier-1 events before it (`Tbl`, `tbl_at`).
* `WuReg.lean`: `RegWaitFacts.before` (`reg_before`), and the bounds on `Sched.threadTime` by the
  counts (`threadTime_rq_le`, `threadTime_b1_le`).
* `WuBar1.lean`, `WuBar0e.lean`, `WuBar0f.lean`, `WuPost.lean`: `BarTime.lag1`, `lag0e`, `lag0f`
  (`bar_lag1`, `bar_lag0e`, `bar_lag0f`).
-/
