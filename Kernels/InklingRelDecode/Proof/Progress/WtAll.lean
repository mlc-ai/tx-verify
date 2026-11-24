-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtTime
public import Kernels.InklingRelDecode.Proof.Progress.WtMono
public import Kernels.InklingRelDecode.Proof.Progress.WtOrder
public import Kernels.InklingRelDecode.Proof.Progress.WtAfter
public import Kernels.InklingRelDecode.Proof.Progress.WtBar0
public import Kernels.InklingRelDecode.Proof.Progress.WtReg

@[expose] public section

/-!
# The progress layer's virtual time and the facts proved about it (umbrella)

The design is in the development notes, "Progress layer: the virtual time". The modules:

* `WtTime.lean`: the timeline and `Wt.time`; every time is at least 2 (`wait_time`).
* `WtMonoSm.lean`, `WtMonoRoles.lean`, `WtMono.lean`: the time rises along every counted step of
  every machine (`smT_lt`, `loaderT_lt`, `mmaT_lt`, `epiT_lt`, `dstartT_lt`, `workerT_lt`,
  `idleT_lt`, and the composed `dcompT_lt`, `wcompT_lt`).
* `WtAfter.lean`: the three `after` clauses (`reg_after`, `bar_after`, `tc_after`).
* `WtOrder.lean`: the band lemmas and the wait table (every producer of a poll is earlier).
* `WtBar0One.lean`, `WtBar0Lock.lean`, `WtBar0.lean`: `Bar0Facts.one`, `Bar0Facts.lock`
  (`bar0_one`, `bar0_lock`) and `bar0Facts_of`.
* `WtReg.lean`: `RegWaitFacts.exit` (`reg_exit`).
-/
