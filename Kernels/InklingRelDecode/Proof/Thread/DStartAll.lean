-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DStartEv
public import Kernels.InklingRelDecode.Proof.Thread.DStartHandoff

/-! # The default partition's common start: umbrella

The common start of every thread (pc 0 to 27) for the threads of the default partition
(warps 0 to 3), as one site machine linked to the prologue `ProA`:

* `DStartBase`: the sites (`alloc`, `allocWr`, `bar0`, `ld0`, `bar1`, `relinq`, `shfl`,
  `toProA`), the states, the facts, the invariant and the abstract successor `next`;
* `DStartStep`, `DStartStepB`, `DStartStepC`: the steps (the last one runs the local code after
  the shuffle through `ProA.entry`);
* `DStartSound`: `stepAt` and the code machine `DStart.code`; `DStartStart`: the code from the
  launch state, `start`, `sound`, `machine_sound`;
* `DStartEv`: the event shapes (`Fired`, `Shape`, `shape`);
* `DStartHandoff`: the link to `ProA.entry` (`handoff20`, `handoff27`) and to `ProA.code`
  (`good_toProA`, `reach_toProA`), and the inherited registers `inh`. -/
