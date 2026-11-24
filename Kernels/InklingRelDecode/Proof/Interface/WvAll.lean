-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WvAnchor
public import Kernels.InklingRelDecode.Proof.Interface.WvArr
public import Kernels.InklingRelDecode.Proof.Protocol.LpObs

@[expose] public section

/-!
# The worker machines' counts at the end of a trace (`Wv*`, interface half)

* `WvAnchor`: the MMA lane's anchored run, polls and commits at an index up to the trace's end
  (`mma_anchor_le`, `mma_polls_le`, `mma_commits_le`).
* `WvArr`: thread 0's arrivals on `p_ready` at an epilogue state (`arr_epi`), and the iteration of
  an MMA state at `pWait` (`mma_pWait_iter`).
* `Lp.numIters_le24` (from `LpObs`) for the layers above.
-/
