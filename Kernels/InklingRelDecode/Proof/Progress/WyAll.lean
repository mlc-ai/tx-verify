-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WyPolls
public import Kernels.InklingRelDecode.Proof.Progress.WySoft

@[expose] public section

/-!
# The polls and the warp collectives (`Wy*`)

* `WyNext`: the next event of a released pending thread at a poll is the poll of the object and
  parity `PollAt` names (`poll_next`).
* `WyState`: the polled object has a final state (`pollAt_final`).
* `WyPolls`: `PollsBlocked` from the blocker clause `PollsRest` (`pollsBlocked_of`).
* `WySoft`: `PollsRest` from the lag of the committing MMA lane (`CmLag`) and the workers' blocker
  clause (`WorkerPollsRest`): the default partition's polls of `s_ready`, `o_done`, `o_final` are
  blocked by that lane or by an undelivered commit (`pollsRest_of`).
-/
