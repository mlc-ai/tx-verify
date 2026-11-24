-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WkPolls

@[expose] public section

/-!
# The KV ring's polls and the warp barriers (`Wk*`)

`Interface/WkWarpBar.lean`: the kernel's warp barriers by role, with the full mask.
`Protocol/WkLdCount.lean`, `WkLdRdv.lean`, `WkLdEnd.lean`, `WkLdBlock.lean`: the loader's warp
barriers by state, the rendezvous of every loader lane with lane 0, the loader's polls at the end
of its trace, `kv_empty` as a commit object with the reuse paths of every loader lane, and the
blocker of a loader lane's poll. `Progress/WkLdLag.lean`, `WkPolls.lean`: the committing MMA
lane's lag, and `Wy.WorkerPollsRest` from the MMA warp's half (`MmaKvPollsRest`).
-/
