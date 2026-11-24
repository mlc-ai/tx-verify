-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WkWarpBar
public import Kernels.InklingRelDecode.Proof.Protocol.WkLdBlock

@[expose] public section

/-!
# What the progress layer takes of the KV ring's loader side (`Wk*`)

`Interface/WkWarpBar.lean`: the kernel's warp barriers by role, with the full mask.
`Protocol/WkLdCount.lean`, `WkLdRdv.lean`, `WkLdEnd.lean`, `WkLdBlock.lean`: the loader's warp
barriers by state, the rendezvous of every loader lane with lane 0, the loader's polls at the end
of its trace, `kv_empty` as a commit object with the reuse paths of every loader lane, and the
blocker of a loader lane's poll (`Wk.loader_empty_blocked`).
-/
