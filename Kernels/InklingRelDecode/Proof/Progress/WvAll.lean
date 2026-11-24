-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WvAll
public import Kernels.InklingRelDecode.Proof.Progress.WvParity
public import Kernels.InklingRelDecode.Proof.Progress.WvP0Lag
public import Kernels.InklingRelDecode.Proof.Progress.WvCmLag

@[expose] public section

/-!
# The worker premises of the polls (`Wv*`)

* `WvParity`: `Wy.MmaParity` (`mmaParity_of`).
* `WvP0Lag`: `Wy.P0Lag` for `Wt.time` (`p0Lag_of`).
* `WvLate`, `WvLane`, `WvCm`, `WvCmLag`: `Wy.CmLag` for `Wt.time` (`cmLag_of`).
-/
