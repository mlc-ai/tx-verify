-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.WmAll
public import Kernels.InklingRelDecode.Proof.Progress.WmPolls

@[expose] public section

/-!
# The MMA warp's `kv_ready` poll (`Wm*`)

`Protocol/WmAll.lean`: the protocol part. `Progress/WmLag.lean`: a short producer lags the
polling lane. `Progress/WmPolls.lean`: `Wk.MmaKvPollsRest` from the premise for the preloaded
blocks (`MmaKvPreRest`).
-/
