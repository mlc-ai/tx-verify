-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RdLayer
public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg
public import Kernels.InklingRelDecode.Proof.Result.RdSLoad
public import Kernels.InklingRelDecode.Proof.Result.RdOLoad

@[expose] public section

/-!
# The read sources of the S load and of the rescale load: umbrella

* `RdSLoad`: `Rd.sLoadSrc_of : Sv.SLoadSrc Q L X` (premises `SRdv`, `SPstAfter`, `SoftAll`, the
  handshake's, `RoleReads`, `SmBaseZero`, the MMA warp's words);
* `RdOLoad`: `Rd.oLoadSrc_of : Rs.OLoadSrc Q L X` (premises `ORdv`, `SoftAll`, the same).

Not imported by `Result/OutAll.lean`, `RsAll.lean`, `SvAll.lean`, `SwAll.lean`.
-/
