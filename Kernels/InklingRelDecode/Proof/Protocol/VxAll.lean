-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.VxLane
public import Kernels.InklingRelDecode.Proof.Protocol.VxLife

@[expose] public section

/-!
# The open handshake facts proved from the threads' states: umbrella

`VxElect` (the MMA warp's count of elections from the entry of its role, the states at the
election positions), `VxLane` (`Mbar.Route.lane_commit`, `Hs.PkgRest`), `VxLife` (the exit
generation of barrier 0, `Hs.TmemLifeRest`, `SO.TmemLife`).
-/
