-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.PlNoNc

/-!
# Placement of the accesses: umbrella of the safety layer

* `PlNoNc`: the kernel has no non-coherent load (`no_nc`).

The placement theorems that need the protocol layer's footprints are in `Protocol/PlAll.lean`
(`Proof2/Lib/MmaFoot.lean`, `Proof2/Safety/Placed.lean`): the safety layer may not import the
protocols.
-/
