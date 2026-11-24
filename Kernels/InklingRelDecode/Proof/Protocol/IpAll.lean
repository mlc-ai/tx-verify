-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpLifeAll
public import Kernels.InklingRelDecode.Proof.Protocol.IpTmAll
public import Kernels.InklingRelDecode.Proof.Protocol.IpMmaAll

/-!
# The protocol layer's statements for the Inkling kernel's open fields: umbrella

* `IpLife*`: `Safety.Protocol.lifetime` (every shared use completes before an exit of its CTA);
* `IpTm*`: `Tmem1Ops`, `Tmem1Facts`, `AllocWordZero`, `Rs.SmBaseZero` and the program-side premises
  of `tcInstr`.

* `IpMma*`: `Life.NextCommit`, the MMA thread of a CTA (the non-`SO.Facts` part of
  `Tmem1.OFinalFacts`) and the epilogue's `o_final` poll before every deallocation (`hpoll`).

None of these modules is imported by `Protocol/All.lean`.
-/
