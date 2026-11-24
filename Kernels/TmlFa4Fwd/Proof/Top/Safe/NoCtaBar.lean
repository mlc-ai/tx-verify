-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.NoCtaBar

@[expose] public section

/-! # ERR-CTA-BARRIER: no named barrier is arrived on twice in one generation

From the credit channel (`Protocol/Credit/NoCtaBar.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-CTA-BARRIER.** -/
theorem Safe.noCtaBar (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) : ¬ CtaBarFault l X :=
  Proof.noCtaBar hp hX (launchFollow hp hX)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
