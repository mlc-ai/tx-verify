-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Bias
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Channels

@[expose] public section

/-! # ERR-SHARED-LIFETIME: asynchronous shared-memory accesses finish before their CTA exits

`Safe.noSharedLifetime` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-SHARED-LIFETIME**. -/
theorem Safe.noSharedLifetime (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ SharedLifetimeUnsafe l kernel Assumptions.all X :=
  Life.no_sharedLifetime hp hX (launchFollow hp hX)
    (Life.bias_loads_finished hp hX (launchFollow hp hX))

end PTX.Kernels.TmlFa4Fwd.Proof.Top
