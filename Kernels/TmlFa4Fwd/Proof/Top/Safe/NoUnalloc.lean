-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Alloc
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.CopySource

@[expose] public section

/-! # ERR-UNALLOCATED-ACCESS: every access is to allocated memory

`Safe.noUnalloc` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-UNALLOCATED-ACCESS**: every access lies in a launched CTA's
shared window, its lane's local memory, or a tensor of the launch (`no_unalloc`, `cpSrc`). -/
theorem Safe.noUnalloc (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ Unalloc m X :=
  no_unalloc hp hX (launchFollow hp hX) (cpSrc hp hX (launchFollow hp hX))

end PTX.Kernels.TmlFa4Fwd.Proof.Top
