-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.MemOrdered

@[expose] public section

/-! # ERR-MIXED-SIZE: overlapping accesses of different sizes are ordered

`Safe.noMixed` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-MIXED-SIZE**: shared and local memory are ordered, and the global writes are LSE words and
single O bytes, which nothing reads (`no_mixed`). -/
theorem Safe.noMixed (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) : ¬ Mixed l X :=
  no_mixed hp hX (launchFollow hp hX)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
