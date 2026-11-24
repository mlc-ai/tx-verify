-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs

@[expose] public section

/-! # ERR-TMEM-RACE (two unordered writes of a cell): two writes of a Tensor Memory cell are ordered

`Safe.noTmemWrites` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-TMEM-RACE** (two writes of a cell), by the orders of the Tensor Memory accesses
from the hand-offs of the S, P and O channels (`Tm.handoffs`). -/
theorem Safe.noTmemWrites (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TcMma.WritesUnsafe l X :=
  have hF := launchFollow hp hX
  Tm.writes_safe hp (Tm.scoreFacts hp hX hF) (Tm.oAccFacts hp hX hF) (Tm.handoffs hp hX hF)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
