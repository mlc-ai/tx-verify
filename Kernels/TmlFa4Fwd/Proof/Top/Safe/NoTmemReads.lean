-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs

@[expose] public section

/-! # ERR-TMEM-RACE (an MMA read unordered with a write of its cell): an MMA read is ordered with
every write of its cells

`Safe.noTmemReads` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-TMEM-RACE** (an MMA read and a write), by the orders of the Tensor Memory accesses
from the hand-offs of the S, P and O channels (`Tm.handoffs`). -/
theorem Safe.noTmemReads (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TcMma.ReadsUnsafe l X :=
  have hF := launchFollow hp hX
  Tm.reads_safe hp (Tm.scoreFacts hp hX hF) (Tm.oAccFacts hp hX hF) (Tm.handoffs hp hX hF)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
