-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoTmemInstruction
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Sources

@[expose] public section

/-! # ERR-TMEM-READ-SOURCE: every Tensor Memory read has its source

`Safe.noTmemSource` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-TMEM-READ-SOURCE** from the open part of ERR-TC-MMA: the read sources are proved
(`Tm.source_safe`). -/
theorem Safe.noTmemSource (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TcMma.SourceUnsafe l Assumptions.all X :=
  fun h => h (Tm.source_safe hp hX (launchFollow hp hX) (Safe.mmaValues hp hX))

end PTX.Kernels.TmlFa4Fwd.Proof.Top
