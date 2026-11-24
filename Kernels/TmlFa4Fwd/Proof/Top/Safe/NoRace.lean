-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.OutOrdered

@[expose] public section

/-! # ERR-DATA-RACE: conflicting accesses are ordered

`Safe.noRace` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **ERR-DATA-RACE**: shared and local memory are ordered, and two output writes of a byte are
ordered or write one value (`out_ordered`). -/
theorem Safe.noRace (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) : ¬ Race l X :=
  no_race hp hX (launchFollow hp hX) (out_ordered hp hX (launchFollow hp hX))

end PTX.Kernels.TmlFa4Fwd.Proof.Top
