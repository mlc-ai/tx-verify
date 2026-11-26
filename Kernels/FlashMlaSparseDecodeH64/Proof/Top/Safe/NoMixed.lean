-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoRace
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Global

@[expose] public section

/-! # ERR-MIXED-SIZE: no mixed-size conflicting accesses

The safety class of Core's `Unsafe` this file owns (`Mixed`). It needs no fact of its own: the
regions' and the outside bytes' orders that ERR-DATA-RACE takes (`Safe.NoRace.regions`) order every
conflict, so none is of mixed size (`no_mixed`, `Protocol/Shared/Ordered.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-MIXED-SIZE**: no mixed-size conflicting accesses. -/
theorem Safe.noMixed (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ Mixed L X :=
  no_mixed hp hX hFw (Safe.NoRace.regions hp hIn hX hFw hnu) (global_ordered hp hX hFw hnu)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
