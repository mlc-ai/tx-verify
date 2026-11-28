-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Order

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- The use of slot `S` that a tensor copy's write is of. -/
noncomputable def copyUseOf (X : Execution) (S : SingleTmaRing.Slot) : AsyncCopy.Ref → Nat
  | .thread _ => 0
  | .async e _ => SingleTmaRing.copyUse X S e

/-- The use of slot `S` that an MMA operand read is of. -/
noncomputable def readUseOf (X : Execution) (S : SingleTmaRing.Slot) : AsyncCopy.Ref → Nat
  | .thread _ => 0
  | .async e _ => SingleTmaRing.readUse X S e

end PTX.Kernels.InklingRelDecode.Proof.Lib
