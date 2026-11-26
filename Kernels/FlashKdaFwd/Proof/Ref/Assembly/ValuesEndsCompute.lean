-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ValuesEndsRef
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocol

@[expose] public section

/-!
# What the Compute phase owed to the values at the ends of the tile loop

`ValuesEndsRef.lean` states two facts about the tile loop of the compute threads as the
structure `ValuesEnds.ComputeOwes P L X`:

* `wr_shared`: a write of the tile loop is to shared memory (it is the row write of an
  `stmatrix`);
* `acc_row`: an access of the tile loop that covers a byte of the bfloat16 state copy
  (`state_acc`, window offsets 0 to 32767 of a block) is an access of a whole row: 16 bytes at
  a multiple of 16 from `shared_mem`.

The Compute phase proves both in `Ref/Compute/ExportsProtocol.lean`
(`Compute.Proto.owes_ends_wr_shared`, `Compute.Proto.owes_ends_acc_row`, in the fields' exact
shapes). `ValuesEnds.computeOwes` is the structure, from the precondition and consistency.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX
open PTX.Kernels.FlashKdaFwd

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **What the Compute phase owed to the values at the ends of the tile loop**, from the
precondition and consistency. -/
theorem ValuesEnds.computeOwes (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) : ValuesEnds.ComputeOwes P L X where
  wr_shared := Compute.Proto.owes_ends_wr_shared hpre hX
  acc_row := Compute.Proto.owes_ends_acc_row hpre hX

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
