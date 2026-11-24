-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WorkerHandoff

@[expose] public section

/-!
# The inherited Tensor Memory base word

The worker reads the word `tcgen05.alloc` stored at `global_smem` into the register `%r2` (pc 13)
and the roles inherit it unchanged in `Loader.Pro.rest`. `Pro.baseWord` names that register, so
that the interface layer states the invariant "the inherited base word is the zero word" without
a register id, and `handoff_baseWord` says the hand-off to a role keeps it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The inherited Tensor Memory base word, the register `%r2`. -/
def Loader.Pro.baseWord (P : Loader.Pro) : Value := P.rest 463

/-- The hand-off keeps the inherited base word. -/
theorem Worker.handoff_baseWord (L : Launch) (g : Nat) (P : Loader.Pro) :
    (Worker.handoff L g P).baseWord = P.baseWord := by
  simp [Loader.Pro.baseWord, Worker.handoff, Worker.valueOf, Worker.own, Loader.Pro.val,
    Loader.Pro.table, PTX.Flow.lookupLit]

end
end PTX.Kernels.InklingRelDecode.Proof
