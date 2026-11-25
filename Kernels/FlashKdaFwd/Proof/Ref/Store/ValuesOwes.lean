-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Ends
public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.ValuesEndsRef

@[expose] public section

/-! # What the Store phase owes the assembly of the value-ends contracts

`Ref/Assembly/ValuesEndsRef.lean` proves the value layer's contracts for the stretches around
the tile loop (`StoreRef`, `StoreCtl`, …) for a whole execution, and states what it needs of the
Store phase as the structure `ValuesEnds.StoreOwes P L X` (five fields about the store path of
a partial last tile: the element stores, the twelve events of a chunk, the element reads, and
two facts that tell the phase's accesses and tensor stores from those of other phases). This
file proves the structure from the precondition and consistency:

    theorem storeOwes (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
        Assembly.ValuesEnds.StoreOwes P L X

Each field is a theorem of `Ends.lean` (`storeCtl_elem`, `owes_chunk`, `owes_reads`,
`owes_acc_free`, `owes_ts_out`), stated there without the assembly's vocabulary; here
`readIdx_eq` identifies the assembly's index of a read site (`ValuesEnds.readIdx`) with
`Ends.lean: rdIdx`, and the assembly's `StoreWeak` (the state is at a position with its register
facts, or it is the exit state) and `NoUb X g k` (no undefined-behaviour event among the first
`k` events of the thread) unfold to the hypotheses of `owes_chunk`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The assembly's index of an element-read site is `rdIdx`. -/
theorem readIdx_eq (s : Site) : Assembly.ValuesEnds.readIdx s = rdIdx s := by
  cases s <;> rfl

/-- **What the Store phase owes the assembly of the value-ends contracts**
(`Ref/Assembly/ValuesEndsRef.lean`), from the precondition and consistency. -/
theorem storeOwes (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    Assembly.ValuesEnds.StoreOwes P L X where
  elem := fun _ _ _ _ _ i hg hen hk0 hσ hI hs he =>
    storeCtl_elem hpre hX hg i hen hk0 hσ hI hs he
  chunk := fun _ _ _ _ hg hen hk0 hk hσ hW hinv hs =>
    owes_chunk hpre hX hg hen hk0 hk hσ hW hinv hs
  reads := fun _ _ _ s _ _ hg hen hk0 hσ hI hm he =>
    owes_reads hpre hX hg hen hk0 hσ hI ((readIdx_eq s.site).symm.trans hm) he
  acc_free := fun _ _ _ _ _ _ _ hg hσ hI hacc hcov => owes_acc_free hpre hX hg hσ hI hacc hcov
  ts_out := fun _ _ _ _ _ _ _ _ _ _ hg hσ hI he hwl => owes_ts_out hpre hX hg hσ hI he hwl

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
