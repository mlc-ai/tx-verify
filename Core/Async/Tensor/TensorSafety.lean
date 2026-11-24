-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorAllocation
public import Core.Async.Tensor.TensorReduce
public import Core.Assembly.SharedLifetime
public import Core.MBarrier.InitPublication

@[expose] public section

namespace PTX
noncomputable section

/-! ## ERR-TENSOR-FILL-VALUE — tensor load value adapters
Statement: A tensor load is unsafe when it writes a byte that has no scalar value.

Defs: TensorUnsafe

Source:
- DEP-TENSOR-LOAD-BYTES (represented fill values)

Direction: stricter

Applies: Two-dimensional global-to-shared tensor loads

Premises: Every produced content has a scalar byte adapter.

Effect: Safety rejection. The box alignment is checked when the instruction is issued
  (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS). The lifetimes of the destination and mbarrier
  CTAs are checked by ERR-SHARED-LIFETIME. The mbarrier of the load is an mbarrier operand
  (`UsesMbar`): its initialization is ERR-MBAR-UNINITIALIZED, its storage ERR-UNALLOCATED-ACCESS,
  and its exact initialization lifetime is checked by ObjectPublished when the completion
  notification enters the object history. An issue is distinct from its write or notification
  completion.
-/
/-- Some tensor load writes a byte without a scalar value. -/
def TensorUnsafe (X : Execution) : Prop :=
  ∃ i observation slot content, X.tensor i = some observation ∧
    observation.effects.write slot = some content ∧ content.byte = none

/-! ## ERR-REDUCTION-NO-RULE — tensor and linear reduction rules
Statement: A tensor or linear reduction is unsafe when a performed element of it has no arithmetic
  rule.

Defs: TensorStoreUnsafe

Source:
- ERR-FAULT-REASON (an instruction form without a rule)

Direction: stricter

Applies: Shared-to-global tensor issues and linear reductions

Premises: None beyond the issue and its performed reductions.

Effect: Safety rejection. The box alignment is checked when the instruction is issued
  (`requireBoxAligned`, DEP-TENSOR-LOAD-EFFECTS). A performed reduction element without an
  arithmetic rule (`ReduceNoRule`, and `CopyReduceNoRule` for a linear reduction,
  DEP-REDUCTION-VALUES) is a `noRule` fault, as a missing MMA rule is
  (ERR-TC-MMA). The lifetime of the source CTA is checked by ERR-SHARED-LIFETIME, whose
  completing stage is the read completion (`.readsDone`), and the read completion closes all
  source observations, including optional out-of-bounds reads.
-/
/-- A performed element of a tensor or linear reduction has no arithmetic rule. -/
def TensorStoreUnsafe (A : List Assumption) (X : Execution) : Prop :=
  TensorStore.ReduceNoRule A X ∨ TensorStore.CopyReduceNoRule A X

end
end PTX
