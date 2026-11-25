-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Wire
public import Kernels.FlashKdaFwd.Proof.Top.Existence

@[expose] public section

/-!
# The kernel is correct, from what each layer of the proof delivers

`Correct.lean` reduces the theorem to `Premises` (the safety facts, progress, the bound, the
result facts). `Wire.lean` reduces the safety facts to the contracts of the layers below. This
file states the whole theorem against those contracts, one field per deliverable:

* `facts`, `union`: the protocol layer's contracts, proved by the reference layer for every
  consistent execution (`Proof/Ref`): per-thread facts about barriers and mbarriers, and the
  classification of the accesses of the buffer region (with the owner functions `owners`);
* `direct`: footprints, the matrix schedule and the operands of tensor copies (reference layer),
  no undefined-behaviour event and the operands of the multiply-accumulate (reference and value
  layers);
* `result`: every output and final-state byte is written, with the specified value (reference,
  protocol and value layers);
* `progress`, `bound`: the two goals, from the instance of `Proof/Progress` on the thread machine.

`correct_of_layers` is then the kernel's theorem, and the two existence statements follow.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX
open PTX.Kernels.FlashKdaFwd.Protocol (Facts UnionFacts Owners ctaTiles)

/-- **What the layers of the proof deliver for one launch.** -/
structure Layers (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  /-- The contract of the protocol layer holds of every consistent execution. -/
  facts : ∀ X, Consistent L kernel Assumptions.all mem0 X → Facts P L X
  /-- The accesses of the buffer region of every consistent execution are classified, for some
  owner functions. -/
  union : ∀ X, Consistent L kernel Assumptions.all mem0 X →
    ∃ O : Owners, UnionFacts L X (ctaTiles P) O
  /-- The safety facts that the protocol contract does not give. -/
  direct : ∀ X, Consistent L kernel Assumptions.all mem0 X → DirectFacts P L mem0 X
  /-- The result facts. -/
  result : ∀ X, Consistent L kernel Assumptions.all mem0 X → ResultFacts P L mem0 X
  /-- Given safety, a maximal execution is complete. -/
  progress : SafeGoal kernel Assumptions.all L mem0 → ProgressGoal kernel Assumptions.all L mem0
  /-- Some number bounds the size of every consistent execution. -/
  bound : BoundGoal kernel Assumptions.all L mem0

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The premises of `correct_of_premises`, from the layers. -/
theorem Layers.premises (hp : Pre P L mem0) (H : Layers P L mem0) : Premises P L mem0 where
  safety X hX := by
    obtain ⟨O, U⟩ := H.union X hX
    exact safetyFacts hp hX (H.facts X hX) U (H.direct X hX)
  progress := H.progress
  bound := H.bound
  result := H.result

/-- **The kernel is correct on every launch that satisfies `Pre`, given the layers.** -/
theorem correct_of_layers (hp : Pre P L mem0) (H : Layers P L mem0) :
    Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  correct_of_premises hp (H.premises hp)

/-- A completed execution exists. -/
theorem completed_execution_of_layers (hp : Pre P L mem0) (H : Layers P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  completed_execution_of_correct hp (correct_of_layers hp H)

/-- A completed execution with the specified result exists. -/
theorem realizable_result_of_layers (hp : Pre P L mem0) (H : Layers P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  realizable_result_of_correct hp (correct_of_layers hp H)

end PTX.Kernels.FlashKdaFwd.Proof.Top
