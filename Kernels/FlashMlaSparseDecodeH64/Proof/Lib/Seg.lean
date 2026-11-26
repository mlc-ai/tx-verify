-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Flow.Hooks

@[expose] public section

/-! # No assumption of the kernel takes a segment

Every one of the kernel's eleven assumptions reads single instructions only: the numeric,
parameter-pointer and shared-pointer readings (with the dead packs of `Assumptions/DeadPack.lean`
and the peer-score packs of `Assumptions/PeerScores.lean`, which `sharedBits` folds in) are local
rules, and the others constrain executions. So no pc starts a segment (`noSegments`), and a step
lemma's segment-free side is `noSegments.segFreePc` at every pc (the generated `step_<pc>`
modules, `Gen/Step/*.json`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

/-- The assumptions every machine is evaluated under. -/
noncomputable abbrev asms : List Assumption := Assumptions.all

/-- No assumption takes a segment at any state. -/
theorem asms_segment_free (L : Launch) (g : Nat) (t : TState) :
    ∀ a ∈ asms, a.segmentRule L g t = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The kernel's assumptions have no segments.** -/
theorem noSegments : Assumption.NoSegments Assumptions.all :=
  fun a ha L g t => asms_segment_free L g t a ha

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
