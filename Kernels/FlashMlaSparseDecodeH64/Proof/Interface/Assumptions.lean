-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Lemmas.Kernel.Existence
public import Lemmas.Kernel.StoreDrain
public import Lemmas.Step.CommitOrderExtend

@[expose] public section

/-! # The assumption list on the empty execution

The existence theorems (`Correct.complete_exists`, `Correct.output_exists`) ask every assumption
to hold on `Execution.empty`. The numeric and site assumptions are vacuously true there: their
`wf`/`ub` predicates quantify over events, and the empty execution has none. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Interface
open PTX

/-- Every kernel assumption holds on the empty execution. -/
theorem all_wf_empty (L : Launch) (mem0 : Mem0) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Execution.empty := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Assumptions.idealArith, Assumptions.approx, Assumptions.mulBf16x2,
      Assumptions.cvtBf16x2, Assumptions.cvtUe8m0, Assumptions.lg2Exact,
      Assumptions.ncReadOnly, Assumptions.paramPointers, Assumptions.storeDrain,
      Assumptions.sharedBits, Assumptions.commitOrder, Assumption.commitOrderAt,
      Assumption.commitPerformedAt,
      Assumption.idealReal, Assumption.approxExact, Assumption.ncReadOnly,
      TensorStore.ReadsDrainedBeforeExit, TraceBefore, Execution.empty, Execution.get]

/-- Monotone effect-only steps preserve all kernel assumptions when new commit notifications
respect the selected issue order. -/
theorem all_wf_effects_inOrder {L : Launch} {mem0 : Mem0} {X Y : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hle : X.le Y)
    (htrace : Y.tr = X.tr) (hinitial : Y.initial = X.initial)
    (hOrder : X.NotifiedInOrder Assumptions.commitOrder.commitInOrder Y) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Y := by
  have hget : Y.get = X.get := by funext i; simp only [Execution.get, htrace]
  intro a ha
  have hold := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact TensorStore.ReadsDrainedBeforeExit.of_trace hold htrace
        (fun _ => Execution.readsDone_mono hle)
    | simpa only [Assumptions.ncReadOnly, Assumption.ncReadOnly, Execution.initialByte,
        hinitial, hget] using hold
    | exact Assumption.commitPerformedAt_extend (fun _ h => h) hold hX.tcCommit hle hOrder

/-- An effect-only step that preserves commit notifications preserves all assumptions. -/
theorem all_wf_effects {L : Launch} {mem0 : Mem0} {X Y : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hle : X.le Y)
    (htrace : Y.tr = X.tr) (hinitial : Y.initial = X.initial)
    (hnotify : Y.tcNotified = X.tcNotified) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Y :=
  all_wf_effects_inOrder hX hle htrace hinitial (Execution.notifiedInOrder_of_eq hnotify)

/-- A new non-NC event preserves all assumptions when an appended exit has drained the
previously issued selected stores of its thread. -/
theorem all_wf_snoc_of_not_nc {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {event : Event} {rf : Nat → Option AsyncCopy.Ref}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hnc : ∀ acc bytes, event.kind ≠ .nc acc bytes)
    (hnew : event.kind = .exit → ∀ i, i.1 = g →
      TensorStore.Selected Assumptions.storeDrain.storeReadsBeforeExit X i →
      X.AsyncPresent i .readsDone) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.snoc g event rf) := by
  intro a ha
  have hold := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hold
    | exact TensorStore.ReadsDrainedBeforeExit.snoc hold hnew
    | intro j eventSite acc bytes he hp
      rw [snoc_get] at he
      split_ifs at he
      · exact False.elim (hnc acc bytes (congrArg Event.kind (Option.some.inj he)))
      · exact hold j eventSite acc bytes he hp
    | exact Assumption.commitPerformedAt_extend (fun _ h => h) hold hX.tcCommit le_snoc
        (Execution.notifiedInOrder_of_eq (sel := Assumptions.commitOrder.commitInOrder) rfl)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Interface
