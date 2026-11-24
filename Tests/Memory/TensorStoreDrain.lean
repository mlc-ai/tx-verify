-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.StoreDrain
public import Lemmas.Execution.ExecutionGrowth

/-! # Scope of the opt-in store-source drain at thread exit -/

namespace PTX.Tests.TensorStoreDrain

private def snapshot (spec : TensorStore.Spec) (ready : Bool) : Execution :=
  { Execution.empty with
    tr := fun g =>
      if g = 0 then [⟨1, .tensorStore 0 spec⟩, ⟨2, .exit⟩] else [⟨2, .exit⟩]
    tensorStores := fun i =>
      if i = (0, 0) then some ⟨spec, { readsDone := ready }⟩ else none }

private def selectStore (site : Nat) : Assumption where
  name := "store-source-drain"
  statement := "Selected stores drain their source reads before the issuer exits."
  storeReadsBeforeExit := (· == site)

/-- The hook recognizes a performed shared read completion even while global writes are pending. -/
theorem readDone_selected (spec : TensorStore.Spec) :
    StoreReadsBeforeExit [selectStore 1] (snapshot spec true) (.async (0, 0) .readsDone)
      (.thread (0, 1)) := by
  refine ⟨?_, ⟨1, 0, spec, rfl, rfl⟩, ⟨2, rfl⟩, ?_⟩
  · simp [TraceBefore, snapshot]
  · exact ⟨⟨spec, { readsDone := true }⟩, rfl, rfl⟩

theorem fullDone_absent (spec : TensorStore.Spec) :
    ¬ (snapshot spec true).AsyncPresent (0, 0) .fullDone := by
  simp [Execution.AsyncPresent, snapshot]

/-- A selected site still needs an actual read completion. -/
theorem readDone_pending (spec : TensorStore.Spec) :
    ¬ StoreReadsBeforeExit [selectStore 1] (snapshot spec false) (.async (0, 0) .readsDone)
      (.thread (0, 1)) := by
  rintro ⟨-, -, -, h⟩
  simp [Execution.AsyncPresent, snapshot] at h

/-- The execution constraint rejects an issuer exit with outstanding shared source reads. -/
theorem exit_pending (spec : TensorStore.Spec) :
    ¬ TensorStore.ReadsDrainedBeforeExit (selectStore 1).storeReadsBeforeExit
      (snapshot spec false) := by
  intro h
  have hb : TraceBefore (snapshot spec false) (0, 0) (0, 1) := by
    simp [TraceBefore, snapshot]
  have hp := h hb ⟨1, 0, spec, rfl, rfl⟩ ⟨2, rfl⟩
  simp [Execution.AsyncPresent, snapshot] at hp

/-- Another thread's exit provides no drain edge. -/
theorem other_exit (spec : TensorStore.Spec) :
    ¬ StoreReadsBeforeExit [selectStore 1] (snapshot spec true) (.async (0, 0) .readsDone)
      (.thread (1, 0)) := by
  rintro ⟨hb, -, -, -⟩
  simp [TraceBefore] at hb

/-- A completed operation at a different site provides no drain edge. -/
theorem other_site (spec : TensorStore.Spec) :
    ¬ StoreReadsBeforeExit [selectStore 0] (snapshot spec true) (.async (0, 0) .readsDone)
      (.thread (0, 1)) := by
  rintro ⟨-, ⟨site, address, sp, hi, hsel⟩, -, -⟩
  have hi' : (snapshot spec true).get (0, 0) = some ⟨1, .tensorStore 0 spec⟩ := rfl
  rw [hi'] at hi
  cases hi
  simp [selectStore] at hsel

end PTX.Tests.TensorStoreDrain
