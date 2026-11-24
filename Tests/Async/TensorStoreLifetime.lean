-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorSafety
public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Order.WaitOrderWaits
public import Mathlib.Data.Fin.VecNotation

namespace PTX.Tests.TensorStoreLifetime
noncomputable section

private def L : Launch := { grid := 1, block := 1, params := fun _ => none }
private def K : Kernel := { name := "k", params := [], code := [] }
private def spec : TensorStore.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, none⟩
private def observation (done : Bool) : TensorStore.Observation :=
  ⟨spec, { read := fun _ => some (.float .f16 0, 0), readsDone := done }⟩
private def X (done : Bool) : Execution := {
  tr := fun _ => [⟨0, .tensorStore 1024 spec⟩, ⟨1, .bulkCommit⟩,
    ⟨2, .bulkWait .read 0⟩, ⟨3, .exit⟩], rf := fun _ _ => none,
  tensorStores := fun _ => some (observation done) }

private theorem waits : BulkWaitsFor (X true) .read (0, 0) (0, 2) := by
  refine ⟨2, 0, rfl, ?_⟩
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions,
    bulkAction, X, BulkGroup.run, BulkGroup.step]

-- Read wait observing the reads' completion, a blocking return followed by the exit, provides a
-- lifetime witness; fullDone remains false.
example : SharedFinished L K [] (X true) (.async (0, 0) .readsDone) 0 := by
  refine ⟨⟨observation true, rfl, rfl⟩, (0, 3), 3, by decide, rfl, rfl, ?_⟩
  have hw : Witness L (X true) (.async (0, 0) .readsDone) (0, 2) :=
    GroupWaitsFor.witness (k := .bulk .read) (p := .readsDone) waits (by decide)
      ⟨observation true, rfl, rfl⟩
  refine CompletedBefore.of_observed hw (.single ?_)
  exact DepStep.of_resumes L (Resumes.of_blocking (X := X true) (w := (0, 2)) (f := (0, 3))
    rfl rfl ⟨rfl, by decide, by decide⟩)

example : ¬ (X true).AsyncPresent (0, 0) .fullDone := by
  rintro ⟨o, ho, hd⟩
  cases ho
  cases hd

-- If all source-owner threads exited without completed reads, reject the execution: the read
-- completion is a use of the source CTA (ERR-SHARED-LIFETIME).
example : SharedLifetimeUnsafe L K [] (X false) := by
  refine ⟨.async (0, 0) .readsDone, 0,
    .inr (.inr (.inr (Or.inl ⟨(0, 0), 1024, spec, rfl, ⟨0, rfl⟩, rfl⟩))), .inr ⟨?_, ?_⟩⟩
  · intro g hg _
    exact ⟨3, rfl⟩
  · rintro ⟨⟨o, ho, hd⟩, _⟩
    cases ho
    cases hd

-- The lifetime check of a store's read completion is discharged by reads completed before an
-- owner exit; it does not ask for full completion or a particular group depth.
example (Y : Execution)
    (h : ∀ i address s, Y.TensorStoreIssue i address s → CtaExited L Y s.sharedBase.cta →
      SharedFinished L K [] Y (.async i .readsDone) s.sharedBase.cta)
    (i : EvId) (address : Nat) (s : TensorStore.Spec) (hi : Y.TensorStoreIssue i address s) :
    ¬ (CtaExited L Y s.sharedBase.cta ∧
      ¬ SharedFinished L K [] Y (.async i .readsDone) s.sharedBase.cta) :=
  fun ⟨he, hn⟩ => hn (h i address s hi he)

-- The store's own check is only the reduction rules; the box alignment is checked when the thread
-- issues the store (`tensorStoreSpec_boxAligned`).
example (Y : Execution)
    (hnr : ∀ i o, Y.tensorStores i = some o → o.spec.reduce = none)
    (hnc : ∀ i s, Y.Copy i s → ∀ r, s.writes ≠ .reduce r) :
    ¬ TensorStoreUnsafe [] Y := by
  rintro (⟨i, o, red, x, y, ho, hr, -⟩ | h)
  · exact absurd hr (by simp [hnr i o ho])
  · exact TensorStore.not_copyReduceNoRule_of_none hnc h

end
end PTX.Tests.TensorStoreLifetime
