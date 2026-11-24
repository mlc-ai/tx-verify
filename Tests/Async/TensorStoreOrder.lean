-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Dependency
public import Core.Assembly.Waiting
public import Mathlib.Tactic

namespace PTX.Tests.TensorStoreOrder
noncomputable section

-- The fixture records both completion stages. Rejection of a read-only wait
-- as a publication of writes must depend on its mode, not missing effects.
private def spec : TensorStore.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, none⟩
private def observation : TensorStore.Observation :=
  ⟨spec, { readsDone := true, fullDone := true }⟩
private def X (mode : BulkGroup.WaitMode) : Execution := {
  tr := fun _ => [⟨0, .tensorStore 1024 spec⟩, ⟨1, .bulkCommit⟩,
    ⟨2, .bulkWait mode 0⟩, ⟨3, .tensorStore 1024 spec⟩],
  rf := fun _ _ => none, tensorStores := fun _ => some observation }

private theorem waits (mode : BulkGroup.WaitMode) :
    BulkWaitsFor (X mode) mode (0, 0) (0, 2) := by
  refine ⟨2, 0, rfl, ?_⟩
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions,
    bulkAction, X, BulkGroup.run, BulkGroup.step]

private theorem wrong_mode {a b : BulkGroup.WaitMode} (h : a ≠ b) :
    ¬ BulkWaitsFor (X a) b (0, 0) (0, 2) := by
  rintro ⟨pc, n, he, _⟩
  have hm : a = b := by cases he; rfl
  exact h hm

-- No stage of a tensor store's write part is tied to an mbarrier notification.
private theorem no_observed (Y : Execution) (i w : EvId) (ws : MbarScope) :
    ¬ AsyncCopy.AsyncObserved Y i (.write (.store 0 0 0)) w true ws := by
  rintro ⟨n, m, h, _⟩
  simp [AsyncCopy.Notifies, AsyncCopy.Part.target] at h

private theorem stages_read (mode : BulkGroup.WaitMode) :
    GroupWaitStages (X mode) (0, 0) (.bulk .read) = [.readsDone] := by
  simp [GroupWaitStages, Execution.get, X]

private theorem stages_other (mode : BulkGroup.WaitMode) (k : GroupWait) (h : k ≠ .bulk .read) :
    GroupWaitStages (X mode) (0, 0) k = [.readsDone, .fullDone] := by
  cases k with
  | bulk m => cases m <;> simp_all [GroupWaitStages, Execution.get, X]
  | cpAsync => simp [GroupWaitStages, Execution.get, X]

private theorem finished_read : AsyncFinished L (X .read) (0, 0) (.read (.store 0 0 0)) (0, 2) :=
  Or.inl ⟨.bulk .read, rfl, waits .read, by
    rw [stages_read]
    intro q hq
    obtain rfl := List.mem_singleton.1 hq
    exact ⟨observation, rfl, rfl⟩⟩

private theorem finished_full : AsyncFinished L (X .full) (0, 0) (.write (.store 0 0 0)) (0, 2) :=
  Or.inl ⟨.bulk .full, rfl, waits .full, by
    rw [stages_other .full _ (by simp)]
    intro q hq
    rcases List.mem_pair.1 hq with rfl | rfl
    · exact ⟨observation, rfl, rfl⟩
    · exact ⟨observation, rfl, rfl⟩⟩

private theorem only_finished :
    AsyncOnlyFinished (X .asyncProxy) (0, 0) (.write (.store 0 0 0)) (0, 2) :=
  ⟨rfl, waits .asyncProxy, by
    rw [stages_other .asyncProxy _ (by simp)]
    intro q hq
    rcases List.mem_pair.1 hq with rfl | rfl
    · exact ⟨observation, rfl, rfl⟩
    · exact ⟨observation, rfl, rfl⟩⟩

-- Only a full wait makes the written bytes visible to generic accesses.
private theorem not_finished_write {mode : BulkGroup.WaitMode} (h : mode ≠ .full) :
    ¬ AsyncFinished L (X mode) (0, 0) (.write (.store 0 0 0)) (0, 2) := by
  rintro (⟨k, hv, hw, _⟩ | ⟨ws, ho, _⟩)
  · have hk : k = .bulk .full := by
      cases k with
      | bulk m => cases m <;> simp [GroupWaitVisible] at hv ⊢
      | cpAsync => simp [GroupWaitVisible] at hv
    subst hk
    exact wrong_mode h hw
  · exact no_observed _ _ _ _ ho

example : AsyncFinished L (X .read) (0, 0) (.read (.store 0 0 0)) (0, 2) := finished_read

-- A read wait does not make the written bytes visible.
example : ¬ AsyncFinished L (X .read) (0, 0) (.write (.store 0 0 0)) (0, 2) :=
  not_finished_write (by decide)

example : AsyncFinished L (X .full) (0, 0) (.write (.store 0 0 0)) (0, 2) := finished_full

example : AsyncOnlyFinished (X .asyncProxy) (0, 0) (.write (.store 0 0 0)) (0, 2) := only_finished

-- An async-proxy wait is not a publication to generic accesses.
example : ¬ AsyncFinished L (X .asyncProxy) (0, 0) (.write (.store 0 0 0)) (0, 2) :=
  not_finished_write (by decide)

-- A completed read wait depends on the read completion, but not on the full completion.
private theorem needs_wait (mode : BulkGroup.WaitMode) :
    Needs L (X mode) (0, 2) = groupNeeds (X mode) (0, 2) (.bulk mode) := rfl

example : Witness L (X .read) (.async (0, 0) .readsDone) (0, 2) := by
  refine ⟨fun x => x = .async (0, 0) .readsDone, ?_, ⟨observation, rfl, rfl⟩, rfl⟩
  rw [needs_wait, groupNeeds, List.mem_flatMap]
  refine ⟨0, by simp, ?_⟩
  simp only [needsIf]
  split_ifs with hw
  · rw [stages_read]
    simp
  · exact absurd (waits .read) hw

example : ¬ Witness L (X .read) (.async (0, 0) .fullDone) (0, 2) := by
  rintro ⟨fills, hmem, _, hf⟩
  rw [needs_wait, groupNeeds, List.mem_flatMap] at hmem
  obtain ⟨j, hj, hn⟩ := hmem
  simp only [needsIf] at hn
  split_ifs at hn with hw
  · rw [List.mem_map] at hn
    obtain ⟨q, hq, hqn⟩ := hn
    obtain ⟨rfl⟩ := Need.node.inj hqn
    obtain ⟨hj0, rfl⟩ : 0 = j ∧ AsyncCopy.Part.fullDone = q := by simpa using hf
    subst hj0
    rw [stages_read] at hq
    simp at hq
  · simp at hn

-- Commit alone never waits for output completion.
example (mode : BulkGroup.WaitMode) :
    ¬ Witness L (X mode) (.async (0, 0) .fullDone) (0, 1) := by
  rintro ⟨fills, hmem, _⟩
  simp [Needs, KindNeeds, X, Execution.get] at hmem

-- Async-only observation has no generic-publication branch in modelCausality.
example (L : Launch) (Y : Execution) (i f : EvId) (l : Loc)
    (h : ∀ w, ¬ AsyncFinished L Y i (.write (.store 0 0 0)) w) :
    ¬ modelCausality L Y l (.async i (.write (.store 0 0 0))) (.thread f) := by
  rintro ⟨_, w, hw, _⟩
  exact h w hw

-- Once the source reads have completed and the read wait has returned, a
-- later generic access may reuse that source byte.
example (L : Launch) (l : Loc) (f : EvId)
    (hc : AsyncCovers (X .read) (0, 0) (.read (.store 0 0 0)) l)
    (hf : baseCausality L (X .read) (0, 2) f) :
    modelCausality L (X .read) l (.async (0, 0) (.read (.store 0 0 0))) (.thread f) :=
  ⟨hc, (0, 2), finished_read, .inl hf⟩

-- Async-only wait can order a subsequent async access, without acquiring
-- a generic visibility edge. Byte footprints are still required on both sides.
example (L : Launch) (l : Loc) (j : EvId) (p : AsyncCopy.Part)
    (hi : AsyncCovers (X .asyncProxy) (0, 0) (.write (.store 0 0 0)) l)
    (hj : AsyncCovers (X .asyncProxy) j p l)
    (hp : po (X .asyncProxy) (0, 2) j) (hs : SameCta L 0 j.1) :
    modelCausality L (X .asyncProxy) l (.async (0, 0) (.write (.store 0 0 0))) (.async j p) :=
  ⟨.inl hs, .direct ⟨hi, hj, Or.inr ⟨(0, 2), only_finished, hp⟩⟩⟩

-- The issuing thread can continue to another copy without waiting for the
-- previous output write. No completion dependency is inferred from that order.
example (mode : BulkGroup.WaitMode) :
    ¬ Witness L (X mode) (.async (0, 0) .fullDone) (0, 3) := by
  rintro ⟨fills, hmem, _⟩
  simp [Needs, KindNeeds, X, Execution.get] at hmem

-- A byte write is stage-ordered after its own source read only, not after another byte's read.
example (Y : Execution) (i : EvId) :
    ¬ StageEdge Y (.async i (.read (.store 0 0 0))) (.async i (.write (.store 1 0 0))) := by
  intro h
  simp [StageEdge] at h

example (Y : Execution) (i : EvId) :
    ¬ StageOrder Y (.async i (.read (.store 0 0 0)), true)
      (.async i (.write (.store 1 0 0)), false) := by
  rintro (⟨h, _⟩ | ⟨_, _, h⟩)
  · simp at h
  · simp [StageEdge] at h

end
end PTX.Tests.TensorStoreOrder
