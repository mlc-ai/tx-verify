-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.TensorStore.TensorStore
public import Core.Async.BulkExecution
public import Core.Assembly.Correctness

namespace PTX.Tests.TensorStoreExecution
noncomputable section

private def L : Launch := { grid := 1, block := 1, params := fun _ => none }
private def spec : TensorStore.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, none⟩
private def byte : Byte := (.float .f16 0, 0)
private def observation : TensorStore.Observation :=
  ⟨spec, { read := fun _ => some byte, readsDone := true }⟩
private def trace (mode : BulkGroup.WaitMode) : List Event :=
  [⟨0, .tensorStore 1024 spec⟩, ⟨1, .bulkCommit⟩, ⟨2, .bulkWait mode 0⟩]
private def X (mode : BulkGroup.WaitMode) : Execution := {
  tr := fun g => if g = 0 then trace mode else [], rf := fun _ _ => none,
  tensorStores := fun i => if i = (0, 0) then some observation else none }

example (mode : BulkGroup.WaitMode) : TensorStoreOk L (X mode) := by
  intro i o ho
  change (if i = (0, 0) then some observation else none) = some o at ho
  split_ifs at ho with hi
  · subst i
    cases ho
    refine ⟨⟨1024, 0, rfl⟩, ?_, ?_⟩
    · unfold TensorStore.Valid
      decide
    · constructor
      · intro slot b hw; cases hw
      · intro _ slot loc _; exact ⟨byte, rfl⟩
      · intro h; cases h
      · intro slot b hw; cases hw
      · intro slot b h; cases h

private theorem observed (mode : BulkGroup.WaitMode) :
    BulkGroup.Observes (bulkStateBefore (X mode) (0, 2)) 0 (0, 0) := by
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions,
    bulkAction, X, trace, BulkGroup.run, BulkGroup.step]

private theorem needsIf_pos {P : Prop} (h : P) (ns : List Need) : needsIf P ns = ns := by
  simp [needsIf, h]

private theorem needsIf_neg {P : Prop} (h : ¬P) (ns : List Need) : needsIf P ns = [] := by
  simp [needsIf, h]

private theorem needs_bulkWait {Y : Execution} {e : EvId} {mode : BulkGroup.WaitMode}
    {n pc : Nat} (h : Y.get e = some ⟨pc, .bulkWait mode n⟩) :
    Needs L Y e = groupNeeds Y e (.bulk mode) := by
  simp only [Needs, h, KindNeeds]

private theorem groupWaitsFor_store (mode : BulkGroup.WaitMode) :
    GroupWaitsFor (X mode) (.bulk mode) (0, 0) (0, 2) :=
  ⟨2, 0, rfl, observed mode⟩

-- A commit is no operation of the group, so the wait does not cover it.
private theorem not_groupWaitsFor_commit (mode : BulkGroup.WaitMode) :
    ¬ GroupWaitsFor (X mode) (.bulk mode) (0, 1) (0, 2) := by
  rintro ⟨pc, remaining, h, hobs⟩
  simp only [X, trace] at h
  cases h
  simp [BulkGroup.Observes, BulkGroup.required, bulkStateBefore, bulkActions, bulkAction, X,
    trace, BulkGroup.run, BulkGroup.step] at hobs

-- The needs of the wait are the stages of the one group it covers.
private theorem needs_stages (mode : BulkGroup.WaitMode) (stages : List AsyncCopy.Part)
    (hst : GroupWaitStages (X mode) (0, 0) (.bulk mode) = stages) :
    Needs L (X mode) (0, 2) =
      stages.map fun p => Need.node fun x => x = .async (0, 0) p := by
  rw [needs_bulkWait (Y := X mode) rfl]
  unfold groupNeeds
  dsimp only
  rw [show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, needsIf_pos (groupWaitsFor_store mode),
    needsIf_neg (not_groupWaitsFor_commit mode), hst, List.append_nil]
  simp

private theorem needs_read :
    Needs L (X .read) (0, 2) = [Need.node fun x => x = .async (0, 0) .readsDone] := by
  have hst : GroupWaitStages (X .read) (0, 0) (.bulk .read) = [.readsDone] := by
    simp [GroupWaitStages, X, trace, Execution.get]
  rw [needs_stages .read [.readsDone] hst]
  rfl

private theorem needs_full :
    Needs L (X .full) (0, 2) =
      [Need.node fun x => x = .async (0, 0) .readsDone,
        Need.node fun x => x = .async (0, 0) .fullDone] := by
  have hst : GroupWaitStages (X .full) (0, 0) (.bulk .full) = [.readsDone, .fullDone] := by
    simp [GroupWaitStages, X, trace, Execution.get]
  rw [needs_stages .full [.readsDone, .fullDone] hst]
  rfl

-- A read wait is ready when all reads (but no output writes) are recorded.
example : Ready L (X .read) (0, 2) := by
  intro n hn
  rw [needs_read] at hn
  obtain rfl := List.mem_singleton.mp hn
  exact ⟨.async (0, 0) .readsDone, ⟨observation, rfl, rfl⟩, rfl⟩

-- Changing only the wait mode to full cannot invent output completion.
example : ¬ Ready L (X .full) (0, 2) := by
  intro h
  have hm : (Need.node fun x => x = .async (0, 0) .fullDone) ∈ Needs L (X .full) (0, 2) := by
    rw [needs_full]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨x, hx, rfl⟩ := h _ hm
  obtain ⟨o, ho, hd⟩ := hx
  have heq : observation = o := Option.some.inj ho
  subst o
  cases hd

-- Erasing the completed read observations is not an execution extension.
example : ¬ (X .read).le { X .read with tensorStores := fun _ => none } := by
  intro h
  obtain ⟨o, ho, _⟩ := h.2.2.2.2.2.2.2.2.2.1 (0, 0) observation rfl
  cases ho

-- Effect records require an actual matching issuing instruction.
example : ¬ TensorStoreOk L { X .read with tr := fun _ => [] } := by
  intro h
  obtain ⟨⟨a, pc, he⟩, _⟩ := h (0, 0) observation rfl
  cases he

-- Read completion is not enough for the kernel's async-drain obligation.
example : ¬ AsyncDrained (X .read) := by
  intro h
  have hf : AsyncCopy.FinalStage (X .read) (0, 0) .fullDone :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨1024, spec, ⟨0, rfl⟩, rfl⟩))))))
  obtain ⟨o, ho, hd⟩ := h (0, 0) .fullDone hf
  have heq : observation = o := Option.some.inj ho
  subst o
  cases hd

end
end PTX.Tests.TensorStoreExecution
