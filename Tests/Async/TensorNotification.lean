-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorExecution
public import Lemmas.Tensor.TensorCopySize
public import Lemmas.Tensor.TensorGrowth
public import Core.Memory.Order
public import Core.Assembly.Waiting
public import Lemmas.MBarrier.MBarrierHistory

namespace PTX.Tests.TensorNotification
noncomputable section
open AsyncCopy

/-- Both threads lie in one CTA, so the waiter's scope meets the notification's. -/
private def L : Launch := { grid := 1, block := 2, params := fun _ => none }

private def mb : Loc := ⟨.shared, 1, 64⟩
private def spec : TensorCopy.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![-16, 0], ⟨.shared,
    0, 128⟩, none⟩, mb, true, .two⟩
private def observation : TensorCopy.Observation := ⟨spec, {
  write := fun slot => some (.filled .zero .f16 slot.2.2.val), notified := true }⟩
private def ops : List (Ref × MBarrier.Action) := [
  (.thread (1, 0), .init 1), (.thread (1, 1), .arrive 1 16),
  (.async (0, 0) (.notify .load), .completeTx 16), (.thread (1, 2), .pollParity 0 true)]
private def log : List (MBarrier.Record Ref) := match MBarrier.replay none ops with
  | .ok xs => xs | .error _ => []
private def X : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorIssue 1024 spec⟩]
    else if g = 1 then [⟨0, .mbInit mb 1⟩, ⟨1, .arrive mb 16⟩, ⟨2, .wait mb 0 true⟩] else [],
  rf := fun _ _ => none,
  tensor := fun i => if i = (0, 0) then some observation else none,
  objects := fun m => if m = mb then log else [] }

example : MBarrier.CheckedLog log :=
  MBarrier.checkedLog_of_replay (ops := ops) rfl (by decide)
example : objectAction X X.async mb (.async (0, 0) (.notify .load)) = some (.completeTx 16) := rfl
example : objectAction X X.async ⟨.shared, 0, 64⟩ (.async (0, 0) (.notify .load)) = none := rfl
example : objectAction { X with tensor := fun _ => none } X.async mb
    (.async (0, 0) (.notify .load)) = none := rfl
example : objectAction { X with tr := fun _ => [] } X.async mb
    (.async (0, 0) (.notify .load)) = none := rfl

example : MatchesObject X X.async mb log := by
  intro r hr
  change r ∈ [_, _, _, _] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals refine ⟨rfl, ?_⟩
  all_goals intro p ok hp _
  all_goals cases hp
  rfl

private theorem observed : AsyncCopy.AsyncObserved X (0, 0) (.notify .load) (1, 2) true .cta := by
  refine ⟨_, _, ⟨rfl, observation, 1024, rfl, ⟨0, rfl⟩, rfl, rfl⟩, ⟨2, 0, rfl⟩, ?_⟩
  change MBarrier.UpdateBeforeWait log _ _
  exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

example : AsyncFinished L X (0, 0) (.write (.load 0 0 0)) (1, 2) :=
  .inr ⟨.cta, observed, by simp [ScopesMeet, MbarScopeIncludes, SameCta, SameCluster, L,
    Launch.threads, Launch.clusterOfCta]⟩

private theorem write_present : X.AsyncPresent (0, 0) (.write (.load 0 0 0)) := by
  let slot : TensorTransfer.Slot spec.descriptor :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  exact ⟨observation, slot, .filled .zero .f16 0, rfl, rfl, rfl⟩

-- OOB filling needs no global read, but the write still follows issue and precedes notify.
example : TensorCopy.readByte observation 0 0 0 = none := rfl
example : IssueStage X (.thread (0, 0), false) (.async (0, 0) (.write (.load 0 0 0)), false) :=
  ⟨rfl, rfl, (0, 0), .write (.load 0 0 0), rfl, rfl, ⟨⟨0, .tensorIssue 1024 spec⟩, rfl⟩,
    write_present, trivial⟩
example : StageEdge X (.async (0, 0) (.write (.load 0 0 0))) (.async (0, 0) (.notify .load)) :=
  ⟨rfl, rfl, write_present, ⟨observation, rfl, rfl⟩⟩
example : ¬ StageEdge X (.async (0, 0) (.notify .load)) (.thread (0, 1)) := by
  simp [StageEdge]
example : ¬ StageEdge X (.async (0, 0) (.write (.load 0 0 0)))
    (.async (0, 1) (.notify .load)) := by
  intro h
  exact absurd h.1 (by decide)

-- Arrival/init of the same object is not observation of completion.
example : ¬ AsyncFinished L X (0, 0) (.write (.load 0 0 0)) (1, 0) := by
  have hget : X.get (1, 0) = some ⟨0, .mbInit mb 1⟩ := rfl
  rintro (⟨k, -, hw, -⟩ | ⟨ws, ⟨n, m, -, ⟨⟨pc, parity, hp⟩, -⟩⟩, hsc⟩)
  · cases k with
    | bulk mode =>
      obtain ⟨pc, rem, hw, -⟩ := hw
      rw [hget] at hw
      cases hw
    | cpAsync =>
      obtain ⟨pc, rem, hw, -⟩ := hw
      rw [hget] at hw
      cases hw
  · rw [hget] at hp
    cases hp

-- Once the actual wait is ordered before a consumer, the exact byte is visible there.
example (L : Launch) (consumer : EvId) (hm : ScopesMeet L .cluster 0 .cta 1)
    (hafter : baseCausality L X (1, 2) consumer) :
    modelCausality L X ⟨.shared, 0, 144⟩ (.async (0, 0) (.write (.load 0 0 0)))
        (.thread consumer) := by
  refine ⟨⟨{ loc := ⟨.shared, 0, 144⟩, size := 1 }, true,
    ⟨rfl, spec, 1024, ⟨0, rfl⟩, rfl, rfl⟩, ?_⟩, (1, 2), .inr ⟨.cta, observed, hm⟩, .inl hafter⟩
  simp [Acc.Covers, Loc.InRange]

-- Every OOB byte write counts, even though none has a global source read.
example : observation.effects.size = 17 := by
  simp [observation, TensorCopy.Effects.size, TensorCopy.Effects.readSlots,
    TensorCopy.Effects.writeSlots, TensorTransfer.Slot, TensorTile.count,
    TensorTile.step, TensorTile.rows, TensorTile.rowsOf, spec, TensorDescriptor.Format.bytes]
  rfl

example : ({} : TensorCopy.Effects spec).size = 0 := TensorCopy.Effects.size_empty spec

-- Tensor effects are part of execution size, not only a private copy measure.
example : X.asyncSize (0, 0) = 17 := by
  change observation.effects.size = 17
  simp [observation, TensorCopy.Effects.size, TensorCopy.Effects.readSlots,
    TensorCopy.Effects.writeSlots, TensorTransfer.Slot, TensorTile.count,
    TensorTile.step, TensorTile.rows, TensorTile.rowsOf, spec, TensorDescriptor.Format.bytes]
  rfl

-- Recording the completion notification is strict progress at the execution level.
example (L : Launch) (hg : 0 < L.threads) :
    ({ X with tensor := fun i => if i = (0, 0) then some ⟨spec,
              { observation.effects with notified := false }⟩ else none }).size L <
    X.size L := by
  let old : TensorCopy.Observation := ⟨spec, { observation.effects with notified := false }⟩
  let before : Execution := { X with tensor := fun i => if i = (0, 0) then some old else none }
  have hs : old.effects.size < observation.effects.size := by
    unfold TensorCopy.Effects.size
    change observation.effects.readSlots.card + observation.effects.writeSlots.card + 0 <
      observation.effects.readSlots.card + observation.effects.writeSlots.card + 1
    omega
  have h := Execution.tensor_update_size (X := before) (L := L) (i := (0, 0))
    (old := old) (newer := observation) rfl hg (by decide) hs
  have he : ({ before with tensor := fun j => if j = (0, 0) then some observation else
                           before.tensor j }) = X := by
    congr 1
    funext j
    change (if j = (0, 0) then some observation else if j = (0, 0) then some old else none) =
      (if j = (0, 0) then some observation else none)
    split_ifs <;> rfl
  rw [he] at h
  exact h

end
end PTX.Tests.TensorNotification
