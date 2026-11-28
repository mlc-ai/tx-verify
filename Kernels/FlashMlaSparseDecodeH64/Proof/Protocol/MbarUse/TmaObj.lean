-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Lemmas.Protocol.TmaUnits
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A barrier whose updates are one lane's TMA arrivals and loads

From the uses of an object alone: when every event naming `l` is an initialization, a poll, or
lane `y`'s tensor load of `bytes` bytes or its unit arrival expecting `n · bytes` bytes, and the
history starts with the initialization of count 1, `l` is a `MbarRing.TmaUnits.Obj` of `y`
(`tmaUnits_of_uses`). The query barrier `qTma` (`Protocol/Query/Obj.lean`) and the raw ring's
`rawReady` (`Protocol/Raw/Obj.lean`) are such objects. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A barrier of one lane's tensor loads and expecting arrivals is a `TmaUnits` object.** -/
theorem tmaUnits_of_uses (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {l : Loc} {y n bytes : Nat} (hinit : PairTmaRing.InitFirst X l 1)
    (hu : ∀ {g k : Nat} {e : Event}, X.get (g, k) = some e → Frame.MbarOf e l →
      (∃ c, e.kind = .mbInit l c) ∨ (∃ q, MbarRow.Wait e l q) ∨
        g = y ∧ (MbarRow.Issue e l bytes ∨ MbarRow.Arrive e l (n * bytes))) :
    TmaUnits.Obj X l y n bytes := by
  have ho := hX.tma.2.2.1
  refine ⟨hinit, AsyncCopy.objects_noInval ho (no_inval hX hR) _, ?_, ?_, ?_⟩
  · intro r hr ha
    cases AsyncCopy.record_source ho hr with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | arrive _ _ ha' | tensor _ _ _ ha'
    | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | commit _ _ _ ha' | clc _ _ _ _ ha' =>
      rw [ha] at ha'; cases ha'
    | increment _ he _ => exact no_asyncArrive hX hR he
  · intro k cnt tx r hr ha
    cases AsyncCopy.record_source ho (List.mem_of_getElem? hr) with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | increment _ _ ha'
    | bulk _ _ _ _ ha' | clc _ _ _ _ ha' => rw [ha] at ha'; cases ha'
    | arriveOn _ he _ _ _ => exact (no_asyncArrive hX hR he).elim
    | @commit i pc sp rank _ he ht _ =>
      obtain ⟨h, j⟩ := i
      rcases hu he ⟨rank, ht⟩ with ⟨_, hk⟩ | ⟨_, ok, hk⟩ | ⟨-, ⟨_, _, hk, -⟩ | hk⟩ <;> cases hk
    | @arrive h j pc tx' cnt' rel sc hid he ha' =>
      rw [ha] at ha'
      simp only [MBarrier.Action.arrive.injEq] at ha'
      obtain ⟨rfl, rfl⟩ := ha'
      rcases hu he rfl with ⟨_, hk⟩ | ⟨_, ok, hk⟩ | ⟨rfl, ⟨_, _, hk, -⟩ | hk⟩
      · cases hk
      · cases hk
      · cases hk
      · simp only [MbarRow.Arrive, Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, -, -⟩ := hk
        exact ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩
  · intro k b r hr ha
    cases AsyncCopy.record_source ho (List.mem_of_getElem? hr) with
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | arrive _ _ ha' | increment _ _ ha'
    | arriveOn _ _ _ _ ha' | commit _ _ _ ha' => rw [ha] at ha'; cases ha'
    | bulk _ he hc _ _ => exact (no_copy hX hR he hc).elim
    | clc _ he _ htg _ => exact (no_clc hX hR he htg).elim
    | @tensor i pc a sp hid he hm ha' =>
      rw [ha] at ha'
      simp only [MBarrier.Action.completeTx.injEq] at ha'
      obtain ⟨h, j⟩ := i
      rcases hu he hm with ⟨_, hk⟩ | ⟨_, ok, hk⟩ | ⟨rfl, ⟨a', sp', hk, -, hb⟩ | hk⟩
      · cases hk
      · cases hk
      · simp only [Kind.tensorIssue.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨ha'.trans hb, j, pc, _, _, hid, he, hm⟩
      · cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
