-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Lemmas.Protocol.UnitObject
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A barrier whose updates are its producers' unit arrivals

From the uses of an object alone: when every event naming `l` is an initialization, a poll with
the parity of its thread's earlier successful polls plus `δ`, or a producer's unit arrival without
bytes, and the history starts with the initialization of count `N`, `l` is a `MbarRing.Unit.Obj`
of the producers (`unit_of_uses`). The raw ring's `rawFree` and the index ring's `coordReady` and
`coordFree` are such objects. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A barrier of its producers' unit arrivals is a unit object.** -/
theorem unit_of_uses (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {l : Loc} {N δ : Nat} {prod : Fin N → Nat} (hN : 0 < N) (hinj : Function.Injective prod)
    (hδ : δ ≤ 1) (hinit : PairTmaRing.InitFirst X l N)
    (hu : ∀ {g k : Nat} {e : Event}, X.get (g, k) = some e → Frame.MbarOf e l →
      (∃ c, e.kind = .mbInit l c) ∨
        (∃ q, MbarRow.Wait e l q ∧ q % 2 = (okPolls l ((X.tr g).take k) + δ) % 2) ∨
        (∃ a, g = prod a) ∧ MbarRow.Arrive e l 0) :
    Unit.Obj X l N prod δ := by
  have ho := hX.tma.2.2.1
  refine ⟨hN, hinj, ?_, hinit, AsyncCopy.objects_noInval ho (no_inval hX hR) _, ?_, hδ⟩
  · intro r hr
    cases AsyncCopy.record_source ho hr with
    | init _ _ ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | inval hid he _ => exact (no_inval hX hR _ _ ⟨_, he⟩).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_asyncArrive hX hR he).elim
    | bulk _ he hc _ _ => exact (no_copy hX hR he hc).elim
    | clc _ he _ htg _ => exact (no_clc hX hR he htg).elim
    | @tensor i pc a sp hid he hm ha =>
      obtain ⟨h, j⟩ := i
      rcases hu he hm with ⟨_, hk⟩ | ⟨_, ⟨ok, hk⟩, -⟩ | ⟨-, hk⟩ <;> cases hk
    | @commit i pc sp rank hid he ht ha =>
      obtain ⟨h, j⟩ := i
      rcases hu he ⟨rank, ht⟩ with ⟨_, hk⟩ | ⟨_, ⟨ok, hk⟩, -⟩ | ⟨-, hk⟩ <;> cases hk
    | @arrive h j pc tx cnt rel sc hid he ha =>
      rcases hu he rfl with ⟨_, hk⟩ | ⟨_, ⟨ok, hk⟩, -⟩ | ⟨hp, hk⟩
      · cases hk
      · cases hk
      · simp only [MbarRow.Arrive, Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        exact .arrive hid hp he ha
  · intro g k pc p acq sc he
    rcases hu he rfl with ⟨_, hk⟩ | ⟨q, ⟨ok, hk⟩, hq⟩ | ⟨-, hk⟩
    · cases hk
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -⟩ := hk
      exact hq
    · cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
