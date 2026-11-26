-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Lemmas.Protocol.UnitNotify
public import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A barrier whose updates are one lane's commits

From the uses of an object alone: when every event naming `l` is an initialization, a poll (with
the parity of its thread's earlier successful polls plus `δ` when the thread is `selected`), or
lane `y`'s `tcgen05.commit` addressing `l`, and the history starts with the initialization of
count 1, `l` is a commit object `MbarRing.Notify.Obj` of `y` (`notify_of_uses`). The main loop's
`qkDone` and `svDone` are such objects. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A barrier of one lane's commits is a commit object.** -/
theorem notify_of_uses (hX : Consistent L kernel Assumptions.all m X) (hR : MbarRows P L X)
    {l : Loc} {y δ : Nat} {sel : Nat → Prop} (hδ : δ ≤ 1) (hinit : PairTmaRing.InitFirst X l 1)
    (hu : ∀ {g k : Nat} {e : Event}, X.get (g, k) = some e → Frame.MbarOf e l →
      (∃ c, e.kind = .mbInit l c) ∨
        (∃ q, MbarRow.Wait e l q ∧ (sel g → q % 2 = (okPolls l ((X.tr g).take k) + δ) % 2)) ∨
        g = y ∧ MbarRow.Commit e l) :
    Notify.Obj X l y l δ sel := by
  have ho := hX.tma.2.2.1
  refine ⟨?_, hinit, AsyncCopy.objects_noInval ho (no_inval hX hR) _, ?_, hδ⟩
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
      rcases hu he hm with ⟨_, hk⟩ | ⟨_, ⟨ok, hk⟩, -⟩ | ⟨-, _, hk, -⟩ <;> cases hk
    | @arrive h j pc tx cnt rel sc hid he ha =>
      rcases hu he rfl with ⟨_, hk⟩ | ⟨_, ⟨ok, hk⟩, -⟩ | ⟨-, _, hk, -⟩ <;> cases hk
    | @commit i pc sp rank hid he ht ha =>
      obtain ⟨h, j⟩ := i
      rcases hu he ⟨rank, ht⟩ with ⟨_, hk⟩ | ⟨_, ⟨ok, hk⟩, -⟩ | ⟨rfl, s, hk, hs, -⟩
      · cases hk
      · cases hk
      · simp only [Kind.tc.injEq, TcKind.commit.injEq] at hk
        subst hk
        exact .commit hid he hs ht ha
  · intro g k pc p acq sc hs he
    rcases hu he rfl with ⟨_, hk⟩ | ⟨q, ⟨ok, hk⟩, hq⟩ | ⟨-, _, hk, -⟩
    · cases hk
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -⟩ := hk
      exact hq hs
    · cases hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
