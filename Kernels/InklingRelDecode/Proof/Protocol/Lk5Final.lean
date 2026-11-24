-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5Glue
public import Kernels.InklingRelDecode.Proof.Protocol.Lk5MRead
public import Kernels.InklingRelDecode.Proof.Interface.Lk5PeerSv
public import Kernels.InklingRelDecode.Proof.Interface.Lk5BAlign

@[expose] public section

/-!
# The softmax value chain, assembled

The induction on the loop iteration (`Lk5Glue.lean`) with its four parts:

* the decision of an iteration from its scratch words (`decAgree_of_it`, `Lk5VChain.lean`);
* the barrier-0 positions at `bar23` from the decisions of the earlier iterations
  (`B0N.b0At_of`, `B0N.b0Pos_of`);
* the stores of an iteration (`hW`);
* the loads of an iteration from the three (`scratchIt_of`, `Lk5MRead.lean`).

From the scratch words of every iteration: the softmax rows of the agreement
(`laneAgreeSm_of_it`) and `Bar.AlphaAgree`; `Sv.ExchPrem` (`exchPrem_full`) by the pair induction
on the iteration.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The scratch words of every iteration.** -/
theorem scratchIt_every (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hW : ∀ c i, StoreWord Q L X c i)
    (hB : ∀ c i, (∀ j < i, DecAgree Q L X c j) → B0At Q L X c i)
    (hP : ∀ c i, (∀ j < i, DecAgree Q L X c j) → B0Pos Q L X c i) :
    ∀ i, ScratchIt Q L X i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hD : ∀ c, ∀ j < i, DecAgree Q L X c j := fun c j hj =>
      decAgree_of_it hpre hX hf (ih j hj) c
    exact scratchIt_of hpre hX hf hR (fun c => hW c i) (fun c => hB c i (hD c))
      (fun c j hj => hP c j (fun j' hj' => hD c j' (by omega)))

/-- **The decisions of every iteration agree in each CTA.** -/
theorem decAgree_every (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (h : ∀ i, ScratchIt Q L X i) : ∀ c j, DecAgree Q L X c j :=
  fun c j => decAgree_of_it hpre hX hf (h j) c

/-- **`Sv.ExchPrem`** from the scratch words of every iteration. -/
theorem exchPrem_of_it (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hM : SmMaxOk Q L X) (hz : Rs.SmBaseZero Q L X)
    (hS : ScorePrem Q L X) : Sv.ExchPrem Q L X :=
  exchPrem_full hpre hX hf hM hz hS

/-- **The scratch words of every iteration**, from the stores of every iteration. -/
theorem scratchIt_of_store (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hW : ∀ c i, StoreWord Q L X c i) :
    ∀ i, ScratchIt Q L X i :=
  scratchIt_every hpre hX hf hR hW (fun _ _ hD => B0N.b0At_of hpre hX hf hD)
    (fun _ _ hD => B0N.b0Pos_of hpre hX hf hD)

/-- **`Bar.AlphaAgree`** from the scratch words of every iteration. -/
theorem alphaAgree_of_it (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (h : ∀ i, ScratchIt Q L X i) : Bar.AlphaAgree L X :=
  B0N.alphaAgree_of hpre hX hf (decAgree_every hpre hX hf h)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
