-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpVote
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # Two warps whose lanes vote alike receive the same mode vote

The `n`-th full-mask mode votes of two lanes `g`, `h` (of two warps) are two instances
(DEP-WARP-VOTE). When lane `l` of both warps has its `n`-th vote with the same input, the two
instances have the same participants' inputs, and the lanes receive the same reduction. -/

namespace PTX.Step
open PTX PTX.Flow

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Two lanes of two warps receive the same result from their `n`-th mode votes with mask `m`**,
when every lane of the mask has its `n`-th vote in both warps with equal inputs. -/
theorem voteMode_pair (hX : Consistent L K A mem0 X) {g h i j n m : Nat} {q : VoteMode}
    {pc pc' : Nat} {a a' r r' : Bool} (hm : ∀ l < 32, m.testBit l = true)
    (he : X.get (g, i) = some ⟨pc, .voteMode q m a r⟩)
    (he' : X.get (h, j) = some ⟨pc', .voteMode q m a' r'⟩)
    (hk : X.MaskK voteClass (g, i) m n) (hk' : X.MaskK voteClass (h, j) m n)
    (hlane : ∀ l < 32, ∃ v : Bool,
      (∃ i' pc1 r1, X.get (g - laneOf L g + l, i') = some ⟨pc1, .voteMode q m v r1⟩ ∧
        X.MaskK voteClass (g - laneOf L g + l, i') m n) ∧
      (∃ j' pc2 r2, X.get (h - laneOf L h + l, j') = some ⟨pc2, .voteMode q m v r2⟩ ∧
        X.MaskK voteClass (h - laneOf L h + l, j') m n)) : r = r' := by
  classical
  let part : Nat → Option Bool := fun l =>
    if hl : l < 32 then some (Classical.choose (hlane l hl)) else none
  have hMI : MaskInstance L voteClass X g m n q part := by
    intro l hl
    obtain ⟨⟨i', pc1, r1, hget, hmk⟩, -⟩ := Classical.choose_spec (hlane l hl)
    refine ⟨fun _ => Or.inl ⟨i', pc1, .voteMode q m _ r1, _, hget, rfl, hmk, ?_⟩,
      fun hbit => by rw [hm l hl] at hbit; cases hbit⟩
    simp [part, hl]
  have hMI' : MaskInstance L voteClass X h m n q part := by
    intro l hl
    obtain ⟨-, ⟨j', pc2, r2, hget, hmk⟩⟩ := Classical.choose_spec (hlane l hl)
    refine ⟨fun _ => Or.inl ⟨j', pc2, .voteMode q m _ r2, _, hget, rfl, hmk, ?_⟩,
      fun hbit => by rw [hm l hl] at hbit; cases hbit⟩
    simp [part, hl]
  rw [hX.warpValue.1 g i pc q m a r n he hk part hMI,
    hX.warpValue.1 h j pc' q m a' r' n he' hk' part hMI']

end PTX.Step
