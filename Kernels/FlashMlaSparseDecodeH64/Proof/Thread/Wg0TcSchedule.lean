-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcVotes
import Lemmas.Step.WarpLanes

@[expose] public section

/-! # The observed per-block schedule of each softmax warp -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcSchedule

open PTX PTX.Flow Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A warp chooses rescale by its actual block vote, if one has fired. -/
def voteOf (L : Launch) (X : Execution) (g block : Nat) : Bool :=
  decide (∃ h i tag test, SameWarp L g h ∧
    X.get (h, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) test true⟩ ∧
    X.MaskK voteClass (h, i) (2 ^ 32 - 1) block)

/-- Each lane of a warp has the same schedule for all blocks. -/
theorem same_warp {g h : Nat} (hw : SameWarp L g h) :
    voteOf L X g = voteOf L X h := by
  funext block
  unfold voteOf
  congr 1
  apply propext
  constructor
  · rintro ⟨q, i, tag, p, hq, he, hk⟩
    exact ⟨q, i, tag, p, Step.sameWarp_trans (sameWarp_symm hw) hq, he, hk⟩
  · rintro ⟨q, i, tag, p, hq, he, hk⟩
    exact ⟨q, i, tag, p, Step.sameWarp_trans hw hq, he, hk⟩

/-- The actual reference vote supplies the schedule at the block of its typed state. -/
theorem at_vote (hX : Consistent L kernel Assumptions.all mem0 X)
    {g i tag : Nat} {d : Wg0.D} {p r : Bool}
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) p r⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) : r = voteOf L X g d.block := by
  have hg := Frame.lt_of_get hX he
  have hv : X.MaskK voteClass (g, i) (2 ^ 32 - 1) d.block := by
    refine ⟨⟨_, _, he, rfl, rfl⟩, ?_⟩
    change ((X.tr g).take i).countP Wg0VoteCount.countsVote = d.block
    have hc := Wg0VoteCount.count_at_wg0 hX hs he hd
    simpa [Wg0VoteCount.ordinal, hsite, Wg0VoteCount.afterVote] using hc
  symm
  cases r with
  | false =>
    apply decide_eq_false
    rintro ⟨h, j, tag', test, hw, hf, hk⟩
    cases Wg0TcVotes.same_result hX hw he hf hv hk
  | true =>
    apply decide_eq_true
    exact ⟨g, i, tag, p, ⟨⟨hg, hg, rfl⟩, rfl⟩, he, hv⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcSchedule
