-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ReferencePrefix

@[expose] public section

/-! # The paired softmax warps carry the same reference across actual sparse blocks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The two corresponding lanes see the same canonical block maximum before their votes. -/
def PairedBlockMax (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g i j : Nat} {d q : D},
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) →
    Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)) →
    d.site = .rescaleVote → q.site = .rescaleVote → q.block = d.block →
    ∃ m : WithBot ℝ, d.blockMax = peakVal m ∧ q.blockMax = peakVal m

/-- Paired lanes use the same reference before a vote in the same block. The block maximum
is the only input required for agreement through the entire preceding vote history. -/
theorem reference_at_vote {g i j : Nat} {d q : D} {e f : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hMax : PairedBlockMax P L X)
    (he : X.get (g, i) = some e) (hf : X.get (Wg0PeerSources.partner L g, j) = some f)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)))
    (hD : d.site = .rescaleVote) (hQ : q.site = .rescaleVote) (hBlock : q.block = d.block) :
    reference d = reference q := by
  have hv := Wg0ReferencePrefix.before_vote hX hs ht he hd hD
  have hw := Wg0ReferencePrefix.before_vote hX hs ht hf hq hQ
  rcases hv with ⟨hZero, hInit⟩ |
    ⟨i', v, tag, take, vNext, _, hi', hv, hvSite, hvBlock, hvNext, hvRef⟩
  · rcases hw with ⟨_, hInit'⟩ | ⟨_, _, _, _, _, _, _, _, _, hb, _, _⟩
    · exact hInit.trans hInit'.symm
    · omega
  · rcases hw with ⟨hZero, _⟩ |
      ⟨j', w, tag', take', wNext, _, hj', hw, hwSite, hwBlock, hwNext, hwRef⟩
    · omega
    have htBlock : w.block = v.block := by omega
    have hOldRef := reference_at_vote hpre hX hs ht hMax hi' hj' hv hw hvSite hwSite htBlock
    have hVoteResult : take = take' := by
      apply paired_vote_result hpre hX hs ht hi' hj' hv hw hvSite hwSite htBlock
      intro l j0 j1 v0 w0 e0 f0 hl he0 hf0 hv0 hw0 hV hW hVBlock hWBlock
      have hB : w0.block = v0.block := hWBlock.trans hVBlock.symm
      obtain ⟨m, hM, hM'⟩ := hMax hv0 hw0 hV hW hB
      exact ⟨m, hM, hM', reference_at_vote hpre hX hs ht hMax he0 hf0 hv0 hw0 hV hW hB⟩
    obtain ⟨m, hM, hM'⟩ := hMax hv hw hvSite hwSite htBlock
    rw [← hVoteResult] at hwNext
    have hRef := equal_reference_after_vote hM hM' hOldRef hvNext hwNext
    exact hvRef.trans (hRef.trans hwRef.symm)
termination_by d.block
decreasing_by all_goals omega

/-- Paired lanes in the same block agree on the collective result and computed reference. -/
theorem reference_after_vote {g i j tag mateTag : Nat} {d q mid mid' : D}
    {p p' take take' : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hMax : PairedBlockMax P L X)
    (he : X.get (g, i) = some ⟨tag, .voteMode .any (2 ^ 32 - 1) p take⟩)
    (hf : X.get (Wg0PeerSources.partner L g, j) =
      some ⟨mateTag, .voteMode .any (2 ^ 32 - 1) p' take'⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hq : Frame.stateAt (Machine.code P L) X (Wg0PeerSources.partner L g) j = some (some (.wg0 q)))
    (hD : d.site = .rescaleVote) (hQ : q.site = .rescaleVote) (hBlock : q.block = d.block)
    (hUpdate : afterReferenceVote d take = some mid)
    (hUpdate' : afterReferenceVote q take' = some mid') :
    take = take' ∧ reference mid = reference mid' := by
  have hRef := reference_at_vote hpre hX hs ht hMax he hf hd hq hD hQ hBlock
  have hTake : take = take' := by
    apply paired_vote_result hpre hX hs ht he hf hd hq hD hQ hBlock
    intro l j0 j1 v w e0 f0 hl he0 hf0 hV hW hv hw hvBlock hwBlock
    have hb := hwBlock.trans hvBlock.symm
    obtain ⟨m, hM, hM'⟩ := hMax hV hW hv hw hb
    exact ⟨m, hM, hM', reference_at_vote hpre hX hs ht hMax he0 hf0 hV hW hv hw hb⟩
  obtain ⟨m, hm, hm'⟩ := hMax hd hq hD hQ hBlock
  rw [← hTake] at hUpdate'
  exact ⟨hTake, equal_reference_after_vote hm hm' hRef hUpdate hUpdate'⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PairedReference
